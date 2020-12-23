%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 234 expanded)
%              Number of leaves         :   25 ( 101 expanded)
%              Depth                    :   10
%              Number of atoms          :  392 ( 672 expanded)
%              Number of equality atoms :   17 (  70 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f76,f81,f90,f91,f101,f106,f113,f118,f130,f144,f146,f159,f161,f163,f164,f167,f171])).

fof(f171,plain,
    ( spl5_13
    | spl5_11
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_7
    | ~ spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f170,f83,f98,f103,f156,f141,f137,f152])).

fof(f152,plain,
    ( spl5_13
  <=> v2_struct_0(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f137,plain,
    ( spl5_11
  <=> r1_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f141,plain,
    ( spl5_12
  <=> l1_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f156,plain,
    ( spl5_14
  <=> v3_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f103,plain,
    ( spl5_7
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f98,plain,
    ( spl5_6
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f83,plain,
    ( spl5_4
  <=> r3_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f170,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f169,f36])).

fof(f36,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f169,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f168,f36])).

fof(f168,plain,
    ( ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f84,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f84,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f167,plain,
    ( ~ spl5_12
    | spl5_10
    | ~ spl5_7
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f166,f137,f98,f103,f127,f141])).

fof(f127,plain,
    ( spl5_10
  <=> r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f166,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f165,f36])).

fof(f165,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f148,f36])).

fof(f148,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ spl5_11 ),
    inference(resolution,[],[f139,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f139,plain,
    ( r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f164,plain,
    ( ~ spl5_9
    | spl5_5
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f131,f127,f110,f87,f115])).

fof(f115,plain,
    ( spl5_9
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f87,plain,
    ( spl5_5
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f110,plain,
    ( spl5_8
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f131,plain,
    ( ~ r2_hidden(sK2,sK0)
    | r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK1,sK0)
    | ~ spl5_10 ),
    inference(resolution,[],[f129,f93])).

fof(f93,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X0)))
      | ~ r2_hidden(X3,X0)
      | r1_tarski(X2,X3)
      | ~ r2_hidden(X2,X0) ) ),
    inference(global_subsumption,[],[f52,f65])).

fof(f65,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(u1_orders_2(k2_yellow_1(X0)))
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | r1_tarski(X2,X3)
      | ~ r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X0))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | r1_tarski(X2,X3)
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | u1_orders_2(k2_yellow_1(X0)) != X1 ) ),
    inference(definition_unfolding,[],[f42,f51])).

fof(f51,plain,(
    ! [X0] : k1_wellord2(X0) = u1_orders_2(k2_yellow_1(X0)) ),
    inference(definition_unfolding,[],[f33,f37])).

fof(f37,plain,(
    ! [X0] : k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] : k1_wellord2(X0) = k1_yellow_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_wellord2(X0) = k1_yellow_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_yellow_1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | r1_tarski(X2,X3)
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f52,plain,(
    ! [X0] : v1_relat_1(u1_orders_2(k2_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f32,f51])).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f129,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f163,plain,
    ( spl5_1
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f162,f152,f68])).

fof(f68,plain,
    ( spl5_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f162,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_13 ),
    inference(resolution,[],[f154,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f154,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f152])).

fof(f161,plain,(
    spl5_14 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl5_14 ),
    inference(resolution,[],[f158,f34])).

fof(f34,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f158,plain,
    ( ~ v3_orders_2(k2_yellow_1(sK0))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f159,plain,
    ( spl5_4
    | spl5_13
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_7
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f150,f137,f98,f103,f156,f141,f152,f83])).

fof(f150,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0))
    | r3_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f149,f36])).

fof(f149,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | v2_struct_0(k2_yellow_1(sK0))
    | r3_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f147,f36])).

fof(f147,plain,
    ( ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | v2_struct_0(k2_yellow_1(sK0))
    | r3_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | ~ spl5_11 ),
    inference(resolution,[],[f139,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f146,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl5_12 ),
    inference(resolution,[],[f143,f35])).

fof(f35,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f143,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f144,plain,
    ( spl5_11
    | ~ spl5_12
    | ~ spl5_7
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f135,f127,f98,f103,f141,f137])).

fof(f135,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f134,f36])).

fof(f134,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f132,f36])).

fof(f132,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | ~ spl5_10 ),
    inference(resolution,[],[f129,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f130,plain,
    ( spl5_10
    | ~ spl5_8
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f125,f115,f87,f110,f127])).

fof(f125,plain,
    ( ~ r2_hidden(sK2,sK0)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(resolution,[],[f124,f88])).

fof(f88,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f124,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK1,X1)
        | ~ r2_hidden(X1,sK0)
        | r2_hidden(k4_tarski(sK1,X1),u1_orders_2(k2_yellow_1(sK0))) )
    | ~ spl5_9 ),
    inference(resolution,[],[f94,f117])).

fof(f117,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f94,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X0))) ) ),
    inference(global_subsumption,[],[f52,f66])).

fof(f66,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(u1_orders_2(k2_yellow_1(X0)))
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X0))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | u1_orders_2(k2_yellow_1(X0)) != X1 ) ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f118,plain,
    ( spl5_9
    | spl5_1
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f108,f103,f68,f115])).

fof(f108,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK1,sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f48,f105])).

fof(f105,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f113,plain,
    ( spl5_8
    | spl5_1
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f107,f98,f68,f110])).

fof(f107,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK2,sK0)
    | ~ spl5_6 ),
    inference(resolution,[],[f48,f100])).

fof(f100,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f106,plain,
    ( spl5_7
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f96,f73,f103])).

fof(f73,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f96,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f75,f36])).

fof(f75,plain,
    ( m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f101,plain,
    ( spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f95,f78,f98])).

fof(f78,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f95,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f80,f36])).

fof(f80,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f91,plain,
    ( spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f27,f87,f83])).

fof(f27,plain,
    ( r1_tarski(sK1,sK2)
    | r3_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <~> r1_tarski(X1,X2) )
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                <=> r1_tarski(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f90,plain,
    ( ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f28,f87,f83])).

fof(f28,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r3_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f29,f78])).

fof(f29,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f30,f73])).

fof(f30,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:03:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (5147)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (5162)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.50  % (5140)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (5147)Refutation not found, incomplete strategy% (5147)------------------------------
% 0.21/0.51  % (5147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5147)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5147)Memory used [KB]: 10618
% 0.21/0.51  % (5147)Time elapsed: 0.092 s
% 0.21/0.51  % (5147)------------------------------
% 0.21/0.51  % (5147)------------------------------
% 0.21/0.51  % (5138)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (5138)Refutation not found, incomplete strategy% (5138)------------------------------
% 0.21/0.51  % (5138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5138)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5138)Memory used [KB]: 10746
% 0.21/0.51  % (5138)Time elapsed: 0.093 s
% 0.21/0.51  % (5138)------------------------------
% 0.21/0.51  % (5138)------------------------------
% 0.21/0.51  % (5158)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (5154)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (5158)Refutation not found, incomplete strategy% (5158)------------------------------
% 0.21/0.51  % (5158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5158)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5158)Memory used [KB]: 10746
% 0.21/0.51  % (5158)Time elapsed: 0.073 s
% 0.21/0.51  % (5158)------------------------------
% 0.21/0.51  % (5158)------------------------------
% 0.21/0.51  % (5152)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (5143)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (5162)Refutation not found, incomplete strategy% (5162)------------------------------
% 0.21/0.52  % (5162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5162)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5162)Memory used [KB]: 10746
% 0.21/0.52  % (5162)Time elapsed: 0.104 s
% 0.21/0.52  % (5162)------------------------------
% 0.21/0.52  % (5162)------------------------------
% 0.21/0.52  % (5152)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f71,f76,f81,f90,f91,f101,f106,f113,f118,f130,f144,f146,f159,f161,f163,f164,f167,f171])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    spl5_13 | spl5_11 | ~spl5_12 | ~spl5_14 | ~spl5_7 | ~spl5_6 | ~spl5_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f170,f83,f98,f103,f156,f141,f137,f152])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    spl5_13 <=> v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    spl5_11 <=> r1_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    spl5_12 <=> l1_orders_2(k2_yellow_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    spl5_14 <=> v3_orders_2(k2_yellow_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    spl5_7 <=> m1_subset_1(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    spl5_6 <=> m1_subset_1(sK2,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    spl5_4 <=> r3_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0) | ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | v2_struct_0(k2_yellow_1(sK0)) | ~spl5_4),
% 0.21/0.52    inference(forward_demodulation,[],[f169,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : (k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0)) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,sK0) | ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | v2_struct_0(k2_yellow_1(sK0)) | ~spl5_4),
% 0.21/0.52    inference(forward_demodulation,[],[f168,f36])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | v2_struct_0(k2_yellow_1(sK0)) | ~spl5_4),
% 0.21/0.52    inference(resolution,[],[f84,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    r3_orders_2(k2_yellow_1(sK0),sK1,sK2) | ~spl5_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f83])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    ~spl5_12 | spl5_10 | ~spl5_7 | ~spl5_6 | ~spl5_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f166,f137,f98,f103,f127,f141])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    spl5_10 <=> r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~spl5_11),
% 0.21/0.52    inference(forward_demodulation,[],[f165,f36])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~spl5_11),
% 0.21/0.52    inference(forward_demodulation,[],[f148,f36])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~spl5_11),
% 0.21/0.52    inference(resolution,[],[f139,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | ~spl5_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f137])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    ~spl5_9 | spl5_5 | ~spl5_8 | ~spl5_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f131,f127,f110,f87,f115])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    spl5_9 <=> r2_hidden(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    spl5_5 <=> r1_tarski(sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    spl5_8 <=> r2_hidden(sK2,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    ~r2_hidden(sK2,sK0) | r1_tarski(sK1,sK2) | ~r2_hidden(sK1,sK0) | ~spl5_10),
% 0.21/0.52    inference(resolution,[],[f129,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X0))) | ~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(X2,X0)) )),
% 0.21/0.52    inference(global_subsumption,[],[f52,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (~v1_relat_1(u1_orders_2(k2_yellow_1(X0))) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X0)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1) | u1_orders_2(k2_yellow_1(X0)) != X1) )),
% 0.21/0.52    inference(definition_unfolding,[],[f42,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0] : (k1_wellord2(X0) = u1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f33,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0] : (k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0] : (k1_wellord2(X0) = k1_yellow_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : k1_wellord2(X0) = k1_yellow_1(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_yellow_1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1) | k1_wellord2(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(u1_orders_2(k2_yellow_1(X0)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f32,f51])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | ~spl5_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f127])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    spl5_1 | ~spl5_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f162,f152,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl5_1 <=> v1_xboole_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    v1_xboole_0(sK0) | ~spl5_13),
% 0.21/0.52    inference(resolution,[],[f154,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    v2_struct_0(k2_yellow_1(sK0)) | ~spl5_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f152])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    spl5_14),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f160])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    $false | spl5_14),
% 0.21/0.52    inference(resolution,[],[f158,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : v3_orders_2(k2_yellow_1(X0))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ~v3_orders_2(k2_yellow_1(sK0)) | spl5_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f156])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    spl5_4 | spl5_13 | ~spl5_12 | ~spl5_14 | ~spl5_7 | ~spl5_6 | ~spl5_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f150,f137,f98,f103,f156,f141,f152,f83])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0) | ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0)) | r3_orders_2(k2_yellow_1(sK0),sK1,sK2) | ~spl5_11),
% 0.21/0.52    inference(forward_demodulation,[],[f149,f36])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,sK0) | ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0)) | r3_orders_2(k2_yellow_1(sK0),sK1,sK2) | ~spl5_11),
% 0.21/0.52    inference(forward_demodulation,[],[f147,f36])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0)) | r3_orders_2(k2_yellow_1(sK0),sK1,sK2) | ~spl5_11),
% 0.21/0.52    inference(resolution,[],[f139,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_orders_2(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    spl5_12),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f145])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    $false | spl5_12),
% 0.21/0.52    inference(resolution,[],[f143,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    ~l1_orders_2(k2_yellow_1(sK0)) | spl5_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f141])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    spl5_11 | ~spl5_12 | ~spl5_7 | ~spl5_6 | ~spl5_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f135,f127,f98,f103,f141,f137])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0) | ~l1_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | ~spl5_10),
% 0.21/0.52    inference(forward_demodulation,[],[f134,f36])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | ~spl5_10),
% 0.21/0.52    inference(forward_demodulation,[],[f132,f36])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | ~spl5_10),
% 0.21/0.52    inference(resolution,[],[f129,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    spl5_10 | ~spl5_8 | ~spl5_5 | ~spl5_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f125,f115,f87,f110,f127])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ~r2_hidden(sK2,sK0) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | (~spl5_5 | ~spl5_9)),
% 0.21/0.52    inference(resolution,[],[f124,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2) | ~spl5_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f87])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_tarski(sK1,X1) | ~r2_hidden(X1,sK0) | r2_hidden(k4_tarski(sK1,X1),u1_orders_2(k2_yellow_1(sK0)))) ) | ~spl5_9),
% 0.21/0.52    inference(resolution,[],[f94,f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    r2_hidden(sK1,sK0) | ~spl5_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f115])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X0)))) )),
% 0.21/0.52    inference(global_subsumption,[],[f52,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (~v1_relat_1(u1_orders_2(k2_yellow_1(X0))) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X0)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1) | u1_orders_2(k2_yellow_1(X0)) != X1) )),
% 0.21/0.52    inference(definition_unfolding,[],[f41,f51])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1) | k1_wellord2(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl5_9 | spl5_1 | ~spl5_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f108,f103,f68,f115])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    v1_xboole_0(sK0) | r2_hidden(sK1,sK0) | ~spl5_7),
% 0.21/0.52    inference(resolution,[],[f48,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    m1_subset_1(sK1,sK0) | ~spl5_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f103])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl5_8 | spl5_1 | ~spl5_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f107,f98,f68,f110])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    v1_xboole_0(sK0) | r2_hidden(sK2,sK0) | ~spl5_6),
% 0.21/0.52    inference(resolution,[],[f48,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    m1_subset_1(sK2,sK0) | ~spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f98])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl5_7 | ~spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f96,f73,f103])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl5_2 <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    m1_subset_1(sK1,sK0) | ~spl5_2),
% 0.21/0.52    inference(backward_demodulation,[],[f75,f36])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl5_6 | ~spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f95,f78,f98])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl5_3 <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    m1_subset_1(sK2,sK0) | ~spl5_3),
% 0.21/0.52    inference(backward_demodulation,[],[f80,f36])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f78])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    spl5_4 | spl5_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f27,f87,f83])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2) | r3_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f11])).
% 0.21/0.52  fof(f11,conjecture,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ~spl5_4 | ~spl5_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f28,f87,f83])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ~r1_tarski(sK1,sK2) | ~r3_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f29,f78])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f30,f73])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ~spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f31,f68])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ~v1_xboole_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (5152)------------------------------
% 0.21/0.52  % (5152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5152)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (5152)Memory used [KB]: 10746
% 0.21/0.52  % (5152)Time elapsed: 0.108 s
% 0.21/0.52  % (5152)------------------------------
% 0.21/0.52  % (5152)------------------------------
% 0.21/0.52  % (5145)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (5145)Refutation not found, incomplete strategy% (5145)------------------------------
% 0.21/0.52  % (5145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5145)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5145)Memory used [KB]: 10618
% 0.21/0.52  % (5145)Time elapsed: 0.119 s
% 0.21/0.52  % (5145)------------------------------
% 0.21/0.52  % (5145)------------------------------
% 0.21/0.52  % (5159)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (5163)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (5140)Refutation not found, incomplete strategy% (5140)------------------------------
% 0.21/0.53  % (5140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5140)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5140)Memory used [KB]: 6268
% 0.21/0.53  % (5140)Time elapsed: 0.102 s
% 0.21/0.53  % (5140)------------------------------
% 0.21/0.53  % (5140)------------------------------
% 0.21/0.53  % (5165)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (5141)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (5155)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (5150)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (5134)Success in time 0.174 s
%------------------------------------------------------------------------------
