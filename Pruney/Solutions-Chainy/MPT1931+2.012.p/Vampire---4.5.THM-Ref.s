%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:39 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 134 expanded)
%              Number of leaves         :   14 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  232 ( 536 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f84,f93,f110,f131,f158,f175,f196])).

fof(f196,plain,
    ( ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f145,f109,f145,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f109,plain,
    ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_10
  <=> ! [X2] : ~ m1_subset_1(X2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f145,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl6_11
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f175,plain,
    ( ~ spl6_10
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl6_10
    | spl6_11 ),
    inference(unit_resulting_resolution,[],[f146,f160,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK5(X0),X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f160,plain,
    ( ! [X0] : ~ r2_hidden(X0,u1_struct_0(sK1))
    | ~ spl6_10
    | spl6_11 ),
    inference(unit_resulting_resolution,[],[f109,f146,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f146,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f144])).

fof(f158,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f16,f89])).

fof(f89,plain,
    ( v2_struct_0(sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl6_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f16,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f131,plain,(
    spl6_9 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f111,f118,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_subset_1(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f35,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f118,plain,
    ( r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_struct_0(sK0))
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f111,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_subset_1(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f34,f30])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f111,plain,
    ( r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f106,f41])).

fof(f106,plain,
    ( ~ v1_xboole_0(k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_9
  <=> v1_xboole_0(k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f110,plain,
    ( ~ spl6_9
    | spl6_10
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f102,f91,f108,f104])).

fof(f91,plain,
    ( spl6_7
  <=> ! [X1,X0] :
        ( ~ r2_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,X1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f102,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ v1_xboole_0(k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) )
    | ~ spl6_7 ),
    inference(resolution,[],[f94,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f94,plain,
    ( ! [X0] :
        ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),X0)),k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl6_7 ),
    inference(resolution,[],[f92,f57])).

fof(f57,plain,(
    r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f22,f21,f16,f19,f20,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_0)).

fof(f20,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ r2_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,X1)),X0) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,
    ( spl6_6
    | spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f85,f82,f91,f87])).

fof(f82,plain,
    ( spl6_5
  <=> ! [X7,X8,X6] :
        ( v2_struct_0(X6)
        | ~ r2_waybel_0(sK0,X6,X8)
        | r2_hidden(k2_waybel_0(sK0,X6,sK3(sK0,X6,X8,X7)),X8)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ l1_waybel_0(X6,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( ~ r2_waybel_0(sK0,sK1,X0)
        | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(sK1) )
    | ~ spl6_5 ),
    inference(resolution,[],[f83,f19])).

fof(f83,plain,
    ( ! [X6,X8,X7] :
        ( ~ l1_waybel_0(X6,sK0)
        | ~ r2_waybel_0(sK0,X6,X8)
        | r2_hidden(k2_waybel_0(sK0,X6,sK3(sK0,X6,X8,X7)),X8)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,
    ( spl6_5
    | spl6_2 ),
    inference(avatar_split_clause,[],[f54,f63,f82])).

fof(f63,plain,
    ( spl6_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f54,plain,(
    ! [X6,X8,X7] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X6)
      | ~ l1_waybel_0(X6,sK0)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | r2_hidden(k2_waybel_0(sK0,X6,sK3(sK0,X6,X8,X7)),X8)
      | ~ r2_waybel_0(sK0,X6,X8) ) ),
    inference(resolution,[],[f22,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

fof(f70,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f21,f65])).

fof(f65,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:24:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.52  % (30737)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.52  % (30717)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.52  % (30721)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.52  % (30737)Refutation not found, incomplete strategy% (30737)------------------------------
% 0.23/0.52  % (30737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (30729)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.53  % (30718)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.26/0.54  % (30737)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (30713)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.54  % (30737)Memory used [KB]: 6268
% 1.26/0.54  % (30737)Time elapsed: 0.109 s
% 1.26/0.54  % (30737)------------------------------
% 1.26/0.54  % (30737)------------------------------
% 1.26/0.54  % (30729)Refutation not found, incomplete strategy% (30729)------------------------------
% 1.26/0.54  % (30729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (30729)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (30729)Memory used [KB]: 10618
% 1.26/0.54  % (30729)Time elapsed: 0.124 s
% 1.26/0.54  % (30729)------------------------------
% 1.26/0.54  % (30729)------------------------------
% 1.26/0.54  % (30715)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.26/0.54  % (30719)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.26/0.54  % (30712)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.26/0.54  % (30740)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.26/0.54  % (30727)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.26/0.55  % (30716)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.41/0.55  % (30739)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.55  % (30716)Refutation found. Thanks to Tanya!
% 1.41/0.55  % SZS status Theorem for theBenchmark
% 1.41/0.55  % SZS output start Proof for theBenchmark
% 1.41/0.55  fof(f197,plain,(
% 1.41/0.55    $false),
% 1.41/0.55    inference(avatar_sat_refutation,[],[f70,f84,f93,f110,f131,f158,f175,f196])).
% 1.41/0.55  fof(f196,plain,(
% 1.41/0.55    ~spl6_10 | ~spl6_11),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f190])).
% 1.41/0.55  fof(f190,plain,(
% 1.41/0.55    $false | (~spl6_10 | ~spl6_11)),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f145,f109,f145,f37])).
% 1.41/0.55  fof(f37,plain,(
% 1.41/0.55    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f15])).
% 1.41/0.55  fof(f15,plain,(
% 1.41/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f3])).
% 1.41/0.55  fof(f3,axiom,(
% 1.41/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.41/0.55  fof(f109,plain,(
% 1.41/0.55    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK1))) ) | ~spl6_10),
% 1.41/0.55    inference(avatar_component_clause,[],[f108])).
% 1.41/0.55  fof(f108,plain,(
% 1.41/0.55    spl6_10 <=> ! [X2] : ~m1_subset_1(X2,u1_struct_0(sK1))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.41/0.55  fof(f145,plain,(
% 1.41/0.55    v1_xboole_0(u1_struct_0(sK1)) | ~spl6_11),
% 1.41/0.55    inference(avatar_component_clause,[],[f144])).
% 1.41/0.55  fof(f144,plain,(
% 1.41/0.55    spl6_11 <=> v1_xboole_0(u1_struct_0(sK1))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.41/0.55  fof(f175,plain,(
% 1.41/0.55    ~spl6_10 | spl6_11),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f173])).
% 1.41/0.55  fof(f173,plain,(
% 1.41/0.55    $false | (~spl6_10 | spl6_11)),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f146,f160,f41])).
% 1.41/0.55  fof(f41,plain,(
% 1.41/0.55    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f1])).
% 1.41/0.55  fof(f1,axiom,(
% 1.41/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.41/0.55  fof(f160,plain,(
% 1.41/0.55    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1))) ) | (~spl6_10 | spl6_11)),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f109,f146,f39])).
% 1.41/0.55  fof(f39,plain,(
% 1.41/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f15])).
% 1.41/0.55  fof(f146,plain,(
% 1.41/0.55    ~v1_xboole_0(u1_struct_0(sK1)) | spl6_11),
% 1.41/0.55    inference(avatar_component_clause,[],[f144])).
% 1.41/0.55  fof(f158,plain,(
% 1.41/0.55    ~spl6_6),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f155])).
% 1.41/0.55  fof(f155,plain,(
% 1.41/0.55    $false | ~spl6_6),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f16,f89])).
% 1.41/0.55  fof(f89,plain,(
% 1.41/0.55    v2_struct_0(sK1) | ~spl6_6),
% 1.41/0.55    inference(avatar_component_clause,[],[f87])).
% 1.41/0.55  fof(f87,plain,(
% 1.41/0.55    spl6_6 <=> v2_struct_0(sK1)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.41/0.55  fof(f16,plain,(
% 1.41/0.55    ~v2_struct_0(sK1)),
% 1.41/0.55    inference(cnf_transformation,[],[f10])).
% 1.41/0.55  fof(f10,plain,(
% 1.41/0.55    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.41/0.55    inference(flattening,[],[f9])).
% 1.41/0.55  fof(f9,plain,(
% 1.41/0.55    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f8])).
% 1.41/0.55  fof(f8,negated_conjecture,(
% 1.41/0.55    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.41/0.55    inference(negated_conjecture,[],[f7])).
% 1.41/0.55  fof(f7,conjecture,(
% 1.41/0.55    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).
% 1.41/0.55  fof(f131,plain,(
% 1.41/0.55    spl6_9),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f129])).
% 1.41/0.55  fof(f129,plain,(
% 1.41/0.55    $false | spl6_9),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f111,f118,f50])).
% 1.41/0.55  fof(f50,plain,(
% 1.41/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_subset_1(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.41/0.55    inference(equality_resolution,[],[f44])).
% 1.41/0.55  fof(f44,plain,(
% 1.41/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k6_subset_1(X0,X1) != X2) )),
% 1.41/0.55    inference(definition_unfolding,[],[f35,f30])).
% 1.41/0.55  fof(f30,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f4])).
% 1.41/0.55  fof(f4,axiom,(
% 1.41/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.41/0.55  fof(f35,plain,(
% 1.41/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.41/0.55    inference(cnf_transformation,[],[f2])).
% 1.41/0.55  fof(f2,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.41/0.55  fof(f118,plain,(
% 1.41/0.55    r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_struct_0(sK0)) | spl6_9),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f111,f51])).
% 1.41/0.55  fof(f51,plain,(
% 1.41/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_subset_1(X0,X1)) | r2_hidden(X3,X0)) )),
% 1.41/0.55    inference(equality_resolution,[],[f45])).
% 1.41/0.55  fof(f45,plain,(
% 1.41/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k6_subset_1(X0,X1) != X2) )),
% 1.41/0.55    inference(definition_unfolding,[],[f34,f30])).
% 1.41/0.55  fof(f34,plain,(
% 1.41/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.41/0.55    inference(cnf_transformation,[],[f2])).
% 1.41/0.55  fof(f111,plain,(
% 1.41/0.55    r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) | spl6_9),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f106,f41])).
% 1.41/0.55  fof(f106,plain,(
% 1.41/0.55    ~v1_xboole_0(k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) | spl6_9),
% 1.41/0.55    inference(avatar_component_clause,[],[f104])).
% 1.41/0.55  fof(f104,plain,(
% 1.41/0.55    spl6_9 <=> v1_xboole_0(k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.41/0.55  fof(f110,plain,(
% 1.41/0.55    ~spl6_9 | spl6_10 | ~spl6_7),
% 1.41/0.55    inference(avatar_split_clause,[],[f102,f91,f108,f104])).
% 1.41/0.55  fof(f91,plain,(
% 1.41/0.55    spl6_7 <=> ! [X1,X0] : (~r2_waybel_0(sK0,sK1,X0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,X1)),X0))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.41/0.55  fof(f102,plain,(
% 1.41/0.55    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK1)) | ~v1_xboole_0(k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ) | ~spl6_7),
% 1.41/0.55    inference(resolution,[],[f94,f42])).
% 1.41/0.55  fof(f42,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f1])).
% 1.41/0.55  fof(f94,plain,(
% 1.41/0.55    ( ! [X0] : (r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),X0)),k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl6_7),
% 1.41/0.55    inference(resolution,[],[f92,f57])).
% 1.41/0.55  fof(f57,plain,(
% 1.41/0.55    r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f22,f21,f16,f19,f20,f23])).
% 1.41/0.55  fof(f23,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | r1_waybel_0(X0,X1,X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f12])).
% 1.41/0.55  fof(f12,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.41/0.55    inference(flattening,[],[f11])).
% 1.41/0.55  fof(f11,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f6])).
% 1.41/0.55  fof(f6,axiom,(
% 1.41/0.55    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_0)).
% 1.41/0.55  fof(f20,plain,(
% 1.41/0.55    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 1.41/0.55    inference(cnf_transformation,[],[f10])).
% 1.41/0.55  fof(f19,plain,(
% 1.41/0.55    l1_waybel_0(sK1,sK0)),
% 1.41/0.55    inference(cnf_transformation,[],[f10])).
% 1.41/0.55  fof(f21,plain,(
% 1.41/0.55    ~v2_struct_0(sK0)),
% 1.41/0.55    inference(cnf_transformation,[],[f10])).
% 1.41/0.55  fof(f22,plain,(
% 1.41/0.55    l1_struct_0(sK0)),
% 1.41/0.55    inference(cnf_transformation,[],[f10])).
% 1.41/0.55  fof(f92,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r2_waybel_0(sK0,sK1,X0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,X1)),X0)) ) | ~spl6_7),
% 1.41/0.55    inference(avatar_component_clause,[],[f91])).
% 1.41/0.55  fof(f93,plain,(
% 1.41/0.55    spl6_6 | spl6_7 | ~spl6_5),
% 1.41/0.55    inference(avatar_split_clause,[],[f85,f82,f91,f87])).
% 1.41/0.55  fof(f82,plain,(
% 1.41/0.55    spl6_5 <=> ! [X7,X8,X6] : (v2_struct_0(X6) | ~r2_waybel_0(sK0,X6,X8) | r2_hidden(k2_waybel_0(sK0,X6,sK3(sK0,X6,X8,X7)),X8) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_waybel_0(X6,sK0))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.41/0.55  fof(f85,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r2_waybel_0(sK0,sK1,X0) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,X1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | v2_struct_0(sK1)) ) | ~spl6_5),
% 1.41/0.55    inference(resolution,[],[f83,f19])).
% 1.41/0.55  fof(f83,plain,(
% 1.41/0.55    ( ! [X6,X8,X7] : (~l1_waybel_0(X6,sK0) | ~r2_waybel_0(sK0,X6,X8) | r2_hidden(k2_waybel_0(sK0,X6,sK3(sK0,X6,X8,X7)),X8) | ~m1_subset_1(X7,u1_struct_0(X6)) | v2_struct_0(X6)) ) | ~spl6_5),
% 1.41/0.55    inference(avatar_component_clause,[],[f82])).
% 1.41/0.55  fof(f84,plain,(
% 1.41/0.55    spl6_5 | spl6_2),
% 1.41/0.55    inference(avatar_split_clause,[],[f54,f63,f82])).
% 1.41/0.55  fof(f63,plain,(
% 1.41/0.55    spl6_2 <=> v2_struct_0(sK0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.41/0.55  fof(f54,plain,(
% 1.41/0.55    ( ! [X6,X8,X7] : (v2_struct_0(sK0) | v2_struct_0(X6) | ~l1_waybel_0(X6,sK0) | ~m1_subset_1(X7,u1_struct_0(X6)) | r2_hidden(k2_waybel_0(sK0,X6,sK3(sK0,X6,X8,X7)),X8) | ~r2_waybel_0(sK0,X6,X8)) )),
% 1.41/0.55    inference(resolution,[],[f22,f28])).
% 1.41/0.55  fof(f28,plain,(
% 1.41/0.55    ( ! [X2,X0,X3,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2) | ~r2_waybel_0(X0,X1,X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f14])).
% 1.41/0.55  fof(f14,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.41/0.55    inference(flattening,[],[f13])).
% 1.41/0.55  fof(f13,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f5])).
% 1.41/0.55  fof(f5,axiom,(
% 1.41/0.55    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).
% 1.41/0.55  fof(f70,plain,(
% 1.41/0.55    ~spl6_2),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f67])).
% 1.41/0.55  fof(f67,plain,(
% 1.41/0.55    $false | ~spl6_2),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f21,f65])).
% 1.41/0.55  fof(f65,plain,(
% 1.41/0.55    v2_struct_0(sK0) | ~spl6_2),
% 1.41/0.55    inference(avatar_component_clause,[],[f63])).
% 1.41/0.55  % SZS output end Proof for theBenchmark
% 1.41/0.55  % (30716)------------------------------
% 1.41/0.55  % (30716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (30716)Termination reason: Refutation
% 1.41/0.55  
% 1.41/0.55  % (30716)Memory used [KB]: 6268
% 1.41/0.55  % (30716)Time elapsed: 0.138 s
% 1.41/0.55  % (30716)------------------------------
% 1.41/0.55  % (30716)------------------------------
% 1.41/0.55  % (30741)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.55  % (30711)Success in time 0.18 s
%------------------------------------------------------------------------------
