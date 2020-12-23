%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 135 expanded)
%              Number of leaves         :   16 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  241 ( 774 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f66,f68,f70,f72,f74,f80,f82,f88])).

fof(f88,plain,(
    ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | ~ spl3_8 ),
    inference(resolution,[],[f84,f25])).

fof(f25,plain,(
    ~ r2_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK2)
    & r1_waybel_0(sK0,sK1,sK2)
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f15,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_waybel_0(X0,X1,X2)
                & r1_waybel_0(X0,X1,X2) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(sK0,X1,X2)
              & r1_waybel_0(sK0,X1,X2) )
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_waybel_0(sK0,X1,X2)
            & r1_waybel_0(sK0,X1,X2) )
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_waybel_0(sK0,sK1,X2)
          & r1_waybel_0(sK0,sK1,X2) )
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ~ r2_waybel_0(sK0,sK1,X2)
        & r1_waybel_0(sK0,sK1,X2) )
   => ( ~ r2_waybel_0(sK0,sK1,sK2)
      & r1_waybel_0(sK0,sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(X0,X1,X2)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(X0,X1,X2)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( r1_waybel_0(X0,X1,X2)
               => r2_waybel_0(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
             => r2_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_yellow_6)).

fof(f84,plain,
    ( r2_waybel_0(sK0,sK1,sK2)
    | ~ spl3_8 ),
    inference(resolution,[],[f79,f31])).

fof(f31,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f29,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f79,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k6_subset_1(u1_struct_0(sK0),X0),sK2)
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ r1_xboole_0(k6_subset_1(u1_struct_0(sK0),X0),sK2)
        | r2_waybel_0(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f82,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | ~ spl3_1 ),
    inference(resolution,[],[f40,f18])).

fof(f18,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f80,plain,
    ( spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_6
    | spl3_8
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f76,f62,f78,f58,f46,f42,f38])).

fof(f42,plain,
    ( spl3_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f46,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f58,plain,
    ( spl3_6
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f62,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | ~ r1_waybel_0(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f76,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k6_subset_1(u1_struct_0(sK0),X0),sK2)
        | r2_waybel_0(sK0,sK1,X0)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_7 ),
    inference(resolution,[],[f63,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f63,plain,
    ( ! [X0] :
        ( ~ r1_waybel_0(sK0,sK1,X0)
        | ~ r1_xboole_0(X0,sK2) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f74,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f48,f20])).

fof(f20,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,
    ( v2_struct_0(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f72,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f60,f23])).

fof(f23,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f70,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f56,f22])).

fof(f22,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,
    ( ~ v7_waybel_0(sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_5
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f68,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f52,f21])).

fof(f21,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,
    ( ~ v4_orders_2(sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_4
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f66,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl3_2 ),
    inference(resolution,[],[f44,f19])).

fof(f19,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f64,plain,
    ( spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(avatar_split_clause,[],[f34,f62,f58,f54,f50,f46,f42,f38])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | ~ r1_waybel_0(sK0,sK1,X0)
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f26,f24])).

fof(f24,plain,(
    r1_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_waybel_0(X0,X1,X3)
      | ~ r1_xboole_0(X2,X3)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ~ r1_xboole_0(X2,X3)
              | ~ r1_waybel_0(X0,X1,X3)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ~ r1_xboole_0(X2,X3)
              | ~ r1_waybel_0(X0,X1,X3)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ~ ( r1_xboole_0(X2,X3)
                & r1_waybel_0(X0,X1,X3)
                & r1_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_6)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:45:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (5250)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (5254)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (5262)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (5254)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f64,f66,f68,f70,f72,f74,f80,f82,f88])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    ~spl3_8),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f87])).
% 0.22/0.47  fof(f87,plain,(
% 0.22/0.47    $false | ~spl3_8),
% 0.22/0.47    inference(resolution,[],[f84,f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ~r2_waybel_0(sK0,sK1,sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ((~r2_waybel_0(sK0,sK1,sK2) & r1_waybel_0(sK0,sK1,sK2)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f15,f14,f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (~r2_waybel_0(X0,X1,X2) & r1_waybel_0(X0,X1,X2)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_waybel_0(sK0,X1,X2) & r1_waybel_0(sK0,X1,X2)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ? [X1] : (? [X2] : (~r2_waybel_0(sK0,X1,X2) & r1_waybel_0(sK0,X1,X2)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_waybel_0(sK0,sK1,X2) & r1_waybel_0(sK0,sK1,X2)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ? [X2] : (~r2_waybel_0(sK0,sK1,X2) & r1_waybel_0(sK0,sK1,X2)) => (~r2_waybel_0(sK0,sK1,sK2) & r1_waybel_0(sK0,sK1,sK2))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (~r2_waybel_0(X0,X1,X2) & r1_waybel_0(X0,X1,X2)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (~r2_waybel_0(X0,X1,X2) & r1_waybel_0(X0,X1,X2)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,negated_conjecture,(
% 0.22/0.47    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X2))))),
% 0.22/0.47    inference(negated_conjecture,[],[f5])).
% 0.22/0.47  fof(f5,conjecture,(
% 0.22/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X2))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_yellow_6)).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    r2_waybel_0(sK0,sK1,sK2) | ~spl3_8),
% 0.22/0.47    inference(resolution,[],[f79,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(k6_subset_1(X0,X1),X1)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f29,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_xboole_0(k6_subset_1(u1_struct_0(sK0),X0),sK2) | r2_waybel_0(sK0,sK1,X0)) ) | ~spl3_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f78])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    spl3_8 <=> ! [X0] : (~r1_xboole_0(k6_subset_1(u1_struct_0(sK0),X0),sK2) | r2_waybel_0(sK0,sK1,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    ~spl3_1),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f81])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    $false | ~spl3_1),
% 0.22/0.47    inference(resolution,[],[f40,f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ~v2_struct_0(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    v2_struct_0(sK0) | ~spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    spl3_1 <=> v2_struct_0(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    spl3_1 | ~spl3_2 | spl3_3 | ~spl3_6 | spl3_8 | ~spl3_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f76,f62,f78,f58,f46,f42,f38])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    spl3_2 <=> l1_struct_0(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    spl3_3 <=> v2_struct_0(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    spl3_6 <=> l1_waybel_0(sK1,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    spl3_7 <=> ! [X0] : (~r1_xboole_0(X0,sK2) | ~r1_waybel_0(sK0,sK1,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_xboole_0(k6_subset_1(u1_struct_0(sK0),X0),sK2) | r2_waybel_0(sK0,sK1,X0) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) ) | ~spl3_7),
% 0.22/0.47    inference(resolution,[],[f63,f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_waybel_0(sK0,sK1,X0) | ~r1_xboole_0(X0,sK2)) ) | ~spl3_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f62])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    ~spl3_3),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f73])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    $false | ~spl3_3),
% 0.22/0.47    inference(resolution,[],[f48,f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ~v2_struct_0(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    v2_struct_0(sK1) | ~spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f46])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    spl3_6),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f71])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    $false | spl3_6),
% 0.22/0.47    inference(resolution,[],[f60,f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    l1_waybel_0(sK1,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    ~l1_waybel_0(sK1,sK0) | spl3_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f58])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    spl3_5),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f69])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    $false | spl3_5),
% 0.22/0.47    inference(resolution,[],[f56,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    v7_waybel_0(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    ~v7_waybel_0(sK1) | spl3_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f54])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    spl3_5 <=> v7_waybel_0(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl3_4),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    $false | spl3_4),
% 0.22/0.48    inference(resolution,[],[f52,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    v4_orders_2(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ~v4_orders_2(sK1) | spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    spl3_4 <=> v4_orders_2(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl3_2),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    $false | spl3_2),
% 0.22/0.48    inference(resolution,[],[f44,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    l1_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ~l1_struct_0(sK0) | spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f42])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl3_1 | ~spl3_2 | spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | spl3_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f62,f58,f54,f50,f46,f42,f38])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~r1_waybel_0(sK0,sK1,X0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f26,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    r1_waybel_0(sK0,sK1,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r1_waybel_0(X0,X1,X3) | ~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2,X3] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2,X3] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2,X3] : ~(r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_6)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (5254)------------------------------
% 0.22/0.48  % (5254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (5254)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (5253)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (5254)Memory used [KB]: 6140
% 0.22/0.48  % (5254)Time elapsed: 0.054 s
% 0.22/0.48  % (5254)------------------------------
% 0.22/0.48  % (5254)------------------------------
% 0.22/0.48  % (5256)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (5264)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (5249)Success in time 0.109 s
%------------------------------------------------------------------------------
