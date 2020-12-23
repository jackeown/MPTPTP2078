%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 342 expanded)
%              Number of leaves         :   15 ( 111 expanded)
%              Depth                    :   19
%              Number of atoms          :  346 (2162 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f144,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f136,f143])).

fof(f143,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f139,f43])).

fof(f43,plain,(
    ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3))
    & l1_waybel_0(sK4,sK3)
    & v7_waybel_0(sK4)
    & v4_orders_2(sK4)
    & ~ v2_struct_0(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f9,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK3,X1,u1_struct_0(sK3))
          & l1_waybel_0(X1,sK3)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ~ r1_waybel_0(sK3,X1,u1_struct_0(sK3))
        & l1_waybel_0(X1,sK3)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3))
      & l1_waybel_0(sK4,sK3)
      & v7_waybel_0(sK4)
      & v4_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f139,plain,
    ( r1_waybel_0(sK3,sK4,u1_struct_0(sK3))
    | ~ spl7_5 ),
    inference(resolution,[],[f138,f68])).

fof(f68,plain,(
    ! [X1] :
      ( ~ sP1(sK3,sK4,X1)
      | r1_waybel_0(sK3,sK4,X1) ) ),
    inference(resolution,[],[f66,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X1,X0,X2)
      | r1_waybel_0(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_waybel_0(X1,X0,X2)
            | ~ sP1(X1,X0,X2) )
          & ( sP1(X1,X0,X2)
            | ~ r1_waybel_0(X1,X0,X2) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( ( r1_waybel_0(X0,X1,X2)
            | ~ sP1(X0,X1,X2) )
          & ( sP1(X0,X1,X2)
            | ~ r1_waybel_0(X0,X1,X2) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( r1_waybel_0(X0,X1,X2)
        <=> sP1(X0,X1,X2) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f66,plain,(
    sP2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f65,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,
    ( v2_struct_0(sK4)
    | sP2(sK4,sK3) ),
    inference(resolution,[],[f61,f42])).

fof(f42,plain,(
    l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X2] :
      ( ~ l1_waybel_0(X2,sK3)
      | v2_struct_0(X2)
      | sP2(X2,sK3) ) ),
    inference(subsumption_resolution,[],[f59,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f26])).

% (2318)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
fof(f59,plain,(
    ! [X2] :
      ( ~ l1_waybel_0(X2,sK3)
      | v2_struct_0(X2)
      | sP2(X2,sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f38,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | sP2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f13,f22,f21,f20])).

fof(f20,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          | ~ r1_orders_2(X1,X3,X4)
          | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ? [X3] :
          ( sP0(X2,X1,X0,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
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
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f38,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f138,plain,
    ( sP1(sK3,sK4,u1_struct_0(sK3))
    | ~ spl7_5 ),
    inference(resolution,[],[f137,f73])).

fof(f73,plain,(
    ! [X4,X3] :
      ( ~ sP0(X3,sK4,X4,o_2_2_yellow_6(sK3,sK4))
      | sP1(X4,sK4,X3) ) ),
    inference(resolution,[],[f71,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ sP0(X2,X1,X0,X3)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( ~ sP0(X2,X1,X0,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( sP0(X2,X1,X0,sK5(X0,X1,X2))
          & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( sP0(X2,X1,X0,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( sP0(X2,X1,X0,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( ~ sP0(X2,X1,X0,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( sP0(X2,X1,X0,X4)
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( ~ sP0(X2,X1,X0,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( sP0(X2,X1,X0,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f71,plain,(
    m1_subset_1(o_2_2_yellow_6(sK3,sK4),u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f70,f37])).

fof(f70,plain,
    ( m1_subset_1(o_2_2_yellow_6(sK3,sK4),u1_struct_0(sK4))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f69,f38])).

fof(f69,plain,
    ( m1_subset_1(o_2_2_yellow_6(sK3,sK4),u1_struct_0(sK4))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f64,f42])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK4,X0)
      | m1_subset_1(o_2_2_yellow_6(X0,sK4),u1_struct_0(sK4))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f63,f39])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK4,X0)
      | m1_subset_1(o_2_2_yellow_6(X0,sK4),u1_struct_0(sK4))
      | v2_struct_0(sK4)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f62,f40])).

fof(f40,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK4,X0)
      | m1_subset_1(o_2_2_yellow_6(X0,sK4),u1_struct_0(sK4))
      | ~ v4_orders_2(sK4)
      | v2_struct_0(sK4)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f41,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).

fof(f41,plain,(
    v7_waybel_0(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f137,plain,
    ( sP0(u1_struct_0(sK3),sK4,sK3,o_2_2_yellow_6(sK3,sK4))
    | ~ spl7_5 ),
    inference(resolution,[],[f131,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X3)),X0)
      | sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ~ r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X3)),X0)
          & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
          & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( r2_hidden(k2_waybel_0(X2,X1,X5),X0)
            | ~ r1_orders_2(X1,X3,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).

fof(f35,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X3)),X0)
        & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
            & r1_orders_2(X1,X3,X4)
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( r2_hidden(k2_waybel_0(X2,X1,X5),X0)
            | ~ r1_orders_2(X1,X3,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            & r1_orders_2(X1,X3,X4)
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,X3,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f131,plain,
    ( r2_hidden(k2_waybel_0(sK3,sK4,sK6(u1_struct_0(sK3),sK4,sK3,o_2_2_yellow_6(sK3,sK4))),u1_struct_0(sK3))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl7_5
  <=> r2_hidden(k2_waybel_0(sK3,sK4,sK6(u1_struct_0(sK3),sK4,sK3,o_2_2_yellow_6(sK3,sK4))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f136,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f134,f37])).

fof(f134,plain,
    ( v2_struct_0(sK3)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f133,f38])).

fof(f133,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_4 ),
    inference(resolution,[],[f110,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f110,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_4
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f132,plain,
    ( spl7_5
    | spl7_4 ),
    inference(avatar_split_clause,[],[f116,f108,f129])).

fof(f116,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | r2_hidden(k2_waybel_0(sK3,sK4,sK6(u1_struct_0(sK3),sK4,sK3,o_2_2_yellow_6(sK3,sK4))),u1_struct_0(sK3)) ),
    inference(resolution,[],[f99,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f99,plain,(
    m1_subset_1(k2_waybel_0(sK3,sK4,sK6(u1_struct_0(sK3),sK4,sK3,o_2_2_yellow_6(sK3,sK4))),u1_struct_0(sK3)) ),
    inference(resolution,[],[f97,f91])).

fof(f91,plain,(
    m1_subset_1(sK6(u1_struct_0(sK3),sK4,sK3,o_2_2_yellow_6(sK3,sK4)),u1_struct_0(sK4)) ),
    inference(resolution,[],[f90,f43])).

fof(f90,plain,(
    ! [X4] :
      ( r1_waybel_0(sK3,sK4,X4)
      | m1_subset_1(sK6(X4,sK4,sK3,o_2_2_yellow_6(sK3,sK4)),u1_struct_0(sK4)) ) ),
    inference(resolution,[],[f86,f68])).

fof(f86,plain,(
    ! [X0,X1] :
      ( sP1(X0,sK4,X1)
      | m1_subset_1(sK6(X1,sK4,X0,o_2_2_yellow_6(sK3,sK4)),u1_struct_0(sK4)) ) ),
    inference(resolution,[],[f73,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
      | m1_subset_1(k2_waybel_0(sK3,sK4,X0),u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f96,f39])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
      | v2_struct_0(sK4)
      | m1_subset_1(k2_waybel_0(sK3,sK4,X0),u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f60,f42])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | m1_subset_1(k2_waybel_0(sK3,X1,X0),u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f58,f37])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,sK3)
      | v2_struct_0(X1)
      | m1_subset_1(k2_waybel_0(sK3,X1,X0),u1_struct_0(sK3))
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f38,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_waybel_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (2322)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.46  % (2315)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.46  % (2315)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f144,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f132,f136,f143])).
% 0.21/0.46  fof(f143,plain,(
% 0.21/0.46    ~spl7_5),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f142])).
% 0.21/0.46  fof(f142,plain,(
% 0.21/0.46    $false | ~spl7_5),
% 0.21/0.46    inference(subsumption_resolution,[],[f139,f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ~r1_waybel_0(sK3,sK4,u1_struct_0(sK3))),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    (~r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) & l1_waybel_0(sK4,sK3) & v7_waybel_0(sK4) & v4_orders_2(sK4) & ~v2_struct_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f9,f25,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK3,X1,u1_struct_0(sK3)) & l1_waybel_0(X1,sK3) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ? [X1] : (~r1_waybel_0(sK3,X1,u1_struct_0(sK3)) & l1_waybel_0(X1,sK3) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) & l1_waybel_0(sK4,sK3) & v7_waybel_0(sK4) & v4_orders_2(sK4) & ~v2_struct_0(sK4))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.46    inference(negated_conjecture,[],[f6])).
% 0.21/0.46  fof(f6,conjecture,(
% 0.21/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) | ~spl7_5),
% 0.21/0.46    inference(resolution,[],[f138,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X1] : (~sP1(sK3,sK4,X1) | r1_waybel_0(sK3,sK4,X1)) )),
% 0.21/0.46    inference(resolution,[],[f66,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~sP2(X0,X1) | ~sP1(X1,X0,X2) | r1_waybel_0(X1,X0,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : ((r1_waybel_0(X1,X0,X2) | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | ~r1_waybel_0(X1,X0,X2))) | ~sP2(X0,X1))),
% 0.21/0.46    inference(rectify,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X1,X0] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | ~r1_waybel_0(X0,X1,X2))) | ~sP2(X1,X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X1,X0] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> sP1(X0,X1,X2)) | ~sP2(X1,X0))),
% 0.21/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    sP2(sK4,sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f65,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ~v2_struct_0(sK4)),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    v2_struct_0(sK4) | sP2(sK4,sK3)),
% 0.21/0.46    inference(resolution,[],[f61,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    l1_waybel_0(sK4,sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ( ! [X2] : (~l1_waybel_0(X2,sK3) | v2_struct_0(X2) | sP2(X2,sK3)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f59,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ~v2_struct_0(sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  % (2318)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ( ! [X2] : (~l1_waybel_0(X2,sK3) | v2_struct_0(X2) | sP2(X2,sK3) | v2_struct_0(sK3)) )),
% 0.21/0.46    inference(resolution,[],[f38,f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | sP2(X1,X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (sP2(X1,X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(definition_folding,[],[f13,f22,f21,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))))),
% 0.21/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ? [X3] : (sP0(X2,X1,X0,X3) & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.21/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    l1_struct_0(sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    sP1(sK3,sK4,u1_struct_0(sK3)) | ~spl7_5),
% 0.21/0.46    inference(resolution,[],[f137,f73])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    ( ! [X4,X3] : (~sP0(X3,sK4,X4,o_2_2_yellow_6(sK3,sK4)) | sP1(X4,sK4,X3)) )),
% 0.21/0.46    inference(resolution,[],[f71,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,u1_struct_0(X1)) | ~sP0(X2,X1,X0,X3) | sP1(X0,X1,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (~sP0(X2,X1,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((sP0(X2,X1,X0,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X2,X1,X0] : (? [X4] : (sP0(X2,X1,X0,X4) & m1_subset_1(X4,u1_struct_0(X1))) => (sP0(X2,X1,X0,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (~sP0(X2,X1,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (sP0(X2,X1,X0,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 0.21/0.46    inference(rectify,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (~sP0(X2,X1,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (sP0(X2,X1,X0,X3) & m1_subset_1(X3,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 0.21/0.46    inference(nnf_transformation,[],[f21])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    m1_subset_1(o_2_2_yellow_6(sK3,sK4),u1_struct_0(sK4))),
% 0.21/0.46    inference(subsumption_resolution,[],[f70,f37])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    m1_subset_1(o_2_2_yellow_6(sK3,sK4),u1_struct_0(sK4)) | v2_struct_0(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f69,f38])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    m1_subset_1(o_2_2_yellow_6(sK3,sK4),u1_struct_0(sK4)) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.21/0.46    inference(resolution,[],[f64,f42])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_waybel_0(sK4,X0) | m1_subset_1(o_2_2_yellow_6(X0,sK4),u1_struct_0(sK4)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f63,f39])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_waybel_0(sK4,X0) | m1_subset_1(o_2_2_yellow_6(X0,sK4),u1_struct_0(sK4)) | v2_struct_0(sK4) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f62,f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    v4_orders_2(sK4)),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_waybel_0(sK4,X0) | m1_subset_1(o_2_2_yellow_6(X0,sK4),u1_struct_0(sK4)) | ~v4_orders_2(sK4) | v2_struct_0(sK4) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(resolution,[],[f41,f56])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    v7_waybel_0(sK4)),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    sP0(u1_struct_0(sK3),sK4,sK3,o_2_2_yellow_6(sK3,sK4)) | ~spl7_5),
% 0.21/0.46    inference(resolution,[],[f131,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X3)),X0) | sP0(X0,X1,X2,X3)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (~r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X3)),X0) & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3)) & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)))) & (! [X5] : (r2_hidden(k2_waybel_0(X2,X1,X5),X0) | ~r1_orders_2(X1,X3,X5) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ! [X3,X2,X1,X0] : (? [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X3)),X0) & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3)) & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))) & (! [X5] : (r2_hidden(k2_waybel_0(X2,X1,X5),X0) | ~r1_orders_2(X1,X3,X5) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.46    inference(rectify,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))) & (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X2,X1,X0,X3)))),
% 0.21/0.46    inference(nnf_transformation,[],[f20])).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    r2_hidden(k2_waybel_0(sK3,sK4,sK6(u1_struct_0(sK3),sK4,sK3,o_2_2_yellow_6(sK3,sK4))),u1_struct_0(sK3)) | ~spl7_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f129])).
% 0.21/0.46  fof(f129,plain,(
% 0.21/0.46    spl7_5 <=> r2_hidden(k2_waybel_0(sK3,sK4,sK6(u1_struct_0(sK3),sK4,sK3,o_2_2_yellow_6(sK3,sK4))),u1_struct_0(sK3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.46  fof(f136,plain,(
% 0.21/0.46    ~spl7_4),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f135])).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    $false | ~spl7_4),
% 0.21/0.46    inference(subsumption_resolution,[],[f134,f37])).
% 0.21/0.46  fof(f134,plain,(
% 0.21/0.46    v2_struct_0(sK3) | ~spl7_4),
% 0.21/0.46    inference(subsumption_resolution,[],[f133,f38])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~spl7_4),
% 0.21/0.46    inference(resolution,[],[f110,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    v1_xboole_0(u1_struct_0(sK3)) | ~spl7_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f108])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    spl7_4 <=> v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.46  fof(f132,plain,(
% 0.21/0.46    spl7_5 | spl7_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f116,f108,f129])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    v1_xboole_0(u1_struct_0(sK3)) | r2_hidden(k2_waybel_0(sK3,sK4,sK6(u1_struct_0(sK3),sK4,sK3,o_2_2_yellow_6(sK3,sK4))),u1_struct_0(sK3))),
% 0.21/0.46    inference(resolution,[],[f99,f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    m1_subset_1(k2_waybel_0(sK3,sK4,sK6(u1_struct_0(sK3),sK4,sK3,o_2_2_yellow_6(sK3,sK4))),u1_struct_0(sK3))),
% 0.21/0.46    inference(resolution,[],[f97,f91])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    m1_subset_1(sK6(u1_struct_0(sK3),sK4,sK3,o_2_2_yellow_6(sK3,sK4)),u1_struct_0(sK4))),
% 0.21/0.46    inference(resolution,[],[f90,f43])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    ( ! [X4] : (r1_waybel_0(sK3,sK4,X4) | m1_subset_1(sK6(X4,sK4,sK3,o_2_2_yellow_6(sK3,sK4)),u1_struct_0(sK4))) )),
% 0.21/0.46    inference(resolution,[],[f86,f68])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ( ! [X0,X1] : (sP1(X0,sK4,X1) | m1_subset_1(sK6(X1,sK4,X0,o_2_2_yellow_6(sK3,sK4)),u1_struct_0(sK4))) )),
% 0.21/0.46    inference(resolution,[],[f73,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f36])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK4)) | m1_subset_1(k2_waybel_0(sK3,sK4,X0),u1_struct_0(sK3))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f96,f39])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK4)) | v2_struct_0(sK4) | m1_subset_1(k2_waybel_0(sK3,sK4,X0),u1_struct_0(sK3))) )),
% 0.21/0.46    inference(resolution,[],[f60,f42])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_waybel_0(X1,sK3) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | m1_subset_1(k2_waybel_0(sK3,X1,X0),u1_struct_0(sK3))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f58,f37])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(X1,sK3) | v2_struct_0(X1) | m1_subset_1(k2_waybel_0(sK3,X1,X0),u1_struct_0(sK3)) | v2_struct_0(sK3)) )),
% 0.21/0.46    inference(resolution,[],[f38,f57])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_waybel_0)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (2315)------------------------------
% 0.21/0.46  % (2315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (2315)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (2315)Memory used [KB]: 9978
% 0.21/0.46  % (2315)Time elapsed: 0.050 s
% 0.21/0.46  % (2315)------------------------------
% 0.21/0.46  % (2315)------------------------------
% 0.21/0.47  % (2299)Success in time 0.11 s
%------------------------------------------------------------------------------
