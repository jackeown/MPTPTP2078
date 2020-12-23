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
% DateTime   : Thu Dec  3 13:22:42 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 176 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  434 ( 869 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f290,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f105,f108,f212,f214,f219,f240,f262,f288])).

fof(f288,plain,(
    ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | ~ spl10_7 ),
    inference(resolution,[],[f266,f77])).

% (7204)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (7205)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (7212)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f77,plain,(
    ! [X0] : sP2(k1_xboole_0,X0,X0) ),
    inference(superposition,[],[f75,f72])).

fof(f72,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f49,f61])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f75,plain,(
    ! [X0,X1] : sP2(X1,X0,k6_subset_1(X0,X1)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f70,f61])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP2(X1,X0,X2) )
      & ( sP2(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP2(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f20])).

fof(f20,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f266,plain,
    ( ! [X4] : ~ sP2(k1_xboole_0,X4,k1_xboole_0)
    | ~ spl10_7 ),
    inference(resolution,[],[f235,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP2(X1,X2,X1) ) ),
    inference(condensation,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X0)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0) ) ),
    inference(resolution,[],[f82,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK8(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK8(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f16,f34])).

fof(f34,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK8(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK8(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK8(X0),X1)
      | ~ sP2(X0,X2,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(resolution,[],[f65,f62])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( r2_hidden(sK9(X0,X1,X2),X0)
            | ~ r2_hidden(sK9(X0,X1,X2),X1)
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK9(X0,X1,X2),X0)
              & r2_hidden(sK9(X0,X1,X2),X1) )
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK9(X0,X1,X2),X0)
          | ~ r2_hidden(sK9(X0,X1,X2),X1)
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK9(X0,X1,X2),X0)
            & r2_hidden(sK9(X0,X1,X2),X1) )
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

% (7187)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f235,plain,
    ( r2_hidden(k2_waybel_0(sK3,sK4,sK6(k1_xboole_0,sK4,sK3,sK7(u1_struct_0(sK4)))),k1_xboole_0)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl10_7
  <=> r2_hidden(k2_waybel_0(sK3,sK4,sK6(k1_xboole_0,sK4,sK3,sK7(u1_struct_0(sK4)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f262,plain,(
    ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl10_8 ),
    inference(resolution,[],[f239,f48])).

fof(f48,plain,(
    ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3))
    & l1_waybel_0(sK4,sK3)
    & v7_waybel_0(sK4)
    & v4_orders_2(sK4)
    & ~ v2_struct_0(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f11,f23,f22])).

fof(f22,plain,
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

fof(f23,plain,
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

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f239,plain,
    ( r1_waybel_0(sK3,sK4,u1_struct_0(sK3))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl10_8
  <=> r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f240,plain,
    ( spl10_7
    | spl10_8
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f227,f217,f102,f237,f233])).

fof(f102,plain,
    ( spl10_4
  <=> sP1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f217,plain,
    ( spl10_6
  <=> ! [X0] :
        ( r2_waybel_0(sK3,sK4,X0)
        | r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f227,plain,
    ( r1_waybel_0(sK3,sK4,u1_struct_0(sK3))
    | r2_hidden(k2_waybel_0(sK3,sK4,sK6(k1_xboole_0,sK4,sK3,sK7(u1_struct_0(sK4)))),k1_xboole_0)
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(superposition,[],[f224,f72])).

fof(f224,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0))
        | r2_hidden(k2_waybel_0(sK3,sK4,sK6(X0,sK4,sK3,sK7(u1_struct_0(sK4)))),X0) )
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(resolution,[],[f223,f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f4,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f223,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK4))
        | r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X1))
        | r2_hidden(k2_waybel_0(sK3,sK4,sK6(X1,sK4,sK3,X2)),X1) )
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(resolution,[],[f220,f56])).

fof(f56,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X5)),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
              | ~ r1_orders_2(X1,sK5(X0,X1,X2),X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( ( r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X5)),X0)
              & r1_orders_2(X1,X5,sK6(X0,X1,X2,X5))
              & m1_subset_1(sK6(X0,X1,X2,X5),u1_struct_0(X1)) )
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f28,f30,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
            | ~ r1_orders_2(X1,sK5(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X2,X1,X6),X0)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X5)),X0)
        & r1_orders_2(X1,X5,sK6(X0,X1,X2,X5))
        & m1_subset_1(sK6(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ! [X4] :
                ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( ? [X6] :
                ( r2_hidden(k2_waybel_0(X2,X1,X6),X0)
                & r1_orders_2(X1,X5,X6)
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ? [X3] :
            ( ! [X4] :
                ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ! [X3] :
          ( ? [X4] :
              ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              & r1_orders_2(X1,X3,X4)
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f220,plain,
    ( ! [X0] :
        ( sP0(X0,sK4,sK3)
        | r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0)) )
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(resolution,[],[f218,f110])).

fof(f110,plain,
    ( ! [X1] :
        ( ~ r2_waybel_0(sK3,sK4,X1)
        | sP0(X1,sK4,sK3) )
    | ~ spl10_4 ),
    inference(resolution,[],[f104,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ r2_waybel_0(X0,X1,X2)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_waybel_0(X0,X1,X2)
            | ~ sP0(X2,X1,X0) )
          & ( sP0(X2,X1,X0)
            | ~ r2_waybel_0(X0,X1,X2) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_waybel_0(X0,X1,X2)
        <=> sP0(X2,X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f104,plain,
    ( sP1(sK3,sK4)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f218,plain,
    ( ! [X0] :
        ( r2_waybel_0(sK3,sK4,X0)
        | r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0)) )
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( spl10_3
    | spl10_6
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f215,f210,f217,f98])).

fof(f98,plain,
    ( spl10_3
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f210,plain,
    ( spl10_5
  <=> ! [X1,X0] :
        ( r1_waybel_0(sK3,X0,k6_subset_1(u1_struct_0(sK3),X1))
        | r2_waybel_0(sK3,X0,X1)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f215,plain,
    ( ! [X0] :
        ( r2_waybel_0(sK3,sK4,X0)
        | v2_struct_0(sK4)
        | r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0)) )
    | ~ spl10_5 ),
    inference(resolution,[],[f211,f47])).

fof(f47,plain,(
    l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f211,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(X0,sK3)
        | r2_waybel_0(sK3,X0,X1)
        | v2_struct_0(X0)
        | r1_waybel_0(sK3,X0,k6_subset_1(u1_struct_0(sK3),X1)) )
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f210])).

fof(f214,plain,(
    ~ spl10_1 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl10_1 ),
    inference(resolution,[],[f91,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f91,plain,
    ( v2_struct_0(sK3)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl10_1
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f212,plain,
    ( spl10_1
    | spl10_5 ),
    inference(avatar_split_clause,[],[f208,f210,f89])).

fof(f208,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(sK3,X0,k6_subset_1(u1_struct_0(sK3),X1))
      | ~ l1_waybel_0(X0,sK3)
      | v2_struct_0(X0)
      | r2_waybel_0(sK3,X0,X1)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f51,f43])).

fof(f43,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r2_waybel_0(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f108,plain,(
    ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | ~ spl10_3 ),
    inference(resolution,[],[f100,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f100,plain,
    ( v2_struct_0(sK4)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f105,plain,
    ( spl10_3
    | spl10_4
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f96,f93,f102,f98])).

fof(f93,plain,
    ( spl10_2
  <=> ! [X0] :
        ( ~ l1_waybel_0(X0,sK3)
        | sP1(sK3,X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f96,plain,
    ( sP1(sK3,sK4)
    | v2_struct_0(sK4)
    | ~ spl10_2 ),
    inference(resolution,[],[f94,f47])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK3)
        | sP1(sK3,X0)
        | v2_struct_0(X0) )
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f95,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f87,f93,f89])).

fof(f87,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK3)
      | v2_struct_0(X0)
      | sP1(sK3,X0)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f59,f43])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | sP1(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f18,f17])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (7189)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.25/0.52  % (7196)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.52  % (7196)Refutation found. Thanks to Tanya!
% 1.25/0.52  % SZS status Theorem for theBenchmark
% 1.25/0.52  % SZS output start Proof for theBenchmark
% 1.25/0.52  fof(f290,plain,(
% 1.25/0.52    $false),
% 1.25/0.52    inference(avatar_sat_refutation,[],[f95,f105,f108,f212,f214,f219,f240,f262,f288])).
% 1.25/0.52  fof(f288,plain,(
% 1.25/0.52    ~spl10_7),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f283])).
% 1.25/0.52  fof(f283,plain,(
% 1.25/0.52    $false | ~spl10_7),
% 1.25/0.52    inference(resolution,[],[f266,f77])).
% 1.25/0.52  % (7204)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.25/0.52  % (7205)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.25/0.53  % (7212)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.25/0.53  fof(f77,plain,(
% 1.25/0.53    ( ! [X0] : (sP2(k1_xboole_0,X0,X0)) )),
% 1.25/0.53    inference(superposition,[],[f75,f72])).
% 1.25/0.53  fof(f72,plain,(
% 1.25/0.53    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 1.25/0.53    inference(definition_unfolding,[],[f49,f61])).
% 1.25/0.53  fof(f61,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f5])).
% 1.25/0.53  fof(f5,axiom,(
% 1.25/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.25/0.53  fof(f49,plain,(
% 1.25/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.25/0.53    inference(cnf_transformation,[],[f2])).
% 1.25/0.53  fof(f2,axiom,(
% 1.25/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.25/0.53  fof(f75,plain,(
% 1.25/0.53    ( ! [X0,X1] : (sP2(X1,X0,k6_subset_1(X0,X1))) )),
% 1.25/0.53    inference(equality_resolution,[],[f74])).
% 1.25/0.53  fof(f74,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k6_subset_1(X0,X1) != X2) )),
% 1.25/0.53    inference(definition_unfolding,[],[f70,f61])).
% 1.25/0.53  fof(f70,plain,(
% 1.25/0.53    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.25/0.53    inference(cnf_transformation,[],[f41])).
% 1.25/0.53  fof(f41,plain,(
% 1.25/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.25/0.53    inference(nnf_transformation,[],[f21])).
% 1.25/0.53  fof(f21,plain,(
% 1.25/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP2(X1,X0,X2))),
% 1.25/0.53    inference(definition_folding,[],[f1,f20])).
% 1.25/0.53  fof(f20,plain,(
% 1.25/0.53    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.25/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.25/0.53  fof(f1,axiom,(
% 1.25/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.38/0.53  fof(f266,plain,(
% 1.38/0.53    ( ! [X4] : (~sP2(k1_xboole_0,X4,k1_xboole_0)) ) | ~spl10_7),
% 1.38/0.53    inference(resolution,[],[f235,f85])).
% 1.38/0.53  fof(f85,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~sP2(X1,X2,X1)) )),
% 1.38/0.53    inference(condensation,[],[f84])).
% 1.38/0.53  fof(f84,plain,(
% 1.38/0.53    ( ! [X2,X0,X3,X1] : (~sP2(X0,X1,X0) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0)) )),
% 1.38/0.53    inference(resolution,[],[f82,f62])).
% 1.38/0.53  fof(f62,plain,(
% 1.38/0.53    ( ! [X0,X1] : (r2_hidden(sK8(X1),X1) | ~r2_hidden(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f35])).
% 1.38/0.53  fof(f35,plain,(
% 1.38/0.53    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK8(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK8(X1),X1)) | ~r2_hidden(X0,X1))),
% 1.38/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f16,f34])).
% 1.38/0.53  fof(f34,plain,(
% 1.38/0.53    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK8(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK8(X1),X1)))),
% 1.38/0.53    introduced(choice_axiom,[])).
% 1.38/0.53  fof(f16,plain,(
% 1.38/0.53    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 1.38/0.53    inference(ennf_transformation,[],[f3])).
% 1.38/0.53  fof(f3,axiom,(
% 1.38/0.53    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 1.38/0.53  fof(f82,plain,(
% 1.38/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK8(X0),X1) | ~sP2(X0,X2,X1) | ~r2_hidden(X3,X0)) )),
% 1.38/0.53    inference(resolution,[],[f65,f62])).
% 1.38/0.53  fof(f65,plain,(
% 1.38/0.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | ~sP2(X0,X1,X2)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f40])).
% 1.38/0.53  fof(f40,plain,(
% 1.38/0.53    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((r2_hidden(sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(sK9(X0,X1,X2),X2)) & ((~r2_hidden(sK9(X0,X1,X2),X0) & r2_hidden(sK9(X0,X1,X2),X1)) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 1.38/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f39])).
% 1.38/0.53  fof(f39,plain,(
% 1.38/0.53    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(sK9(X0,X1,X2),X2)) & ((~r2_hidden(sK9(X0,X1,X2),X0) & r2_hidden(sK9(X0,X1,X2),X1)) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 1.38/0.53    introduced(choice_axiom,[])).
% 1.38/0.53  % (7187)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.53  fof(f38,plain,(
% 1.38/0.53    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 1.38/0.53    inference(rectify,[],[f37])).
% 1.38/0.53  fof(f37,plain,(
% 1.38/0.53    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 1.38/0.53    inference(flattening,[],[f36])).
% 1.38/0.53  fof(f36,plain,(
% 1.38/0.53    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 1.38/0.53    inference(nnf_transformation,[],[f20])).
% 1.38/0.53  fof(f235,plain,(
% 1.38/0.53    r2_hidden(k2_waybel_0(sK3,sK4,sK6(k1_xboole_0,sK4,sK3,sK7(u1_struct_0(sK4)))),k1_xboole_0) | ~spl10_7),
% 1.38/0.53    inference(avatar_component_clause,[],[f233])).
% 1.38/0.53  fof(f233,plain,(
% 1.38/0.53    spl10_7 <=> r2_hidden(k2_waybel_0(sK3,sK4,sK6(k1_xboole_0,sK4,sK3,sK7(u1_struct_0(sK4)))),k1_xboole_0)),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 1.38/0.53  fof(f262,plain,(
% 1.38/0.53    ~spl10_8),
% 1.38/0.53    inference(avatar_contradiction_clause,[],[f261])).
% 1.38/0.53  fof(f261,plain,(
% 1.38/0.53    $false | ~spl10_8),
% 1.38/0.53    inference(resolution,[],[f239,f48])).
% 1.38/0.53  fof(f48,plain,(
% 1.38/0.53    ~r1_waybel_0(sK3,sK4,u1_struct_0(sK3))),
% 1.38/0.53    inference(cnf_transformation,[],[f24])).
% 1.38/0.53  fof(f24,plain,(
% 1.38/0.53    (~r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) & l1_waybel_0(sK4,sK3) & v7_waybel_0(sK4) & v4_orders_2(sK4) & ~v2_struct_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 1.38/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f11,f23,f22])).
% 1.38/0.53  fof(f22,plain,(
% 1.38/0.53    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK3,X1,u1_struct_0(sK3)) & l1_waybel_0(X1,sK3) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 1.38/0.53    introduced(choice_axiom,[])).
% 1.38/0.53  fof(f23,plain,(
% 1.38/0.53    ? [X1] : (~r1_waybel_0(sK3,X1,u1_struct_0(sK3)) & l1_waybel_0(X1,sK3) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) & l1_waybel_0(sK4,sK3) & v7_waybel_0(sK4) & v4_orders_2(sK4) & ~v2_struct_0(sK4))),
% 1.38/0.53    introduced(choice_axiom,[])).
% 1.38/0.53  fof(f11,plain,(
% 1.38/0.53    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.38/0.53    inference(flattening,[],[f10])).
% 1.38/0.53  fof(f10,plain,(
% 1.38/0.53    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.38/0.53    inference(ennf_transformation,[],[f9])).
% 1.38/0.53  fof(f9,negated_conjecture,(
% 1.38/0.53    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.38/0.53    inference(negated_conjecture,[],[f8])).
% 1.38/0.53  fof(f8,conjecture,(
% 1.38/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).
% 1.38/0.53  fof(f239,plain,(
% 1.38/0.53    r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) | ~spl10_8),
% 1.38/0.53    inference(avatar_component_clause,[],[f237])).
% 1.38/0.53  fof(f237,plain,(
% 1.38/0.53    spl10_8 <=> r1_waybel_0(sK3,sK4,u1_struct_0(sK3))),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 1.38/0.53  fof(f240,plain,(
% 1.38/0.53    spl10_7 | spl10_8 | ~spl10_4 | ~spl10_6),
% 1.38/0.53    inference(avatar_split_clause,[],[f227,f217,f102,f237,f233])).
% 1.38/0.53  fof(f102,plain,(
% 1.38/0.53    spl10_4 <=> sP1(sK3,sK4)),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.38/0.53  fof(f217,plain,(
% 1.38/0.53    spl10_6 <=> ! [X0] : (r2_waybel_0(sK3,sK4,X0) | r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0)))),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.38/0.53  fof(f227,plain,(
% 1.38/0.53    r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) | r2_hidden(k2_waybel_0(sK3,sK4,sK6(k1_xboole_0,sK4,sK3,sK7(u1_struct_0(sK4)))),k1_xboole_0) | (~spl10_4 | ~spl10_6)),
% 1.38/0.53    inference(superposition,[],[f224,f72])).
% 1.38/0.53  fof(f224,plain,(
% 1.38/0.53    ( ! [X0] : (r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0)) | r2_hidden(k2_waybel_0(sK3,sK4,sK6(X0,sK4,sK3,sK7(u1_struct_0(sK4)))),X0)) ) | (~spl10_4 | ~spl10_6)),
% 1.38/0.53    inference(resolution,[],[f223,f60])).
% 1.38/0.53  fof(f60,plain,(
% 1.38/0.53    ( ! [X0] : (m1_subset_1(sK7(X0),X0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f33])).
% 1.38/0.53  fof(f33,plain,(
% 1.38/0.53    ! [X0] : m1_subset_1(sK7(X0),X0)),
% 1.38/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f4,f32])).
% 1.38/0.53  fof(f32,plain,(
% 1.38/0.53    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK7(X0),X0))),
% 1.38/0.53    introduced(choice_axiom,[])).
% 1.38/0.53  fof(f4,axiom,(
% 1.38/0.53    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 1.38/0.53  fof(f223,plain,(
% 1.38/0.53    ( ! [X2,X1] : (~m1_subset_1(X2,u1_struct_0(sK4)) | r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X1)) | r2_hidden(k2_waybel_0(sK3,sK4,sK6(X1,sK4,sK3,X2)),X1)) ) | (~spl10_4 | ~spl10_6)),
% 1.38/0.53    inference(resolution,[],[f220,f56])).
% 1.38/0.53  fof(f56,plain,(
% 1.38/0.53    ( ! [X2,X0,X5,X1] : (~sP0(X0,X1,X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X5)),X0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f31])).
% 1.38/0.53  fof(f31,plain,(
% 1.38/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) | ~r1_orders_2(X1,sK5(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X5)),X0) & r1_orders_2(X1,X5,sK6(X0,X1,X2,X5)) & m1_subset_1(sK6(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 1.38/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f28,f30,f29])).
% 1.38/0.53  fof(f29,plain,(
% 1.38/0.53    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) | ~r1_orders_2(X1,sK5(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))))),
% 1.38/0.53    introduced(choice_axiom,[])).
% 1.38/0.53  fof(f30,plain,(
% 1.38/0.53    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X2,X1,X6),X0) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X5)),X0) & r1_orders_2(X1,X5,sK6(X0,X1,X2,X5)) & m1_subset_1(sK6(X0,X1,X2,X5),u1_struct_0(X1))))),
% 1.38/0.53    introduced(choice_axiom,[])).
% 1.38/0.53  fof(f28,plain,(
% 1.38/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X2,X1,X6),X0) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 1.38/0.53    inference(rectify,[],[f27])).
% 1.38/0.53  fof(f27,plain,(
% 1.38/0.53    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X2,X1,X0)))),
% 1.38/0.53    inference(nnf_transformation,[],[f17])).
% 1.38/0.53  fof(f17,plain,(
% 1.38/0.53    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))))),
% 1.38/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.38/0.53  fof(f220,plain,(
% 1.38/0.53    ( ! [X0] : (sP0(X0,sK4,sK3) | r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0))) ) | (~spl10_4 | ~spl10_6)),
% 1.38/0.53    inference(resolution,[],[f218,f110])).
% 1.38/0.53  fof(f110,plain,(
% 1.38/0.53    ( ! [X1] : (~r2_waybel_0(sK3,sK4,X1) | sP0(X1,sK4,sK3)) ) | ~spl10_4),
% 1.38/0.53    inference(resolution,[],[f104,f52])).
% 1.38/0.53  fof(f52,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (~sP1(X0,X1) | ~r2_waybel_0(X0,X1,X2) | sP0(X2,X1,X0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f26])).
% 1.38/0.53  fof(f26,plain,(
% 1.38/0.53    ! [X0,X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_waybel_0(X0,X1,X2))) | ~sP1(X0,X1))),
% 1.38/0.53    inference(nnf_transformation,[],[f18])).
% 1.38/0.53  fof(f18,plain,(
% 1.38/0.53    ! [X0,X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> sP0(X2,X1,X0)) | ~sP1(X0,X1))),
% 1.38/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.38/0.53  fof(f104,plain,(
% 1.38/0.53    sP1(sK3,sK4) | ~spl10_4),
% 1.38/0.53    inference(avatar_component_clause,[],[f102])).
% 1.38/0.53  fof(f218,plain,(
% 1.38/0.53    ( ! [X0] : (r2_waybel_0(sK3,sK4,X0) | r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0))) ) | ~spl10_6),
% 1.38/0.53    inference(avatar_component_clause,[],[f217])).
% 1.38/0.53  fof(f219,plain,(
% 1.38/0.53    spl10_3 | spl10_6 | ~spl10_5),
% 1.38/0.53    inference(avatar_split_clause,[],[f215,f210,f217,f98])).
% 1.38/0.53  fof(f98,plain,(
% 1.38/0.53    spl10_3 <=> v2_struct_0(sK4)),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.38/0.53  fof(f210,plain,(
% 1.38/0.53    spl10_5 <=> ! [X1,X0] : (r1_waybel_0(sK3,X0,k6_subset_1(u1_struct_0(sK3),X1)) | r2_waybel_0(sK3,X0,X1) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK3))),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.38/0.53  fof(f215,plain,(
% 1.38/0.53    ( ! [X0] : (r2_waybel_0(sK3,sK4,X0) | v2_struct_0(sK4) | r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0))) ) | ~spl10_5),
% 1.38/0.53    inference(resolution,[],[f211,f47])).
% 1.38/0.53  fof(f47,plain,(
% 1.38/0.53    l1_waybel_0(sK4,sK3)),
% 1.38/0.53    inference(cnf_transformation,[],[f24])).
% 1.38/0.53  fof(f211,plain,(
% 1.38/0.53    ( ! [X0,X1] : (~l1_waybel_0(X0,sK3) | r2_waybel_0(sK3,X0,X1) | v2_struct_0(X0) | r1_waybel_0(sK3,X0,k6_subset_1(u1_struct_0(sK3),X1))) ) | ~spl10_5),
% 1.38/0.53    inference(avatar_component_clause,[],[f210])).
% 1.38/0.53  fof(f214,plain,(
% 1.38/0.53    ~spl10_1),
% 1.38/0.53    inference(avatar_contradiction_clause,[],[f213])).
% 1.38/0.53  fof(f213,plain,(
% 1.38/0.53    $false | ~spl10_1),
% 1.38/0.53    inference(resolution,[],[f91,f42])).
% 1.38/0.53  fof(f42,plain,(
% 1.38/0.53    ~v2_struct_0(sK3)),
% 1.38/0.53    inference(cnf_transformation,[],[f24])).
% 1.38/0.53  fof(f91,plain,(
% 1.38/0.53    v2_struct_0(sK3) | ~spl10_1),
% 1.38/0.53    inference(avatar_component_clause,[],[f89])).
% 1.38/0.53  fof(f89,plain,(
% 1.38/0.53    spl10_1 <=> v2_struct_0(sK3)),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.38/0.53  fof(f212,plain,(
% 1.38/0.53    spl10_1 | spl10_5),
% 1.38/0.53    inference(avatar_split_clause,[],[f208,f210,f89])).
% 1.38/0.53  fof(f208,plain,(
% 1.38/0.53    ( ! [X0,X1] : (r1_waybel_0(sK3,X0,k6_subset_1(u1_struct_0(sK3),X1)) | ~l1_waybel_0(X0,sK3) | v2_struct_0(X0) | r2_waybel_0(sK3,X0,X1) | v2_struct_0(sK3)) )),
% 1.38/0.53    inference(resolution,[],[f51,f43])).
% 1.38/0.53  fof(f43,plain,(
% 1.38/0.53    l1_struct_0(sK3)),
% 1.38/0.53    inference(cnf_transformation,[],[f24])).
% 1.38/0.53  fof(f51,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r2_waybel_0(X0,X1,X2) | v2_struct_0(X0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f25])).
% 1.38/0.53  fof(f25,plain,(
% 1.38/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.38/0.53    inference(nnf_transformation,[],[f13])).
% 1.38/0.53  fof(f13,plain,(
% 1.38/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.38/0.53    inference(flattening,[],[f12])).
% 1.38/0.53  fof(f12,plain,(
% 1.38/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.38/0.53    inference(ennf_transformation,[],[f7])).
% 1.38/0.53  fof(f7,axiom,(
% 1.38/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).
% 1.38/0.53  fof(f108,plain,(
% 1.38/0.53    ~spl10_3),
% 1.38/0.53    inference(avatar_contradiction_clause,[],[f107])).
% 1.38/0.53  fof(f107,plain,(
% 1.38/0.53    $false | ~spl10_3),
% 1.38/0.53    inference(resolution,[],[f100,f44])).
% 1.38/0.53  fof(f44,plain,(
% 1.38/0.53    ~v2_struct_0(sK4)),
% 1.38/0.53    inference(cnf_transformation,[],[f24])).
% 1.38/0.53  fof(f100,plain,(
% 1.38/0.53    v2_struct_0(sK4) | ~spl10_3),
% 1.38/0.53    inference(avatar_component_clause,[],[f98])).
% 1.38/0.53  fof(f105,plain,(
% 1.38/0.53    spl10_3 | spl10_4 | ~spl10_2),
% 1.38/0.53    inference(avatar_split_clause,[],[f96,f93,f102,f98])).
% 1.38/0.53  fof(f93,plain,(
% 1.38/0.53    spl10_2 <=> ! [X0] : (~l1_waybel_0(X0,sK3) | sP1(sK3,X0) | v2_struct_0(X0))),
% 1.38/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.38/0.53  fof(f96,plain,(
% 1.38/0.53    sP1(sK3,sK4) | v2_struct_0(sK4) | ~spl10_2),
% 1.38/0.53    inference(resolution,[],[f94,f47])).
% 1.38/0.53  fof(f94,plain,(
% 1.38/0.53    ( ! [X0] : (~l1_waybel_0(X0,sK3) | sP1(sK3,X0) | v2_struct_0(X0)) ) | ~spl10_2),
% 1.38/0.53    inference(avatar_component_clause,[],[f93])).
% 1.38/0.53  fof(f95,plain,(
% 1.38/0.53    spl10_1 | spl10_2),
% 1.38/0.53    inference(avatar_split_clause,[],[f87,f93,f89])).
% 1.38/0.53  fof(f87,plain,(
% 1.38/0.53    ( ! [X0] : (~l1_waybel_0(X0,sK3) | v2_struct_0(X0) | sP1(sK3,X0) | v2_struct_0(sK3)) )),
% 1.38/0.53    inference(resolution,[],[f59,f43])).
% 1.38/0.53  fof(f59,plain,(
% 1.38/0.53    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | sP1(X0,X1) | v2_struct_0(X0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f19])).
% 1.38/0.53  fof(f19,plain,(
% 1.38/0.53    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.38/0.53    inference(definition_folding,[],[f15,f18,f17])).
% 1.38/0.53  fof(f15,plain,(
% 1.38/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.38/0.53    inference(flattening,[],[f14])).
% 1.38/0.53  fof(f14,plain,(
% 1.38/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.38/0.53    inference(ennf_transformation,[],[f6])).
% 1.38/0.53  fof(f6,axiom,(
% 1.38/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).
% 1.38/0.53  % SZS output end Proof for theBenchmark
% 1.38/0.53  % (7196)------------------------------
% 1.38/0.53  % (7196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (7196)Termination reason: Refutation
% 1.38/0.53  
% 1.38/0.53  % (7196)Memory used [KB]: 6396
% 1.38/0.53  % (7196)Time elapsed: 0.118 s
% 1.38/0.53  % (7196)------------------------------
% 1.38/0.53  % (7196)------------------------------
% 1.38/0.53  % (7194)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.54  % (7183)Success in time 0.178 s
%------------------------------------------------------------------------------
