%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 214 expanded)
%              Number of leaves         :   26 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  397 (1002 expanded)
%              Number of equality atoms :   62 (  67 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f224,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f165,f167,f169,f171,f182,f188,f192,f193,f202,f205,f223])).

fof(f223,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | ~ spl5_2
    | spl5_3 ),
    inference(resolution,[],[f213,f71])).

fof(f71,plain,(
    ! [X4,X2,X3,X1] : sP0(X1,X1,X2,X3,X4) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X5,X3,X2,X1,X0] :
      ( ( sP0(X5,X3,X2,X1,X0)
        | ( X3 != X5
          & X2 != X5
          & X1 != X5
          & X0 != X5 ) )
      & ( X3 = X5
        | X2 = X5
        | X1 = X5
        | X0 = X5
        | ~ sP0(X5,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X5,X3,X2,X1,X0] :
      ( ( sP0(X5,X3,X2,X1,X0)
        | ( X3 != X5
          & X2 != X5
          & X1 != X5
          & X0 != X5 ) )
      & ( X3 = X5
        | X2 = X5
        | X1 = X5
        | X0 = X5
        | ~ sP0(X5,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X5,X3,X2,X1,X0] :
      ( sP0(X5,X3,X2,X1,X0)
    <=> ( X3 = X5
        | X2 = X5
        | X1 = X5
        | X0 = X5 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f213,plain,
    ( ~ sP0(sK3,sK3,sK3,sK3,sK3)
    | ~ spl5_2
    | spl5_3 ),
    inference(resolution,[],[f206,f97])).

fof(f97,plain,
    ( sP1(sK3,sK3,sK3,sK3,k6_domain_1(u1_struct_0(sK2),sK3))
    | ~ spl5_2 ),
    inference(superposition,[],[f75,f95])).

fof(f95,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_enumset1(sK3,sK3,sK3,sK3)
    | ~ spl5_2 ),
    inference(resolution,[],[f93,f46])).

fof(f46,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( r2_hidden(sK3,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f31,f30])).

fof(f30,plain,
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
          ( r2_hidden(X1,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1)))
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( r2_hidden(X1,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1)))
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( r2_hidden(sK3,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_orders_2)).

fof(f93,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | k2_enumset1(X0,X0,X0,X0) = k6_domain_1(u1_struct_0(sK2),X0) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_2
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | k2_enumset1(X0,X0,X0,X0) = k6_domain_1(u1_struct_0(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : sP1(X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP1(X0,X1,X2,X3,X4) )
      & ( sP1(X0,X1,X2,X3,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP1(X0,X1,X2,X3,X4) ) ),
    inference(definition_folding,[],[f26,f28,f27])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP1(X0,X1,X2,X3,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> sP0(X5,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(f206,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ sP1(X3,X2,X1,X0,k6_domain_1(u1_struct_0(sK2),sK3))
        | ~ sP0(sK3,X0,X1,X2,X3) )
    | spl5_3 ),
    inference(resolution,[],[f121,f58])).

% (9292)Termination reason: Refutation not found, incomplete strategy
fof(f58,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | ~ sP0(X6,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f36])).

% (9292)Memory used [KB]: 10746
% (9292)Time elapsed: 0.131 s
% (9292)------------------------------
% (9292)------------------------------
fof(f36,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ( ( ~ sP0(sK4(X0,X1,X2,X3,X4),X3,X2,X1,X0)
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4),X4) )
          & ( sP0(sK4(X0,X1,X2,X3,X4),X3,X2,X1,X0)
            | r2_hidden(sK4(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ~ sP0(X6,X3,X2,X1,X0) )
            & ( sP0(X6,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ sP0(X5,X3,X2,X1,X0)
            | ~ r2_hidden(X5,X4) )
          & ( sP0(X5,X3,X2,X1,X0)
            | r2_hidden(X5,X4) ) )
     => ( ( ~ sP0(sK4(X0,X1,X2,X3,X4),X3,X2,X1,X0)
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4),X4) )
        & ( sP0(sK4(X0,X1,X2,X3,X4),X3,X2,X1,X0)
          | r2_hidden(sK4(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ~ sP0(X5,X3,X2,X1,X0)
              | ~ r2_hidden(X5,X4) )
            & ( sP0(X5,X3,X2,X1,X0)
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ~ sP0(X6,X3,X2,X1,X0) )
            & ( sP0(X6,X3,X2,X1,X0)
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP1(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ~ sP0(X5,X3,X2,X1,X0)
              | ~ r2_hidden(X5,X4) )
            & ( sP0(X5,X3,X2,X1,X0)
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ~ sP0(X5,X3,X2,X1,X0) )
            & ( sP0(X5,X3,X2,X1,X0)
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP1(X0,X1,X2,X3,X4) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f121,plain,
    ( ~ r2_hidden(sK3,k6_domain_1(u1_struct_0(sK2),sK3))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl5_3
  <=> r2_hidden(sK3,k6_domain_1(u1_struct_0(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f205,plain,(
    spl5_13 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl5_13 ),
    inference(resolution,[],[f201,f47])).

fof(f47,plain,(
    r2_hidden(sK3,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) ),
    inference(cnf_transformation,[],[f32])).

fof(f201,plain,
    ( ~ r2_hidden(sK3,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl5_13
  <=> r2_hidden(sK3,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f202,plain,
    ( ~ spl5_13
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f197,f178,f119,f199])).

fof(f178,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK2),X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f197,plain,
    ( ~ r2_hidden(sK3,k6_domain_1(u1_struct_0(sK2),sK3))
    | ~ r2_hidden(sK3,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
    | ~ spl5_11 ),
    inference(resolution,[],[f196,f46])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK2),sK3))
        | ~ r2_hidden(X0,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) )
    | ~ spl5_11 ),
    inference(resolution,[],[f179,f46])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r2_hidden(X0,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1)))
        | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK2),X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f178])).

fof(f193,plain,
    ( spl5_10
    | spl5_11
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f190,f163,f178,f174])).

fof(f174,plain,
    ( spl5_10
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f163,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_orders_2(sK2,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK2),X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | v1_xboole_0(u1_struct_0(sK2)) )
    | ~ spl5_9 ),
    inference(resolution,[],[f164,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(X0,k1_orders_2(sK2,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f163])).

fof(f192,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl5_12 ),
    inference(resolution,[],[f189,f45])).

fof(f45,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f189,plain,
    ( ~ l1_orders_2(sK2)
    | spl5_12 ),
    inference(resolution,[],[f187,f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f187,plain,
    ( ~ l1_struct_0(sK2)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl5_12
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f188,plain,
    ( spl5_1
    | ~ spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f183,f174,f185,f88])).

fof(f88,plain,
    ( spl5_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f183,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl5_10 ),
    inference(resolution,[],[f176,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f176,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f174])).

fof(f182,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl5_1 ),
    inference(resolution,[],[f90,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,
    ( v2_struct_0(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f171,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl5_8 ),
    inference(resolution,[],[f161,f45])).

fof(f161,plain,
    ( ~ l1_orders_2(sK2)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl5_8
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f169,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl5_7 ),
    inference(resolution,[],[f157,f43])).

fof(f43,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f157,plain,
    ( ~ v4_orders_2(sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl5_7
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f167,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl5_6 ),
    inference(resolution,[],[f153,f42])).

fof(f42,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f153,plain,
    ( ~ v3_orders_2(sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl5_6
  <=> v3_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f165,plain,
    ( spl5_1
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f149,f163,f159,f155,f151,f88])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ r2_hidden(X0,k1_orders_2(sK2,X1))
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f50,f44])).

fof(f44,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f32])).

% (9289)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f50,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).

fof(f94,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f86,f92,f88])).

fof(f86,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | v2_struct_0(sK2)
      | k2_enumset1(X0,X0,X0,X0) = k6_domain_1(u1_struct_0(sK2),X0) ) ),
    inference(resolution,[],[f85,f45])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | k2_enumset1(X0,X0,X0,X0) = k6_domain_1(u1_struct_0(X1),X0) ) ),
    inference(resolution,[],[f78,f49])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | k2_enumset1(X0,X0,X0,X0) = k6_domain_1(u1_struct_0(X1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f70,f51])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_enumset1(X1,X1,X1,X1) ) ),
    inference(definition_unfolding,[],[f53,f69])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:04:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.53  % (9284)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (9272)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (9293)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (9292)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (9284)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (9297)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (9277)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (9292)Refutation not found, incomplete strategy% (9292)------------------------------
% 0.21/0.55  % (9292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f224,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f94,f165,f167,f169,f171,f182,f188,f192,f193,f202,f205,f223])).
% 0.21/0.55  fof(f223,plain,(
% 0.21/0.55    ~spl5_2 | spl5_3),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f215])).
% 0.21/0.55  fof(f215,plain,(
% 0.21/0.55    $false | (~spl5_2 | spl5_3)),
% 0.21/0.55    inference(resolution,[],[f213,f71])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X4,X2,X3,X1] : (sP0(X1,X1,X2,X3,X4)) )),
% 0.21/0.55    inference(equality_resolution,[],[f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | X0 != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | ~sP0(X0,X1,X2,X3,X4)))),
% 0.21/0.55    inference(rectify,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ! [X5,X3,X2,X1,X0] : ((sP0(X5,X3,X2,X1,X0) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~sP0(X5,X3,X2,X1,X0)))),
% 0.21/0.55    inference(flattening,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X5,X3,X2,X1,X0] : ((sP0(X5,X3,X2,X1,X0) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~sP0(X5,X3,X2,X1,X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X5,X3,X2,X1,X0] : (sP0(X5,X3,X2,X1,X0) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.55  fof(f213,plain,(
% 0.21/0.55    ~sP0(sK3,sK3,sK3,sK3,sK3) | (~spl5_2 | spl5_3)),
% 0.21/0.55    inference(resolution,[],[f206,f97])).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    sP1(sK3,sK3,sK3,sK3,k6_domain_1(u1_struct_0(sK2),sK3)) | ~spl5_2),
% 0.21/0.55    inference(superposition,[],[f75,f95])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    k6_domain_1(u1_struct_0(sK2),sK3) = k2_enumset1(sK3,sK3,sK3,sK3) | ~spl5_2),
% 0.21/0.55    inference(resolution,[],[f93,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    (r2_hidden(sK3,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f31,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ? [X1] : (r2_hidden(X1,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1))) & m1_subset_1(X1,u1_struct_0(sK2))) => (r2_hidden(sK3,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.21/0.55    inference(negated_conjecture,[],[f11])).
% 0.21/0.55  fof(f11,conjecture,(
% 0.21/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_orders_2)).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | k2_enumset1(X0,X0,X0,X0) = k6_domain_1(u1_struct_0(sK2),X0)) ) | ~spl5_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f92])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    spl5_2 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | k2_enumset1(X0,X0,X0,X0) = k6_domain_1(u1_struct_0(sK2),X0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3))) )),
% 0.21/0.55    inference(equality_resolution,[],[f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X1,X2,X3,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.21/0.55    inference(cnf_transformation,[],[f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ~sP1(X0,X1,X2,X3,X4)) & (sP1(X0,X1,X2,X3,X4) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.21/0.55    inference(nnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> sP1(X0,X1,X2,X3,X4))),
% 0.21/0.55    inference(definition_folding,[],[f26,f28,f27])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : (sP1(X0,X1,X2,X3,X4) <=> ! [X5] : (r2_hidden(X5,X4) <=> sP0(X5,X3,X2,X1,X0)))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).
% 0.21/0.55  fof(f206,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~sP1(X3,X2,X1,X0,k6_domain_1(u1_struct_0(sK2),sK3)) | ~sP0(sK3,X0,X1,X2,X3)) ) | spl5_3),
% 0.21/0.55    inference(resolution,[],[f121,f58])).
% 0.21/0.55  % (9292)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | ~sP0(X6,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  
% 0.21/0.55  % (9292)Memory used [KB]: 10746
% 0.21/0.55  % (9292)Time elapsed: 0.131 s
% 0.21/0.55  % (9292)------------------------------
% 0.21/0.55  % (9292)------------------------------
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ((~sP0(sK4(X0,X1,X2,X3,X4),X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4),X4)) & (sP0(sK4(X0,X1,X2,X3,X4),X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | ~sP0(X6,X3,X2,X1,X0)) & (sP0(X6,X3,X2,X1,X0) | ~r2_hidden(X6,X4))) | ~sP1(X0,X1,X2,X3,X4)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X4,X3,X2,X1,X0] : (? [X5] : ((~sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP0(X5,X3,X2,X1,X0) | r2_hidden(X5,X4))) => ((~sP0(sK4(X0,X1,X2,X3,X4),X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4),X4)) & (sP0(sK4(X0,X1,X2,X3,X4),X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4),X4))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ? [X5] : ((~sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP0(X5,X3,X2,X1,X0) | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | ~sP0(X6,X3,X2,X1,X0)) & (sP0(X6,X3,X2,X1,X0) | ~r2_hidden(X6,X4))) | ~sP1(X0,X1,X2,X3,X4)))),
% 0.21/0.55    inference(rectify,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ? [X5] : ((~sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4)) & (sP0(X5,X3,X2,X1,X0) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | ~sP0(X5,X3,X2,X1,X0)) & (sP0(X5,X3,X2,X1,X0) | ~r2_hidden(X5,X4))) | ~sP1(X0,X1,X2,X3,X4)))),
% 0.21/0.55    inference(nnf_transformation,[],[f28])).
% 0.21/0.55  fof(f121,plain,(
% 0.21/0.55    ~r2_hidden(sK3,k6_domain_1(u1_struct_0(sK2),sK3)) | spl5_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f119])).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    spl5_3 <=> r2_hidden(sK3,k6_domain_1(u1_struct_0(sK2),sK3))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.55  fof(f205,plain,(
% 0.21/0.55    spl5_13),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f203])).
% 0.21/0.55  fof(f203,plain,(
% 0.21/0.55    $false | spl5_13),
% 0.21/0.55    inference(resolution,[],[f201,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    r2_hidden(sK3,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f201,plain,(
% 0.21/0.55    ~r2_hidden(sK3,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) | spl5_13),
% 0.21/0.55    inference(avatar_component_clause,[],[f199])).
% 0.21/0.55  fof(f199,plain,(
% 0.21/0.55    spl5_13 <=> r2_hidden(sK3,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.55  fof(f202,plain,(
% 0.21/0.55    ~spl5_13 | ~spl5_3 | ~spl5_11),
% 0.21/0.55    inference(avatar_split_clause,[],[f197,f178,f119,f199])).
% 0.21/0.55  fof(f178,plain,(
% 0.21/0.55    spl5_11 <=> ! [X1,X0] : (~r2_hidden(X0,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1))) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r2_hidden(X0,k6_domain_1(u1_struct_0(sK2),X1)) | ~m1_subset_1(X0,u1_struct_0(sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.55  fof(f197,plain,(
% 0.21/0.55    ~r2_hidden(sK3,k6_domain_1(u1_struct_0(sK2),sK3)) | ~r2_hidden(sK3,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) | ~spl5_11),
% 0.21/0.55    inference(resolution,[],[f196,f46])).
% 0.21/0.55  fof(f196,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,k6_domain_1(u1_struct_0(sK2),sK3)) | ~r2_hidden(X0,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))) ) | ~spl5_11),
% 0.21/0.55    inference(resolution,[],[f179,f46])).
% 0.21/0.55  fof(f179,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK2)) | ~r2_hidden(X0,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1))) | ~r2_hidden(X0,k6_domain_1(u1_struct_0(sK2),X1)) | ~m1_subset_1(X0,u1_struct_0(sK2))) ) | ~spl5_11),
% 0.21/0.55    inference(avatar_component_clause,[],[f178])).
% 0.21/0.55  fof(f193,plain,(
% 0.21/0.55    spl5_10 | spl5_11 | ~spl5_9),
% 0.21/0.55    inference(avatar_split_clause,[],[f190,f163,f178,f174])).
% 0.21/0.55  fof(f174,plain,(
% 0.21/0.55    spl5_10 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.55  fof(f163,plain,(
% 0.21/0.55    spl5_9 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_orders_2(sK2,X1)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.55  fof(f190,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,k6_domain_1(u1_struct_0(sK2),X1)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))) ) | ~spl5_9),
% 0.21/0.55    inference(resolution,[],[f164,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.55  fof(f164,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X0,k1_orders_2(sK2,X1)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,X1)) ) | ~spl5_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f163])).
% 0.21/0.55  fof(f192,plain,(
% 0.21/0.55    spl5_12),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f191])).
% 0.21/0.55  fof(f191,plain,(
% 0.21/0.55    $false | spl5_12),
% 0.21/0.55    inference(resolution,[],[f189,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    l1_orders_2(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f189,plain,(
% 0.21/0.55    ~l1_orders_2(sK2) | spl5_12),
% 0.21/0.55    inference(resolution,[],[f187,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.55  fof(f187,plain,(
% 0.21/0.55    ~l1_struct_0(sK2) | spl5_12),
% 0.21/0.55    inference(avatar_component_clause,[],[f185])).
% 0.21/0.55  fof(f185,plain,(
% 0.21/0.55    spl5_12 <=> l1_struct_0(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    spl5_1 | ~spl5_12 | ~spl5_10),
% 0.21/0.55    inference(avatar_split_clause,[],[f183,f174,f185,f88])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    spl5_1 <=> v2_struct_0(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.55  fof(f183,plain,(
% 0.21/0.55    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl5_10),
% 0.21/0.55    inference(resolution,[],[f176,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.55  fof(f176,plain,(
% 0.21/0.55    v1_xboole_0(u1_struct_0(sK2)) | ~spl5_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f174])).
% 0.21/0.55  fof(f182,plain,(
% 0.21/0.55    ~spl5_1),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f181])).
% 0.21/0.55  fof(f181,plain,(
% 0.21/0.55    $false | ~spl5_1),
% 0.21/0.55    inference(resolution,[],[f90,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ~v2_struct_0(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    v2_struct_0(sK2) | ~spl5_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f88])).
% 0.21/0.55  fof(f171,plain,(
% 0.21/0.55    spl5_8),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f170])).
% 0.21/0.55  fof(f170,plain,(
% 0.21/0.55    $false | spl5_8),
% 0.21/0.55    inference(resolution,[],[f161,f45])).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    ~l1_orders_2(sK2) | spl5_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f159])).
% 0.21/0.55  fof(f159,plain,(
% 0.21/0.55    spl5_8 <=> l1_orders_2(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.55  fof(f169,plain,(
% 0.21/0.55    spl5_7),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f168])).
% 0.21/0.55  fof(f168,plain,(
% 0.21/0.55    $false | spl5_7),
% 0.21/0.55    inference(resolution,[],[f157,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    v4_orders_2(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f157,plain,(
% 0.21/0.55    ~v4_orders_2(sK2) | spl5_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f155])).
% 0.21/0.55  fof(f155,plain,(
% 0.21/0.55    spl5_7 <=> v4_orders_2(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.55  fof(f167,plain,(
% 0.21/0.55    spl5_6),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f166])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    $false | spl5_6),
% 0.21/0.55    inference(resolution,[],[f153,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    v3_orders_2(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f153,plain,(
% 0.21/0.55    ~v3_orders_2(sK2) | spl5_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f151])).
% 0.21/0.55  fof(f151,plain,(
% 0.21/0.55    spl5_6 <=> v3_orders_2(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.55  fof(f165,plain,(
% 0.21/0.55    spl5_1 | ~spl5_6 | ~spl5_7 | ~spl5_8 | spl5_9),
% 0.21/0.55    inference(avatar_split_clause,[],[f149,f163,f159,f155,f151,f88])).
% 0.21/0.55  fof(f149,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~r2_hidden(X0,k1_orders_2(sK2,X1)) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.55    inference(resolution,[],[f50,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    v5_orders_2(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  % (9289)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X1,k1_orders_2(X0,X2)) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    spl5_1 | spl5_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f86,f92,f88])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | v2_struct_0(sK2) | k2_enumset1(X0,X0,X0,X0) = k6_domain_1(u1_struct_0(sK2),X0)) )),
% 0.21/0.55    inference(resolution,[],[f85,f45])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | k2_enumset1(X0,X0,X0,X0) = k6_domain_1(u1_struct_0(X1),X0)) )),
% 0.21/0.55    inference(resolution,[],[f78,f49])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_struct_0(X1) | k2_enumset1(X0,X0,X0,X0) = k6_domain_1(u1_struct_0(X1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1)) )),
% 0.21/0.55    inference(resolution,[],[f70,f51])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_enumset1(X1,X1,X1,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f53,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f48,f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f52,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.55    inference(flattening,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (9284)------------------------------
% 0.21/0.55  % (9284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9284)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (9284)Memory used [KB]: 6268
% 0.21/0.55  % (9284)Time elapsed: 0.123 s
% 0.21/0.55  % (9284)------------------------------
% 0.21/0.55  % (9284)------------------------------
% 0.21/0.55  % (9275)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (9289)Refutation not found, incomplete strategy% (9289)------------------------------
% 0.21/0.55  % (9289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9289)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9289)Memory used [KB]: 10618
% 0.21/0.55  % (9289)Time elapsed: 0.145 s
% 0.21/0.55  % (9289)------------------------------
% 0.21/0.55  % (9289)------------------------------
% 0.21/0.55  % (9271)Success in time 0.195 s
%------------------------------------------------------------------------------
