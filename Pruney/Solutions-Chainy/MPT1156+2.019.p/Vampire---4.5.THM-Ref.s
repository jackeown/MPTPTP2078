%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 156 expanded)
%              Number of leaves         :   23 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  332 ( 696 expanded)
%              Number of equality atoms :   61 (  63 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f91,f96,f102,f113,f116,f149,f250])).

fof(f250,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f85,f65,f70,f75,f80,f108,f90,f58,f148,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_orders_2(X2,k2_tarski(X1,X1)))
      | ~ r2_hidden(X0,k2_tarski(X1,X1))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2)
      | ~ v3_orders_2(X2)
      | v2_struct_0(X2)
      | ~ r2_hidden(X1,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f50,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k2_orders_2(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

% (11555)Refutation not found, incomplete strategy% (11555)------------------------------
% (11555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11555)Termination reason: Refutation not found, incomplete strategy

% (11555)Memory used [KB]: 10618
% (11555)Time elapsed: 0.120 s
% (11555)------------------------------
% (11555)------------------------------
fof(f9,axiom,(
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
             => ~ ( r2_hidden(X1,k2_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).

fof(f148,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_12
  <=> r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f58,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f90,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f108,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_9
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f80,plain,
    ( v5_orders_2(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f75,plain,
    ( v4_orders_2(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f70,plain,
    ( v3_orders_2(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f65,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f85,plain,
    ( l1_orders_2(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f149,plain,
    ( spl3_10
    | ~ spl3_6
    | spl3_12
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f132,f93,f146,f88,f110])).

fof(f110,plain,
    ( spl3_10
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f93,plain,
    ( spl3_7
  <=> r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f132,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_7 ),
    inference(superposition,[],[f95,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f51,f54])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f95,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f116,plain,
    ( spl3_1
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl3_1
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f65,f101,f112,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f112,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f101,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f113,plain,
    ( spl3_9
    | spl3_10
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f103,f88,f110,f106])).

fof(f103,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(resolution,[],[f48,f90])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f102,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f97,f83,f99])).

fof(f97,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f53,f85])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f96,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f40,f93])).

fof(f40,plain,(
    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
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
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).

fof(f91,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f39,f88])).

fof(f39,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f38,f83])).

fof(f38,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f37,f78])).

fof(f37,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f36,f73])).

fof(f36,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f35,f68])).

fof(f35,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f34,f63])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:10:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (11542)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (11566)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (11547)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (11566)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (11558)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (11550)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (11546)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (11570)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (11556)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (11555)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f251,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f91,f96,f102,f113,f116,f149,f250])).
% 0.20/0.53  fof(f250,plain,(
% 0.20/0.53    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_12),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f246])).
% 0.20/0.53  fof(f246,plain,(
% 0.20/0.53    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_12)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f85,f65,f70,f75,f80,f108,f90,f58,f148,f173])).
% 0.20/0.53  fof(f173,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_orders_2(X2,k2_tarski(X1,X1))) | ~r2_hidden(X0,k2_tarski(X1,X1)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~l1_orders_2(X2) | ~v5_orders_2(X2) | ~v4_orders_2(X2) | ~v3_orders_2(X2) | v2_struct_0(X2) | ~r2_hidden(X1,u1_struct_0(X2))) )),
% 0.20/0.53    inference(resolution,[],[f50,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f49,f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,k2_orders_2(X0,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  % (11555)Refutation not found, incomplete strategy% (11555)------------------------------
% 0.20/0.53  % (11555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11555)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11555)Memory used [KB]: 10618
% 0.20/0.53  % (11555)Time elapsed: 0.120 s
% 0.20/0.53  % (11555)------------------------------
% 0.20/0.53  % (11555)------------------------------
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).
% 0.20/0.53  fof(f148,plain,(
% 0.20/0.53    r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK1,sK1))) | ~spl3_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f146])).
% 0.20/0.53  fof(f146,plain,(
% 0.20/0.53    spl3_12 <=> r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.20/0.53    inference(equality_resolution,[],[f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.20/0.53    inference(equality_resolution,[],[f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(rectify,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(flattening,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    spl3_6 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl3_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f106])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    spl3_9 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    v5_orders_2(sK0) | ~spl3_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f78])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    spl3_4 <=> v5_orders_2(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    v4_orders_2(sK0) | ~spl3_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    spl3_3 <=> v4_orders_2(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    v3_orders_2(sK0) | ~spl3_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    spl3_2 <=> v3_orders_2(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ~v2_struct_0(sK0) | spl3_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    spl3_1 <=> v2_struct_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    l1_orders_2(sK0) | ~spl3_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f83])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    spl3_5 <=> l1_orders_2(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.53  fof(f149,plain,(
% 0.20/0.53    spl3_10 | ~spl3_6 | spl3_12 | ~spl3_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f132,f93,f146,f88,f110])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    spl3_10 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    spl3_7 <=> r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl3_7),
% 0.20/0.53    inference(superposition,[],[f95,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f51,f54])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.53    inference(flattening,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~spl3_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f93])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    spl3_1 | ~spl3_8 | ~spl3_10),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f114])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    $false | (spl3_1 | ~spl3_8 | ~spl3_10)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f65,f101,f112,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    v1_xboole_0(u1_struct_0(sK0)) | ~spl3_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f110])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    l1_struct_0(sK0) | ~spl3_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f99])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    spl3_8 <=> l1_struct_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    spl3_9 | spl3_10 | ~spl3_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f103,f88,f110,f106])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 0.20/0.53    inference(resolution,[],[f48,f90])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    spl3_8 | ~spl3_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f97,f83,f99])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    l1_struct_0(sK0) | ~spl3_5),
% 0.20/0.53    inference(resolution,[],[f53,f85])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    spl3_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f40,f93])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f27,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ? [X1] : (r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X1,u1_struct_0(sK0))) => (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.20/0.53    inference(negated_conjecture,[],[f10])).
% 0.20/0.53  fof(f10,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    spl3_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f39,f88])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    spl3_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f38,f83])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    l1_orders_2(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    spl3_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f37,f78])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    v5_orders_2(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    spl3_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f36,f73])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    v4_orders_2(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    spl3_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f35,f68])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    v3_orders_2(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ~spl3_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f34,f63])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (11566)------------------------------
% 0.20/0.53  % (11566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11566)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (11566)Memory used [KB]: 10874
% 0.20/0.53  % (11566)Time elapsed: 0.116 s
% 0.20/0.53  % (11566)------------------------------
% 0.20/0.53  % (11566)------------------------------
% 0.20/0.54  % (11541)Success in time 0.171 s
%------------------------------------------------------------------------------
