%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2044+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:04 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 287 expanded)
%              Number of leaves         :   12 ( 102 expanded)
%              Depth                    :   22
%              Number of atoms          :  375 (1804 expanded)
%              Number of equality atoms :   18 (  49 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f88,f92,f95,f151,f178])).

fof(f178,plain,
    ( spl5_2
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f176,f20])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ m1_connsp_2(sK2,sK0,sK1)
      | ~ r2_hidden(sK2,k1_yellow19(sK0,sK1)) )
    & ( m1_connsp_2(sK2,sK0,sK1)
      | r2_hidden(sK2,k1_yellow19(sK0,sK1)) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X2,k1_yellow19(X0,X1)) )
                & ( m1_connsp_2(X2,X0,X1)
                  | r2_hidden(X2,k1_yellow19(X0,X1)) ) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,sK0,X1)
                | ~ r2_hidden(X2,k1_yellow19(sK0,X1)) )
              & ( m1_connsp_2(X2,sK0,X1)
                | r2_hidden(X2,k1_yellow19(sK0,X1)) ) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_connsp_2(X2,sK0,X1)
              | ~ r2_hidden(X2,k1_yellow19(sK0,X1)) )
            & ( m1_connsp_2(X2,sK0,X1)
              | r2_hidden(X2,k1_yellow19(sK0,X1)) ) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ m1_connsp_2(X2,sK0,sK1)
            | ~ r2_hidden(X2,k1_yellow19(sK0,sK1)) )
          & ( m1_connsp_2(X2,sK0,sK1)
            | r2_hidden(X2,k1_yellow19(sK0,sK1)) ) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ( ~ m1_connsp_2(X2,sK0,sK1)
          | ~ r2_hidden(X2,k1_yellow19(sK0,sK1)) )
        & ( m1_connsp_2(X2,sK0,sK1)
          | r2_hidden(X2,k1_yellow19(sK0,sK1)) ) )
   => ( ( ~ m1_connsp_2(sK2,sK0,sK1)
        | ~ r2_hidden(sK2,k1_yellow19(sK0,sK1)) )
      & ( m1_connsp_2(sK2,sK0,sK1)
        | r2_hidden(sK2,k1_yellow19(sK0,sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ r2_hidden(X2,k1_yellow19(X0,X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | r2_hidden(X2,k1_yellow19(X0,X1)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <~> m1_connsp_2(X2,X0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <~> m1_connsp_2(X2,X0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( r2_hidden(X2,k1_yellow19(X0,X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow19)).

fof(f176,plain,
    ( v2_struct_0(sK0)
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f175,f21])).

fof(f21,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f175,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f174,f22])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f174,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f173,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f173,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f172,f142])).

fof(f142,plain,
    ( r2_hidden(sK2,a_2_0_yellow19(sK0,sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl5_5
  <=> r2_hidden(sK2,a_2_0_yellow19(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f172,plain,
    ( ~ r2_hidden(sK2,a_2_0_yellow19(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,
    ( ~ r2_hidden(sK2,a_2_0_yellow19(sK0,sK1))
    | ~ r2_hidden(sK2,a_2_0_yellow19(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(resolution,[],[f166,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_proxy_replacement,[],[f28,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
          | ! [X3] :
              ( X0 != X3
              | ~ m1_connsp_2(X3,X1,X2) ) )
        & ( ( sK3(X0,X1,X2) = X0
            & m1_connsp_2(sK3(X0,X1,X2),X1,X2) )
          | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

% (8222)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( X0 = X4
          & m1_connsp_2(X4,X1,X2) )
     => ( sK3(X0,X1,X2) = X0
        & m1_connsp_2(sK3(X0,X1,X2),X1,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
          | ! [X3] :
              ( X0 != X3
              | ~ m1_connsp_2(X3,X1,X2) ) )
        & ( ? [X4] :
              ( X0 = X4
              & m1_connsp_2(X4,X1,X2) )
          | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
          | ! [X3] :
              ( X0 != X3
              | ~ m1_connsp_2(X3,X1,X2) ) )
        & ( ? [X3] :
              ( X0 = X3
              & m1_connsp_2(X3,X1,X2) )
          | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      <=> ? [X3] :
            ( X0 = X3
            & m1_connsp_2(X3,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      <=> ? [X3] :
            ( X0 = X3
            & m1_connsp_2(X3,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      <=> ? [X3] :
            ( X0 = X3
            & m1_connsp_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow19)).

fof(f166,plain,
    ( ! [X0] :
        ( ~ sQ4_eqProxy(sK3(X0,sK0,sK1),sK2)
        | ~ r2_hidden(X0,a_2_0_yellow19(sK0,sK1)) )
    | spl5_2 ),
    inference(subsumption_resolution,[],[f138,f44])).

fof(f44,plain,(
    ! [X0] : sQ4_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f31])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_0_yellow19(sK0,sK1))
        | ~ sQ4_eqProxy(sK3(X0,sK0,sK1),sK2)
        | ~ sQ4_eqProxy(sK1,sK1) )
    | spl5_2 ),
    inference(resolution,[],[f128,f23])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,a_2_0_yellow19(sK0,X1))
        | ~ sQ4_eqProxy(sK3(X0,sK0,X1),sK2)
        | ~ sQ4_eqProxy(X1,sK1) )
    | spl5_2 ),
    inference(subsumption_resolution,[],[f127,f20])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ sQ4_eqProxy(sK3(X0,sK0,X1),sK2)
        | ~ r2_hidden(X0,a_2_0_yellow19(sK0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ sQ4_eqProxy(X1,sK1)
        | v2_struct_0(sK0) )
    | spl5_2 ),
    inference(subsumption_resolution,[],[f126,f21])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ sQ4_eqProxy(sK3(X0,sK0,X1),sK2)
        | ~ r2_hidden(X0,a_2_0_yellow19(sK0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ sQ4_eqProxy(X1,sK1)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_2 ),
    inference(subsumption_resolution,[],[f124,f44])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ sQ4_eqProxy(sK0,sK0)
        | ~ sQ4_eqProxy(sK3(X0,sK0,X1),sK2)
        | ~ r2_hidden(X0,a_2_0_yellow19(sK0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ sQ4_eqProxy(X1,sK1)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_2 ),
    inference(resolution,[],[f116,f22])).

fof(f116,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ sQ4_eqProxy(X1,sK0)
        | ~ sQ4_eqProxy(sK3(X2,X1,X0),sK2)
        | ~ r2_hidden(X2,a_2_0_yellow19(X1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ sQ4_eqProxy(X0,sK1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl5_2 ),
    inference(resolution,[],[f97,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK3(X0,X1,X2),X1,X2)
      | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f97,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_connsp_2(X2,X0,X1)
        | ~ sQ4_eqProxy(X1,sK1)
        | ~ sQ4_eqProxy(X0,sK0)
        | ~ sQ4_eqProxy(X2,sK2) )
    | spl5_2 ),
    inference(resolution,[],[f43,f53])).

fof(f53,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl5_2
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_connsp_2(X1,X3,X5)
      | ~ sQ4_eqProxy(X2,X3)
      | ~ sQ4_eqProxy(X4,X5)
      | ~ m1_connsp_2(X0,X2,X4)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f31])).

fof(f151,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f44,f50,f73,f143,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ sQ4_eqProxy(X2,X3)
      | ~ r2_hidden(X0,X2)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f31])).

fof(f143,plain,
    ( ~ r2_hidden(sK2,a_2_0_yellow19(sK0,sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f141])).

fof(f73,plain,
    ( sQ4_eqProxy(k1_yellow19(sK0,sK1),a_2_0_yellow19(sK0,sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_3
  <=> sQ4_eqProxy(k1_yellow19(sK0,sK1),a_2_0_yellow19(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f50,plain,
    ( r2_hidden(sK2,k1_yellow19(sK0,sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl5_1
  <=> r2_hidden(sK2,k1_yellow19(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f95,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f93,f50])).

fof(f93,plain,
    ( ~ r2_hidden(sK2,k1_yellow19(sK0,sK1))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f25,f54])).

fof(f54,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f25,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ r2_hidden(sK2,k1_yellow19(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f92,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f22,f20,f21,f44,f54,f23,f73,f64])).

fof(f64,plain,
    ( ! [X6,X4,X5] :
        ( ~ l1_pre_topc(X5)
        | ~ m1_connsp_2(X4,X5,X6)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ sQ4_eqProxy(X4,sK2)
        | ~ v2_pre_topc(X5)
        | v2_struct_0(X5)
        | ~ sQ4_eqProxy(k1_yellow19(sK0,sK1),a_2_0_yellow19(X5,X6)) )
    | spl5_1 ),
    inference(resolution,[],[f57,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X1,X0)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f31])).

fof(f57,plain,
    ( ! [X2,X0,X1] :
        ( ~ sQ4_eqProxy(a_2_0_yellow19(X0,X1),k1_yellow19(sK0,sK1))
        | ~ sQ4_eqProxy(X2,sK2)
        | ~ m1_connsp_2(X2,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl5_1 ),
    inference(resolution,[],[f56,f30])).

fof(f30,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_yellow19(X1,X2))
      | ~ m1_connsp_2(X3,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      | X0 != X3
      | ~ m1_connsp_2(X3,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ sQ4_eqProxy(X0,k1_yellow19(sK0,sK1))
        | ~ sQ4_eqProxy(X1,sK2) )
    | spl5_1 ),
    inference(resolution,[],[f42,f49])).

fof(f49,plain,
    ( ~ r2_hidden(sK2,k1_yellow19(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f88,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f86,f20])).

fof(f86,plain,
    ( v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f85,f21])).

fof(f85,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f84,f22])).

fof(f84,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f80,f23])).

fof(f80,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(resolution,[],[f74,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(k1_yellow19(X0,X1),a_2_0_yellow19(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f26,f31])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow19)).

fof(f74,plain,
    ( ~ sQ4_eqProxy(k1_yellow19(sK0,sK1),a_2_0_yellow19(sK0,sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f55,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f24,f52,f48])).

fof(f24,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | r2_hidden(sK2,k1_yellow19(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

%------------------------------------------------------------------------------
