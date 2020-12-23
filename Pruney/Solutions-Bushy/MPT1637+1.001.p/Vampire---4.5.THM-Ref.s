%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1637+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 387 expanded)
%              Number of leaves         :   39 ( 167 expanded)
%              Depth                    :   14
%              Number of atoms          :  758 (1768 expanded)
%              Number of equality atoms :   91 ( 178 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (30837)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f415,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f76,f81,f86,f96,f98,f109,f118,f123,f139,f157,f171,f176,f191,f195,f204,f244,f256,f274,f278,f283,f308,f335,f371,f394,f414])).

fof(f414,plain,
    ( ~ spl6_5
    | spl6_6
    | ~ spl6_29
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | ~ spl6_5
    | spl6_6
    | ~ spl6_29
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f407,f94])).

fof(f94,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_6
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f407,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl6_5
    | ~ spl6_29
    | ~ spl6_36 ),
    inference(backward_demodulation,[],[f334,f399])).

fof(f399,plain,
    ( sK1 = sK5(sK2,sK0,k1_tarski(sK1))
    | ~ spl6_5
    | ~ spl6_36 ),
    inference(resolution,[],[f393,f91])).

fof(f91,plain,
    ( r2_hidden(sK2,k5_waybel_0(sK0,sK1))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_5
  <=> r2_hidden(sK2,k5_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f393,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_waybel_0(sK0,sK1))
        | sK1 = sK5(X1,sK0,k1_tarski(sK1)) )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl6_36
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k5_waybel_0(sK0,sK1))
        | sK1 = sK5(X1,sK0,k1_tarski(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f334,plain,
    ( r1_orders_2(sK0,sK2,sK5(sK2,sK0,k1_tarski(sK1)))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl6_29
  <=> r1_orders_2(sK0,sK2,sK5(sK2,sK0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f394,plain,
    ( spl6_36
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f386,f369,f392])).

fof(f369,plain,
    ( spl6_34
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k5_waybel_0(sK0,sK1))
        | r2_hidden(sK5(X0,sK0,k1_tarski(sK1)),k1_tarski(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f386,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_waybel_0(sK0,sK1))
        | sK1 = sK5(X1,sK0,k1_tarski(sK1)) )
    | ~ spl6_34 ),
    inference(resolution,[],[f370,f65])).

fof(f65,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f370,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(X0,sK0,k1_tarski(sK1)),k1_tarski(sK1))
        | ~ r2_hidden(X0,k5_waybel_0(sK0,sK1)) )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f369])).

fof(f371,plain,
    ( spl6_34
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f262,f253,f202,f136,f369])).

fof(f136,plain,
    ( spl6_10
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f202,plain,
    ( spl6_19
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,a_2_0_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK5(X0,sK0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f253,plain,
    ( spl6_22
  <=> k5_waybel_0(sK0,sK1) = a_2_0_waybel_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f262,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_waybel_0(sK0,sK1))
        | r2_hidden(sK5(X0,sK0,k1_tarski(sK1)),k1_tarski(sK1)) )
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f260,f138])).

fof(f138,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_waybel_0(sK0,sK1))
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK5(X0,sK0,k1_tarski(sK1)),k1_tarski(sK1)) )
    | ~ spl6_19
    | ~ spl6_22 ),
    inference(superposition,[],[f203,f255])).

fof(f255,plain,
    ( k5_waybel_0(sK0,sK1) = a_2_0_waybel_0(sK0,k1_tarski(sK1))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f253])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_0_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK5(X0,sK0,X1),X1) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f202])).

fof(f335,plain,
    ( spl6_29
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f327,f305,f253,f136,f89,f73,f68,f332])).

fof(f68,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f73,plain,
    ( spl6_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f305,plain,
    ( spl6_28
  <=> sK2 = sK4(sK2,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f327,plain,
    ( r1_orders_2(sK0,sK2,sK5(sK2,sK0,k1_tarski(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f326,f91])).

fof(f326,plain,
    ( ~ r2_hidden(sK2,k5_waybel_0(sK0,sK1))
    | r1_orders_2(sK0,sK2,sK5(sK2,sK0,k1_tarski(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f325,f255])).

fof(f325,plain,
    ( r1_orders_2(sK0,sK2,sK5(sK2,sK0,k1_tarski(sK1)))
    | ~ r2_hidden(sK2,a_2_0_waybel_0(sK0,k1_tarski(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f324,f70])).

fof(f70,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f324,plain,
    ( r1_orders_2(sK0,sK2,sK5(sK2,sK0,k1_tarski(sK1)))
    | ~ r2_hidden(sK2,a_2_0_waybel_0(sK0,k1_tarski(sK1)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f323,f75])).

fof(f75,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f323,plain,
    ( r1_orders_2(sK0,sK2,sK5(sK2,sK0,k1_tarski(sK1)))
    | ~ r2_hidden(sK2,a_2_0_waybel_0(sK0,k1_tarski(sK1)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f321,f138])).

fof(f321,plain,
    ( r1_orders_2(sK0,sK2,sK5(sK2,sK0,k1_tarski(sK1)))
    | ~ r2_hidden(sK2,a_2_0_waybel_0(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_28 ),
    inference(superposition,[],[f60,f307])).

fof(f307,plain,
    ( sK2 = sK4(sK2,sK0,k1_tarski(sK1))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f305])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X1,sK4(X0,X1,X2),sK5(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X2)
            & r1_orders_2(X1,sK4(X0,X1,X2),sK5(X0,X1,X2))
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f37,f39,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X2)
              & r1_orders_2(X1,X5,X6)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X2)
            & r1_orders_2(X1,sK4(X0,X1,X2),X6)
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r1_orders_2(X1,sK4(X0,X1,X2),X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK5(X0,X1,X2),X2)
        & r1_orders_2(X1,sK4(X0,X1,X2),sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X2)
                  & r1_orders_2(X1,X5,X6)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r1_orders_2(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_waybel_0)).

fof(f308,plain,
    ( spl6_28
    | ~ spl6_5
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f295,f276,f89,f305])).

fof(f276,plain,
    ( spl6_25
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k5_waybel_0(sK0,sK1))
        | sK4(X1,sK0,k1_tarski(sK1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f295,plain,
    ( sK2 = sK4(sK2,sK0,k1_tarski(sK1))
    | ~ spl6_5
    | ~ spl6_25 ),
    inference(resolution,[],[f277,f91])).

fof(f277,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_waybel_0(sK0,sK1))
        | sK4(X1,sK0,k1_tarski(sK1)) = X1 )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f276])).

fof(f283,plain,
    ( spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f281,f90])).

fof(f90,plain,
    ( ~ r2_hidden(sK2,k5_waybel_0(sK0,sK1))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f281,plain,
    ( r2_hidden(sK2,k5_waybel_0(sK0,sK1))
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f280,f255])).

fof(f280,plain,
    ( r2_hidden(sK2,a_2_0_waybel_0(sK0,k1_tarski(sK1)))
    | ~ spl6_10
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f279,f138])).

fof(f279,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,a_2_0_waybel_0(sK0,k1_tarski(sK1)))
    | ~ spl6_24 ),
    inference(resolution,[],[f273,f64])).

fof(f64,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f273,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,a_2_0_waybel_0(sK0,X0)) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f272])).

% (30849)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f272,plain,
    ( spl6_24
  <=> ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,a_2_0_waybel_0(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f278,plain,
    ( spl6_25
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f263,f253,f193,f136,f276])).

fof(f193,plain,
    ( spl6_17
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,a_2_0_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK4(X0,sK0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f263,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_waybel_0(sK0,sK1))
        | sK4(X1,sK0,k1_tarski(sK1)) = X1 )
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f261,f138])).

fof(f261,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_waybel_0(sK0,sK1))
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK4(X1,sK0,k1_tarski(sK1)) = X1 )
    | ~ spl6_17
    | ~ spl6_22 ),
    inference(superposition,[],[f194,f255])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_0_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK4(X0,sK0,X1) = X0 )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f193])).

% (30840)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f274,plain,
    ( spl6_24
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f249,f242,f93,f83,f78,f272])).

fof(f78,plain,
    ( spl6_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f83,plain,
    ( spl6_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f242,plain,
    ( spl6_21
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X2,a_2_0_waybel_0(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,a_2_0_waybel_0(sK0,X0)) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f248,f85])).

fof(f85,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,a_2_0_waybel_0(sK0,X0)) )
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f246,f80])).

fof(f80,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,a_2_0_waybel_0(sK0,X0)) )
    | ~ spl6_6
    | ~ spl6_21 ),
    inference(resolution,[],[f243,f95])).

fof(f95,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f243,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X2,X0)
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X2,a_2_0_waybel_0(sK0,X1)) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f242])).

fof(f256,plain,
    ( spl6_22
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f245,f188,f173,f253])).

fof(f173,plain,
    ( spl6_15
  <=> a_2_0_waybel_0(sK0,k1_tarski(sK1)) = k3_waybel_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f188,plain,
    ( spl6_16
  <=> k5_waybel_0(sK0,sK1) = k3_waybel_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f245,plain,
    ( k5_waybel_0(sK0,sK1) = a_2_0_waybel_0(sK0,k1_tarski(sK1))
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f175,f190])).

fof(f190,plain,
    ( k5_waybel_0(sK0,sK1) = k3_waybel_0(sK0,k1_tarski(sK1))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f188])).

fof(f175,plain,
    ( a_2_0_waybel_0(sK0,k1_tarski(sK1)) = k3_waybel_0(sK0,k1_tarski(sK1))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f244,plain,
    ( spl6_21
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f150,f73,f68,f242])).

fof(f150,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X2,a_2_0_waybel_0(sK0,X1)) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f149,f70])).

fof(f149,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X2,a_2_0_waybel_0(sK0,X1))
        | v2_struct_0(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f66,f75])).

fof(f66,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_hidden(X4,X2)
      | ~ r1_orders_2(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(X3,a_2_0_waybel_0(X1,X2))
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r1_orders_2(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f204,plain,
    ( spl6_19
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f134,f73,f68,f202])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_0_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK5(X0,sK0,X1),X1) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f133,f70])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_0_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK5(X0,sK0,X1),X1)
        | v2_struct_0(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f61,f75])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK5(X0,X1,X2),X2)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f195,plain,
    ( spl6_17
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f129,f73,f68,f193])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_0_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK4(X0,sK0,X1) = X0 )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f128,f70])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_0_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK4(X0,sK0,X1) = X0
        | v2_struct_0(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f58,f75])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sK4(X0,X1,X2) = X0
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f191,plain,
    ( spl6_16
    | ~ spl6_3
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f181,f169,f106,f78,f188])).

fof(f106,plain,
    ( spl6_8
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f169,plain,
    ( spl6_14
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_waybel_0(sK0,X0) = k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f181,plain,
    ( k5_waybel_0(sK0,sK1) = k3_waybel_0(sK0,k1_tarski(sK1))
    | ~ spl6_3
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f177,f108])).

fof(f108,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f177,plain,
    ( k5_waybel_0(sK0,sK1) = k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl6_3
    | ~ spl6_14 ),
    inference(resolution,[],[f170,f80])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_waybel_0(sK0,X0) = k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f176,plain,
    ( spl6_15
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f164,f155,f136,f173])).

fof(f155,plain,
    ( spl6_12
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_waybel_0(sK0,X0) = a_2_0_waybel_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f164,plain,
    ( a_2_0_waybel_0(sK0,k1_tarski(sK1)) = k3_waybel_0(sK0,k1_tarski(sK1))
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(resolution,[],[f156,f138])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_waybel_0(sK0,X0) = a_2_0_waybel_0(sK0,X0) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f171,plain,
    ( spl6_14
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f127,f73,f68,f169])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_waybel_0(sK0,X0) = k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f126,f70])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_waybel_0(sK0,X0) = k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | v2_struct_0(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f49,f75])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_waybel_0)).

fof(f157,plain,
    ( spl6_12
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f125,f73,f68,f155])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_waybel_0(sK0,X0) = a_2_0_waybel_0(sK0,X0) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f124,f70])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_waybel_0(sK0,X0) = a_2_0_waybel_0(sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f50,f75])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k3_waybel_0(X0,X1) = a_2_0_waybel_0(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_waybel_0(X0,X1) = a_2_0_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_waybel_0(X0,X1) = a_2_0_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_waybel_0(X0,X1) = a_2_0_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_waybel_0)).

fof(f139,plain,
    ( spl6_10
    | ~ spl6_3
    | spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f132,f106,f102,f78,f136])).

fof(f102,plain,
    ( spl6_7
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f132,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_3
    | spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f131,f103])).

fof(f103,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f131,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f130,f80])).

fof(f130,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_8 ),
    inference(superposition,[],[f52,f108])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f123,plain,
    ( ~ spl6_2
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl6_2
    | spl6_9 ),
    inference(subsumption_resolution,[],[f120,f75])).

fof(f120,plain,
    ( ~ l1_orders_2(sK0)
    | spl6_9 ),
    inference(resolution,[],[f117,f47])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f117,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f118,plain,
    ( ~ spl6_9
    | spl6_1
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f112,f102,f68,f115])).

fof(f112,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_1
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f111,f70])).

fof(f111,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f104,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f104,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f109,plain,
    ( spl6_7
    | spl6_8
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f99,f78,f106,f102])).

fof(f99,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(resolution,[],[f51,f80])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f98,plain,
    ( ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f97,f93,f89])).

fof(f97,plain,
    ( ~ r2_hidden(sK2,k5_waybel_0(sK0,sK1))
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f46,f95])).

fof(f46,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r2_hidden(sK2,k5_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ r1_orders_2(sK0,sK2,sK1)
      | ~ r2_hidden(sK2,k5_waybel_0(sK0,sK1)) )
    & ( r1_orders_2(sK0,sK2,sK1)
      | r2_hidden(sK2,k5_waybel_0(sK0,sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_orders_2(X0,X2,X1)
                  | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) )
                & ( r1_orders_2(X0,X2,X1)
                  | r2_hidden(X2,k5_waybel_0(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(sK0,X2,X1)
                | ~ r2_hidden(X2,k5_waybel_0(sK0,X1)) )
              & ( r1_orders_2(sK0,X2,X1)
                | r2_hidden(X2,k5_waybel_0(sK0,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_orders_2(sK0,X2,X1)
              | ~ r2_hidden(X2,k5_waybel_0(sK0,X1)) )
            & ( r1_orders_2(sK0,X2,X1)
              | r2_hidden(X2,k5_waybel_0(sK0,X1)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r1_orders_2(sK0,X2,sK1)
            | ~ r2_hidden(X2,k5_waybel_0(sK0,sK1)) )
          & ( r1_orders_2(sK0,X2,sK1)
            | r2_hidden(X2,k5_waybel_0(sK0,sK1)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ( ~ r1_orders_2(sK0,X2,sK1)
          | ~ r2_hidden(X2,k5_waybel_0(sK0,sK1)) )
        & ( r1_orders_2(sK0,X2,sK1)
          | r2_hidden(X2,k5_waybel_0(sK0,sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r1_orders_2(sK0,sK2,sK1)
        | ~ r2_hidden(sK2,k5_waybel_0(sK0,sK1)) )
      & ( r1_orders_2(sK0,sK2,sK1)
        | r2_hidden(sK2,k5_waybel_0(sK0,sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X2,X1)
                | r2_hidden(X2,k5_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X2,X1)
                | r2_hidden(X2,k5_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k5_waybel_0(X0,X1))
                <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_waybel_0)).

fof(f96,plain,
    ( spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f45,f93,f89])).

fof(f45,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_hidden(sK2,k5_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f86,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f44,f83])).

fof(f44,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f43,f78])).

fof(f43,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f42,f73])).

fof(f42,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f41,f68])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

%------------------------------------------------------------------------------
