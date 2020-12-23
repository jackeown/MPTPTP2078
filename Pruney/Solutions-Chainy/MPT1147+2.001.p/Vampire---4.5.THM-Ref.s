%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 938 expanded)
%              Number of leaves         :   17 ( 330 expanded)
%              Depth                    :   30
%              Number of atoms          :  972 (14553 expanded)
%              Number of equality atoms :   13 (  32 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f710,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f169,f407,f421,f454,f536,f580,f629,f659,f709])).

fof(f709,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f704])).

fof(f704,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f27,f28,f30,f29,f83,f399,f701,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(X1,X2)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_proxy_replacement,[],[f53,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(f701,plain,
    ( ~ sQ5_eqProxy(sK2,sK1)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f698,f69])).

fof(f69,plain,(
    ! [X0] : sQ5_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f55])).

% (32189)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f698,plain,
    ( ~ sQ5_eqProxy(sK1,sK1)
    | ~ sQ5_eqProxy(sK2,sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f697,f29])).

fof(f697,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sQ5_eqProxy(sK1,X0)
        | ~ sQ5_eqProxy(sK2,X0) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f695,f69])).

fof(f695,plain,
    ( ! [X0] :
        ( ~ sQ5_eqProxy(sK0,sK0)
        | ~ sQ5_eqProxy(sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sQ5_eqProxy(sK2,X0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f691,f28])).

fof(f691,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(X1)
        | ~ sQ5_eqProxy(sK0,X1)
        | ~ sQ5_eqProxy(sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ sQ5_eqProxy(sK2,X0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f427,f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f427,plain,
    ( ! [X2,X0,X1] :
        ( r2_orders_2(X2,X0,X1)
        | ~ sQ5_eqProxy(sK2,X1)
        | ~ sQ5_eqProxy(sK0,X2)
        | ~ sQ5_eqProxy(sK1,X0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f79,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_orders_2(X0,X2,X4)
      | ~ sQ5_eqProxy(X2,X3)
      | ~ sQ5_eqProxy(X4,X5)
      | ~ sQ5_eqProxy(X0,X1)
      | r2_orders_2(X1,X3,X5) ) ),
    inference(equality_proxy_axiom,[],[f55])).

fof(f79,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_2
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f399,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f397])).

fof(f397,plain,
    ( spl6_7
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f83,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_3
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f29,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ( ( r1_orders_2(sK0,sK2,sK1)
          | ~ r2_orders_2(sK0,sK1,sK2) )
        & ( ~ r1_orders_2(sK0,sK2,sK1)
          | r2_orders_2(sK0,sK1,sK2) ) )
      | ! [X3] :
          ( ~ r2_hidden(sK2,X3)
          | ~ r2_hidden(sK1,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v6_orders_2(X3,sK0) ) )
    & ( ( ( r2_orders_2(sK0,sK1,sK2)
          | r1_orders_2(sK0,sK2,sK1) )
        & ( ~ r1_orders_2(sK0,sK2,sK1)
          | ~ r2_orders_2(sK0,sK1,sK2) ) )
      | ( r2_hidden(sK2,sK3)
        & r2_hidden(sK1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        & v6_orders_2(sK3,sK0) ) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ( r1_orders_2(X0,X2,X1)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X1)
                      | r2_orders_2(X0,X1,X2) ) )
                  | ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X3,X0) ) )
                & ( ( ( r2_orders_2(X0,X1,X2)
                      | r1_orders_2(X0,X2,X1) )
                    & ( ~ r1_orders_2(X0,X2,X1)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | ? [X4] :
                      ( r2_hidden(X2,X4)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X4,X0) ) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ( r1_orders_2(sK0,X2,X1)
                    | ~ r2_orders_2(sK0,X1,X2) )
                  & ( ~ r1_orders_2(sK0,X2,X1)
                    | r2_orders_2(sK0,X1,X2) ) )
                | ! [X3] :
                    ( ~ r2_hidden(X2,X3)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                    | ~ v6_orders_2(X3,sK0) ) )
              & ( ( ( r2_orders_2(sK0,X1,X2)
                    | r1_orders_2(sK0,X2,X1) )
                  & ( ~ r1_orders_2(sK0,X2,X1)
                    | ~ r2_orders_2(sK0,X1,X2) ) )
                | ? [X4] :
                    ( r2_hidden(X2,X4)
                    & r2_hidden(X1,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
                    & v6_orders_2(X4,sK0) ) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ( ( r1_orders_2(sK0,X2,X1)
                  | ~ r2_orders_2(sK0,X1,X2) )
                & ( ~ r1_orders_2(sK0,X2,X1)
                  | r2_orders_2(sK0,X1,X2) ) )
              | ! [X3] :
                  ( ~ r2_hidden(X2,X3)
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                  | ~ v6_orders_2(X3,sK0) ) )
            & ( ( ( r2_orders_2(sK0,X1,X2)
                  | r1_orders_2(sK0,X2,X1) )
                & ( ~ r1_orders_2(sK0,X2,X1)
                  | ~ r2_orders_2(sK0,X1,X2) ) )
              | ? [X4] :
                  ( r2_hidden(X2,X4)
                  & r2_hidden(X1,X4)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
                  & v6_orders_2(X4,sK0) ) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ( ( r1_orders_2(sK0,X2,sK1)
                | ~ r2_orders_2(sK0,sK1,X2) )
              & ( ~ r1_orders_2(sK0,X2,sK1)
                | r2_orders_2(sK0,sK1,X2) ) )
            | ! [X3] :
                ( ~ r2_hidden(X2,X3)
                | ~ r2_hidden(sK1,X3)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                | ~ v6_orders_2(X3,sK0) ) )
          & ( ( ( r2_orders_2(sK0,sK1,X2)
                | r1_orders_2(sK0,X2,sK1) )
              & ( ~ r1_orders_2(sK0,X2,sK1)
                | ~ r2_orders_2(sK0,sK1,X2) ) )
            | ? [X4] :
                ( r2_hidden(X2,X4)
                & r2_hidden(sK1,X4)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
                & v6_orders_2(X4,sK0) ) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ( ( ( r1_orders_2(sK0,X2,sK1)
              | ~ r2_orders_2(sK0,sK1,X2) )
            & ( ~ r1_orders_2(sK0,X2,sK1)
              | r2_orders_2(sK0,sK1,X2) ) )
          | ! [X3] :
              ( ~ r2_hidden(X2,X3)
              | ~ r2_hidden(sK1,X3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
              | ~ v6_orders_2(X3,sK0) ) )
        & ( ( ( r2_orders_2(sK0,sK1,X2)
              | r1_orders_2(sK0,X2,sK1) )
            & ( ~ r1_orders_2(sK0,X2,sK1)
              | ~ r2_orders_2(sK0,sK1,X2) ) )
          | ? [X4] :
              ( r2_hidden(X2,X4)
              & r2_hidden(sK1,X4)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
              & v6_orders_2(X4,sK0) ) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ( ( r1_orders_2(sK0,sK2,sK1)
            | ~ r2_orders_2(sK0,sK1,sK2) )
          & ( ~ r1_orders_2(sK0,sK2,sK1)
            | r2_orders_2(sK0,sK1,sK2) ) )
        | ! [X3] :
            ( ~ r2_hidden(sK2,X3)
            | ~ r2_hidden(sK1,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v6_orders_2(X3,sK0) ) )
      & ( ( ( r2_orders_2(sK0,sK1,sK2)
            | r1_orders_2(sK0,sK2,sK1) )
          & ( ~ r1_orders_2(sK0,sK2,sK1)
            | ~ r2_orders_2(sK0,sK1,sK2) ) )
        | ? [X4] :
            ( r2_hidden(sK2,X4)
            & r2_hidden(sK1,X4)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
            & v6_orders_2(X4,sK0) ) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X4] :
        ( r2_hidden(sK2,X4)
        & r2_hidden(sK1,X4)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        & v6_orders_2(X4,sK0) )
   => ( r2_hidden(sK2,sK3)
      & r2_hidden(sK1,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      & v6_orders_2(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ( r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | r2_orders_2(X0,X1,X2) ) )
                | ! [X3] :
                    ( ~ r2_hidden(X2,X3)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v6_orders_2(X3,X0) ) )
              & ( ( ( r2_orders_2(X0,X1,X2)
                    | r1_orders_2(X0,X2,X1) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) ) )
                | ? [X4] :
                    ( r2_hidden(X2,X4)
                    & r2_hidden(X1,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X4,X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ( r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | r2_orders_2(X0,X1,X2) ) )
                | ! [X3] :
                    ( ~ r2_hidden(X2,X3)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v6_orders_2(X3,X0) ) )
              & ( ( ( r2_orders_2(X0,X1,X2)
                    | r1_orders_2(X0,X2,X1) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) ) )
                | ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ( r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | r2_orders_2(X0,X1,X2) ) )
                | ! [X3] :
                    ( ~ r2_hidden(X2,X3)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v6_orders_2(X3,X0) ) )
              & ( ( ( r2_orders_2(X0,X1,X2)
                    | r1_orders_2(X0,X2,X1) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) ) )
                | ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <~> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <~> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                <=> ( r2_orders_2(X0,X1,X2)
                  <=> ~ r1_orders_2(X0,X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <=> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_orders_2)).

fof(f30,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f28,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f27,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f659,plain,
    ( ~ spl6_7
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f658])).

fof(f658,plain,
    ( $false
    | ~ spl6_7
    | spl6_10 ),
    inference(subsumption_resolution,[],[f657,f26])).

fof(f26,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f657,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl6_7
    | spl6_10 ),
    inference(subsumption_resolution,[],[f656,f28])).

fof(f656,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_7
    | spl6_10 ),
    inference(subsumption_resolution,[],[f655,f30])).

fof(f655,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_7
    | spl6_10 ),
    inference(subsumption_resolution,[],[f654,f29])).

fof(f654,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_7
    | spl6_10 ),
    inference(subsumption_resolution,[],[f639,f399])).

fof(f639,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl6_10 ),
    inference(resolution,[],[f535,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(sK4(X0,X1,X2),X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( r2_hidden(X2,sK4(X0,X1,X2))
                    & r2_hidden(X1,sK4(X0,X1,X2))
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(sK4(X0,X1,X2),X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X3,X0) )
     => ( r2_hidden(X2,sK4(X0,X1,X2))
        & r2_hidden(X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & v6_orders_2(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X4] :
                        ( r2_hidden(X2,X4)
                        & r2_hidden(X1,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X4,X0) ) ) ) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X3] :
                        ( r2_hidden(X2,X3)
                        & r2_hidden(X1,X3)
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).

fof(f535,plain,
    ( ~ v6_orders_2(sK4(sK0,sK2,sK1),sK0)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f533])).

fof(f533,plain,
    ( spl6_10
  <=> v6_orders_2(sK4(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f629,plain,
    ( ~ spl6_7
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | ~ spl6_7
    | spl6_9 ),
    inference(subsumption_resolution,[],[f627,f399])).

fof(f627,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl6_9 ),
    inference(subsumption_resolution,[],[f626,f30])).

fof(f626,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | spl6_9 ),
    inference(subsumption_resolution,[],[f594,f29])).

fof(f594,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | spl6_9 ),
    inference(resolution,[],[f531,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK4(sK0,X1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f117,f28])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_hidden(X0,sK4(sK0,X1,X0)) ) ),
    inference(resolution,[],[f52,f26])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(X2,sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f531,plain,
    ( ~ r2_hidden(sK1,sK4(sK0,sK2,sK1))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f529])).

fof(f529,plain,
    ( spl6_9
  <=> r2_hidden(sK1,sK4(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f580,plain,
    ( ~ spl6_7
    | spl6_8 ),
    inference(avatar_contradiction_clause,[],[f579])).

fof(f579,plain,
    ( $false
    | ~ spl6_7
    | spl6_8 ),
    inference(subsumption_resolution,[],[f578,f399])).

fof(f578,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f577,f30])).

fof(f577,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f545,f29])).

fof(f545,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | spl6_8 ),
    inference(resolution,[],[f527,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,sK4(sK0,X1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f101,f28])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_hidden(X1,sK4(sK0,X1,X0)) ) ),
    inference(resolution,[],[f50,f26])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(X1,sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f527,plain,
    ( ~ r2_hidden(sK2,sK4(sK0,sK2,sK1))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f525])).

fof(f525,plain,
    ( spl6_8
  <=> r2_hidden(sK2,sK4(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f536,plain,
    ( ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_2
    | spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f498,f397,f82,f78,f533,f529,f525])).

fof(f498,plain,
    ( ~ v6_orders_2(sK4(sK0,sK2,sK1),sK0)
    | ~ r2_hidden(sK1,sK4(sK0,sK2,sK1))
    | ~ r2_hidden(sK2,sK4(sK0,sK2,sK1))
    | ~ spl6_2
    | spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f496,f399])).

fof(f496,plain,
    ( ~ v6_orders_2(sK4(sK0,sK2,sK1),sK0)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ r2_hidden(sK1,sK4(sK0,sK2,sK1))
    | ~ r2_hidden(sK2,sK4(sK0,sK2,sK1))
    | ~ spl6_2
    | spl6_3 ),
    inference(resolution,[],[f484,f30])).

fof(f484,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v6_orders_2(sK4(sK0,X0,sK1),sK0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r2_hidden(sK1,sK4(sK0,X0,sK1))
        | ~ r2_hidden(sK2,sK4(sK0,X0,sK1)) )
    | ~ spl6_2
    | spl6_3 ),
    inference(resolution,[],[f471,f29])).

fof(f471,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(sK2,sK4(sK0,X0,X1))
        | ~ v6_orders_2(sK4(sK0,X0,X1),sK0)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r2_hidden(sK1,sK4(sK0,X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f470,f26])).

fof(f470,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK1,sK4(sK0,X0,X1))
        | ~ r2_hidden(sK2,sK4(sK0,X0,X1))
        | ~ v6_orders_2(sK4(sK0,X0,X1),sK0)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v3_orders_2(sK0) )
    | ~ spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f467,f28])).

fof(f467,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK1,sK4(sK0,X0,X1))
        | ~ r2_hidden(sK2,sK4(sK0,X0,X1))
        | ~ v6_orders_2(sK4(sK0,X0,X1),sK0)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_2
    | spl6_3 ),
    inference(resolution,[],[f462,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f462,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X3)
        | ~ r2_hidden(sK2,X3)
        | ~ v6_orders_2(X3,sK0) )
    | ~ spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f422,f79])).

fof(f422,plain,
    ( ! [X3] :
        ( ~ r2_orders_2(sK0,sK1,sK2)
        | ~ r2_hidden(sK2,X3)
        | ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(X3,sK0) )
    | spl6_3 ),
    inference(subsumption_resolution,[],[f40,f84])).

fof(f84,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f40,plain,(
    ! [X3] :
      ( r1_orders_2(sK0,sK2,sK1)
      | ~ r2_orders_2(sK0,sK1,sK2)
      | ~ r2_hidden(sK2,X3)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(X3,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

% (32184)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f454,plain,
    ( ~ spl6_2
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | ~ spl6_2
    | spl6_7 ),
    inference(subsumption_resolution,[],[f452,f28])).

fof(f452,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl6_2
    | spl6_7 ),
    inference(subsumption_resolution,[],[f451,f29])).

fof(f451,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl6_2
    | spl6_7 ),
    inference(subsumption_resolution,[],[f450,f30])).

fof(f450,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl6_2
    | spl6_7 ),
    inference(subsumption_resolution,[],[f443,f79])).

fof(f443,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl6_7 ),
    inference(resolution,[],[f398,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f398,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f397])).

fof(f421,plain,
    ( spl6_2
    | spl6_3
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | spl6_2
    | spl6_3
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f28,f29,f30,f399,f80,f415,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(X1,X2)
      | r2_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_proxy_replacement,[],[f43,f55])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,X1,X2)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f415,plain,
    ( ~ sQ5_eqProxy(sK1,sK2)
    | spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f414,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( sQ5_eqProxy(X1,X0)
      | ~ sQ5_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f55])).

fof(f414,plain,
    ( ~ sQ5_eqProxy(sK2,sK1)
    | ~ sQ5_eqProxy(sK1,sK2)
    | spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f413,f69])).

fof(f413,plain,
    ( ~ sQ5_eqProxy(sK2,sK1)
    | ~ sQ5_eqProxy(sK1,sK2)
    | ~ sQ5_eqProxy(sK0,sK0)
    | spl6_3
    | ~ spl6_7 ),
    inference(resolution,[],[f399,f370])).

fof(f370,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_orders_2(X3,X1,X2)
        | ~ sQ5_eqProxy(X2,sK1)
        | ~ sQ5_eqProxy(X1,sK2)
        | ~ sQ5_eqProxy(X3,sK0) )
    | spl6_3 ),
    inference(resolution,[],[f84,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X3,X5)
      | ~ sQ5_eqProxy(X2,X3)
      | ~ sQ5_eqProxy(X4,X5)
      | ~ r1_orders_2(X0,X2,X4)
      | ~ sQ5_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f55])).

fof(f80,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f407,plain,
    ( ~ spl6_1
    | spl6_2
    | spl6_3
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | spl6_3
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f26,f28,f380,f383,f76,f30,f29,f387,f84,f398,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(X2,X4)
      | ~ r2_hidden(X1,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X4,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f387,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f386,f84])).

fof(f386,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_2 ),
    inference(subsumption_resolution,[],[f36,f80])).

fof(f36,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,
    ( v6_orders_2(sK3,sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_1
  <=> v6_orders_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f383,plain,
    ( r2_hidden(sK2,sK3)
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f382,f84])).

fof(f382,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_hidden(sK2,sK3)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f38,f80])).

fof(f38,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f380,plain,
    ( r2_hidden(sK1,sK3)
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f379,f84])).

fof(f379,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_hidden(sK1,sK3)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f37,f80])).

fof(f37,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f169,plain,
    ( spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f167,f83])).

fof(f167,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f166,f30])).

fof(f166,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f156,f29])).

fof(f156,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f147,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,sK4(sK0,X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f109,f28])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_hidden(X1,sK4(sK0,X0,X1)) ) ),
    inference(resolution,[],[f51,f26])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(X2,sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f147,plain,
    ( ~ r2_hidden(sK1,sK4(sK0,sK2,sK1))
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f143,f29])).

fof(f143,plain,
    ( ~ r2_hidden(sK1,sK4(sK0,sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f142,f83])).

fof(f142,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,sK2,X1)
        | ~ r2_hidden(sK1,sK4(sK0,sK2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f141,f26])).

fof(f141,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,sK4(sK0,sK2,X1))
        | ~ r1_orders_2(sK0,sK2,X1)
        | ~ v3_orders_2(sK0) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f140,f28])).

fof(f140,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,sK4(sK0,sK2,X1))
        | ~ r1_orders_2(sK0,sK2,X1)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f135,f30])).

fof(f135,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,sK4(sK0,sK2,X1))
        | ~ r1_orders_2(sK0,sK2,X1)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | spl6_2
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,sK4(sK0,sK2,X1))
        | ~ r1_orders_2(sK0,sK2,X1)
        | ~ r1_orders_2(sK0,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f132,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(sK4(X0,X1,X2),X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ v6_orders_2(sK4(sK0,sK2,X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,sK4(sK0,sK2,X0))
        | ~ r1_orders_2(sK0,sK2,X0) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f131,f26])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v3_orders_2(sK0)
        | ~ r2_hidden(sK1,sK4(sK0,sK2,X0))
        | ~ v6_orders_2(sK4(sK0,sK2,X0),sK0) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f130,f28])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ r2_hidden(sK1,sK4(sK0,sK2,X0))
        | ~ v6_orders_2(sK4(sK0,sK2,X0),sK0) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f129,f30])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ r2_hidden(sK1,sK4(sK0,sK2,X0))
        | ~ v6_orders_2(sK4(sK0,sK2,X0),sK0) )
    | spl6_2
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r2_hidden(sK1,sK4(sK0,sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v6_orders_2(sK4(sK0,sK2,X0),sK0) )
    | spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f47,f100])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK0,sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r2_hidden(sK1,sK4(sK0,sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v6_orders_2(sK4(sK0,sK2,X0),sK0) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f98,f30])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r2_hidden(sK1,sK4(sK0,sK2,X0))
        | ~ m1_subset_1(sK4(sK0,sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(sK4(sK0,sK2,X0),sK0) )
    | spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f97,f92])).

fof(f92,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK2,X3)
        | ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(X3,sK0) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f91,f80])).

fof(f91,plain,
    ( ! [X3] :
        ( r2_orders_2(sK0,sK1,sK2)
        | ~ r2_hidden(sK2,X3)
        | ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(X3,sK0) )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f39,f83])).

fof(f39,plain,(
    ! [X3] :
      ( ~ r1_orders_2(sK0,sK2,sK1)
      | r2_orders_2(sK0,sK1,sK2)
      | ~ r2_hidden(sK2,X3)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(X3,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK4(sK0,X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f95,f28])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_hidden(X0,sK4(sK0,X0,X1)) ) ),
    inference(resolution,[],[f49,f26])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(X1,sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f89,plain,
    ( spl6_1
    | spl6_2
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl6_1
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f87,f75])).

fof(f75,plain,
    ( ~ v6_orders_2(sK3,sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f87,plain,
    ( v6_orders_2(sK3,sK0)
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f86,f84])).

fof(f86,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | v6_orders_2(sK3,sK0)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f35,f80])).

fof(f35,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | v6_orders_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (32194)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (32185)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (32182)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (32199)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (32190)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (32191)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (32186)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (32183)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (32198)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (32194)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f710,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f89,f169,f407,f421,f454,f536,f580,f629,f659,f709])).
% 0.22/0.53  fof(f709,plain,(
% 0.22/0.53    ~spl6_2 | ~spl6_3 | ~spl6_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f704])).
% 0.22/0.53  fof(f704,plain,(
% 0.22/0.53    $false | (~spl6_2 | ~spl6_3 | ~spl6_7)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f27,f28,f30,f29,f83,f399,f701,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (sQ5_eqProxy(X1,X2) | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.53    inference(equality_proxy_replacement,[],[f53,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.53    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (X1 = X2 | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).
% 0.22/0.53  fof(f701,plain,(
% 0.22/0.53    ~sQ5_eqProxy(sK2,sK1) | ~spl6_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f698,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X0] : (sQ5_eqProxy(X0,X0)) )),
% 0.22/0.53    inference(equality_proxy_axiom,[],[f55])).
% 0.22/0.53  % (32189)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  fof(f698,plain,(
% 0.22/0.53    ~sQ5_eqProxy(sK1,sK1) | ~sQ5_eqProxy(sK2,sK1) | ~spl6_2),
% 0.22/0.53    inference(resolution,[],[f697,f29])).
% 0.22/0.53  fof(f697,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~sQ5_eqProxy(sK1,X0) | ~sQ5_eqProxy(sK2,X0)) ) | ~spl6_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f695,f69])).
% 0.22/0.53  fof(f695,plain,(
% 0.22/0.53    ( ! [X0] : (~sQ5_eqProxy(sK0,sK0) | ~sQ5_eqProxy(sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~sQ5_eqProxy(sK2,X0)) ) | ~spl6_2),
% 0.22/0.53    inference(resolution,[],[f691,f28])).
% 0.22/0.53  fof(f691,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_orders_2(X1) | ~sQ5_eqProxy(sK0,X1) | ~sQ5_eqProxy(sK1,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~sQ5_eqProxy(sK2,X0)) ) | ~spl6_2),
% 0.22/0.53    inference(resolution,[],[f427,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 0.22/0.53  fof(f427,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_orders_2(X2,X0,X1) | ~sQ5_eqProxy(sK2,X1) | ~sQ5_eqProxy(sK0,X2) | ~sQ5_eqProxy(sK1,X0)) ) | ~spl6_2),
% 0.22/0.53    inference(resolution,[],[f79,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_orders_2(X0,X2,X4) | ~sQ5_eqProxy(X2,X3) | ~sQ5_eqProxy(X4,X5) | ~sQ5_eqProxy(X0,X1) | r2_orders_2(X1,X3,X5)) )),
% 0.22/0.53    inference(equality_proxy_axiom,[],[f55])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    r2_orders_2(sK0,sK1,sK2) | ~spl6_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    spl6_2 <=> r2_orders_2(sK0,sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.53  fof(f399,plain,(
% 0.22/0.53    r1_orders_2(sK0,sK1,sK2) | ~spl6_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f397])).
% 0.22/0.53  fof(f397,plain,(
% 0.22/0.53    spl6_7 <=> r1_orders_2(sK0,sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    r1_orders_2(sK0,sK2,sK1) | ~spl6_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    spl6_3 <=> r1_orders_2(sK0,sK2,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    (((((r1_orders_2(sK0,sK2,sK1) | ~r2_orders_2(sK0,sK1,sK2)) & (~r1_orders_2(sK0,sK2,sK1) | r2_orders_2(sK0,sK1,sK2))) | ! [X3] : (~r2_hidden(sK2,X3) | ~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(X3,sK0))) & (((r2_orders_2(sK0,sK1,sK2) | r1_orders_2(sK0,sK2,sK1)) & (~r1_orders_2(sK0,sK2,sK1) | ~r2_orders_2(sK0,sK1,sK2))) | (r2_hidden(sK2,sK3) & r2_hidden(sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) & v6_orders_2(sK3,sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v3_orders_2(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f20,f19,f18,f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((((r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X1) | r2_orders_2(X0,X1,X2))) | ! [X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X3,X0))) & (((r2_orders_2(X0,X1,X2) | r1_orders_2(X0,X2,X1)) & (~r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2))) | ? [X4] : (r2_hidden(X2,X4) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X4,X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : ((((r1_orders_2(sK0,X2,X1) | ~r2_orders_2(sK0,X1,X2)) & (~r1_orders_2(sK0,X2,X1) | r2_orders_2(sK0,X1,X2))) | ! [X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(X3,sK0))) & (((r2_orders_2(sK0,X1,X2) | r1_orders_2(sK0,X2,X1)) & (~r1_orders_2(sK0,X2,X1) | ~r2_orders_2(sK0,X1,X2))) | ? [X4] : (r2_hidden(X2,X4) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) & v6_orders_2(X4,sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v3_orders_2(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : ((((r1_orders_2(sK0,X2,X1) | ~r2_orders_2(sK0,X1,X2)) & (~r1_orders_2(sK0,X2,X1) | r2_orders_2(sK0,X1,X2))) | ! [X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(X3,sK0))) & (((r2_orders_2(sK0,X1,X2) | r1_orders_2(sK0,X2,X1)) & (~r1_orders_2(sK0,X2,X1) | ~r2_orders_2(sK0,X1,X2))) | ? [X4] : (r2_hidden(X2,X4) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) & v6_orders_2(X4,sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((((r1_orders_2(sK0,X2,sK1) | ~r2_orders_2(sK0,sK1,X2)) & (~r1_orders_2(sK0,X2,sK1) | r2_orders_2(sK0,sK1,X2))) | ! [X3] : (~r2_hidden(X2,X3) | ~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(X3,sK0))) & (((r2_orders_2(sK0,sK1,X2) | r1_orders_2(sK0,X2,sK1)) & (~r1_orders_2(sK0,X2,sK1) | ~r2_orders_2(sK0,sK1,X2))) | ? [X4] : (r2_hidden(X2,X4) & r2_hidden(sK1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) & v6_orders_2(X4,sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X2] : ((((r1_orders_2(sK0,X2,sK1) | ~r2_orders_2(sK0,sK1,X2)) & (~r1_orders_2(sK0,X2,sK1) | r2_orders_2(sK0,sK1,X2))) | ! [X3] : (~r2_hidden(X2,X3) | ~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(X3,sK0))) & (((r2_orders_2(sK0,sK1,X2) | r1_orders_2(sK0,X2,sK1)) & (~r1_orders_2(sK0,X2,sK1) | ~r2_orders_2(sK0,sK1,X2))) | ? [X4] : (r2_hidden(X2,X4) & r2_hidden(sK1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) & v6_orders_2(X4,sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) => ((((r1_orders_2(sK0,sK2,sK1) | ~r2_orders_2(sK0,sK1,sK2)) & (~r1_orders_2(sK0,sK2,sK1) | r2_orders_2(sK0,sK1,sK2))) | ! [X3] : (~r2_hidden(sK2,X3) | ~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(X3,sK0))) & (((r2_orders_2(sK0,sK1,sK2) | r1_orders_2(sK0,sK2,sK1)) & (~r1_orders_2(sK0,sK2,sK1) | ~r2_orders_2(sK0,sK1,sK2))) | ? [X4] : (r2_hidden(sK2,X4) & r2_hidden(sK1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) & v6_orders_2(X4,sK0))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ? [X4] : (r2_hidden(sK2,X4) & r2_hidden(sK1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) & v6_orders_2(X4,sK0)) => (r2_hidden(sK2,sK3) & r2_hidden(sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) & v6_orders_2(sK3,sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((((r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X1) | r2_orders_2(X0,X1,X2))) | ! [X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X3,X0))) & (((r2_orders_2(X0,X1,X2) | r1_orders_2(X0,X2,X1)) & (~r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2))) | ? [X4] : (r2_hidden(X2,X4) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X4,X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 0.22/0.53    inference(rectify,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((((r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X1) | r2_orders_2(X0,X1,X2))) | ! [X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X3,X0))) & (((r2_orders_2(X0,X1,X2) | r1_orders_2(X0,X2,X1)) & (~r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2))) | ? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (((((r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X1) | r2_orders_2(X0,X1,X2))) | ! [X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X3,X0))) & (((r2_orders_2(X0,X1,X2) | r1_orders_2(X0,X2,X1)) & (~r1_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2))) | ? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) <~> (r2_orders_2(X0,X1,X2) <=> ~r1_orders_2(X0,X2,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f7])).
% 0.22/0.53  fof(f7,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) <~> (r2_orders_2(X0,X1,X2) <=> ~r1_orders_2(X0,X2,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) <=> (r2_orders_2(X0,X1,X2) <=> ~r1_orders_2(X0,X2,X1))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f4])).
% 0.22/0.53  fof(f4,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) <=> (r2_orders_2(X0,X1,X2) <=> ~r1_orders_2(X0,X2,X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_orders_2)).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    l1_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    v5_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f659,plain,(
% 0.22/0.53    ~spl6_7 | spl6_10),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f658])).
% 0.22/0.53  fof(f658,plain,(
% 0.22/0.53    $false | (~spl6_7 | spl6_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f657,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    v3_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f657,plain,(
% 0.22/0.53    ~v3_orders_2(sK0) | (~spl6_7 | spl6_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f656,f28])).
% 0.22/0.53  fof(f656,plain,(
% 0.22/0.53    ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | (~spl6_7 | spl6_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f655,f30])).
% 0.22/0.53  fof(f655,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | (~spl6_7 | spl6_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f654,f29])).
% 0.22/0.53  fof(f654,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | (~spl6_7 | spl6_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f639,f399])).
% 0.22/0.53  fof(f639,plain,(
% 0.22/0.53    ~r1_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | spl6_10),
% 0.22/0.53    inference(resolution,[],[f535,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v6_orders_2(sK4(X0,X1,X2),X0) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((((r2_hidden(X2,sK4(X0,X1,X2)) & r2_hidden(X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(sK4(X0,X1,X2),X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => (r2_hidden(X2,sK4(X0,X1,X2)) & r2_hidden(X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(sK4(X0,X1,X2),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : ((r2_hidden(X2,X3) & r2_hidden(X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0))) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,plain,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X4] : (r2_hidden(X2,X4) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X4,X0)))))))),
% 0.22/0.53    inference(rectify,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).
% 0.22/0.53  fof(f535,plain,(
% 0.22/0.53    ~v6_orders_2(sK4(sK0,sK2,sK1),sK0) | spl6_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f533])).
% 0.22/0.53  fof(f533,plain,(
% 0.22/0.53    spl6_10 <=> v6_orders_2(sK4(sK0,sK2,sK1),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.53  fof(f629,plain,(
% 0.22/0.53    ~spl6_7 | spl6_9),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f628])).
% 0.22/0.53  fof(f628,plain,(
% 0.22/0.53    $false | (~spl6_7 | spl6_9)),
% 0.22/0.53    inference(subsumption_resolution,[],[f627,f399])).
% 0.22/0.53  fof(f627,plain,(
% 0.22/0.53    ~r1_orders_2(sK0,sK1,sK2) | spl6_9),
% 0.22/0.53    inference(subsumption_resolution,[],[f626,f30])).
% 0.22/0.53  fof(f626,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK2) | spl6_9),
% 0.22/0.53    inference(subsumption_resolution,[],[f594,f29])).
% 0.22/0.53  fof(f594,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK2) | spl6_9),
% 0.22/0.53    inference(resolution,[],[f531,f119])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(X0,sK4(sK0,X1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f117,f28])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_hidden(X0,sK4(sK0,X1,X0))) )),
% 0.22/0.53    inference(resolution,[],[f52,f26])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(X2,sK4(X0,X1,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f531,plain,(
% 0.22/0.53    ~r2_hidden(sK1,sK4(sK0,sK2,sK1)) | spl6_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f529])).
% 0.22/0.53  fof(f529,plain,(
% 0.22/0.53    spl6_9 <=> r2_hidden(sK1,sK4(sK0,sK2,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.53  fof(f580,plain,(
% 0.22/0.53    ~spl6_7 | spl6_8),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f579])).
% 0.22/0.53  fof(f579,plain,(
% 0.22/0.53    $false | (~spl6_7 | spl6_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f578,f399])).
% 0.22/0.53  fof(f578,plain,(
% 0.22/0.53    ~r1_orders_2(sK0,sK1,sK2) | spl6_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f577,f30])).
% 0.22/0.53  fof(f577,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK2) | spl6_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f545,f29])).
% 0.22/0.53  fof(f545,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK2) | spl6_8),
% 0.22/0.53    inference(resolution,[],[f527,f103])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(X1,sK4(sK0,X1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f101,f28])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_hidden(X1,sK4(sK0,X1,X0))) )),
% 0.22/0.53    inference(resolution,[],[f50,f26])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(X1,sK4(X0,X1,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f527,plain,(
% 0.22/0.53    ~r2_hidden(sK2,sK4(sK0,sK2,sK1)) | spl6_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f525])).
% 0.22/0.53  fof(f525,plain,(
% 0.22/0.53    spl6_8 <=> r2_hidden(sK2,sK4(sK0,sK2,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.53  fof(f536,plain,(
% 0.22/0.53    ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_2 | spl6_3 | ~spl6_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f498,f397,f82,f78,f533,f529,f525])).
% 0.22/0.53  fof(f498,plain,(
% 0.22/0.53    ~v6_orders_2(sK4(sK0,sK2,sK1),sK0) | ~r2_hidden(sK1,sK4(sK0,sK2,sK1)) | ~r2_hidden(sK2,sK4(sK0,sK2,sK1)) | (~spl6_2 | spl6_3 | ~spl6_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f496,f399])).
% 0.22/0.53  fof(f496,plain,(
% 0.22/0.53    ~v6_orders_2(sK4(sK0,sK2,sK1),sK0) | ~r1_orders_2(sK0,sK1,sK2) | ~r2_hidden(sK1,sK4(sK0,sK2,sK1)) | ~r2_hidden(sK2,sK4(sK0,sK2,sK1)) | (~spl6_2 | spl6_3)),
% 0.22/0.53    inference(resolution,[],[f484,f30])).
% 0.22/0.53  fof(f484,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v6_orders_2(sK4(sK0,X0,sK1),sK0) | ~r1_orders_2(sK0,sK1,X0) | ~r2_hidden(sK1,sK4(sK0,X0,sK1)) | ~r2_hidden(sK2,sK4(sK0,X0,sK1))) ) | (~spl6_2 | spl6_3)),
% 0.22/0.53    inference(resolution,[],[f471,f29])).
% 0.22/0.53  fof(f471,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(sK2,sK4(sK0,X0,X1)) | ~v6_orders_2(sK4(sK0,X0,X1),sK0) | ~r1_orders_2(sK0,X1,X0) | ~r2_hidden(sK1,sK4(sK0,X0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl6_2 | spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f470,f26])).
% 0.22/0.53  fof(f470,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(sK1,sK4(sK0,X0,X1)) | ~r2_hidden(sK2,sK4(sK0,X0,X1)) | ~v6_orders_2(sK4(sK0,X0,X1),sK0) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_orders_2(sK0)) ) | (~spl6_2 | spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f467,f28])).
% 0.22/0.53  fof(f467,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(sK1,sK4(sK0,X0,X1)) | ~r2_hidden(sK2,sK4(sK0,X0,X1)) | ~v6_orders_2(sK4(sK0,X0,X1),sK0) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0)) ) | (~spl6_2 | spl6_3)),
% 0.22/0.53    inference(resolution,[],[f462,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f462,plain,(
% 0.22/0.53    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X3) | ~r2_hidden(sK2,X3) | ~v6_orders_2(X3,sK0)) ) | (~spl6_2 | spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f422,f79])).
% 0.22/0.53  fof(f422,plain,(
% 0.22/0.53    ( ! [X3] : (~r2_orders_2(sK0,sK1,sK2) | ~r2_hidden(sK2,X3) | ~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(X3,sK0)) ) | spl6_3),
% 0.22/0.53    inference(subsumption_resolution,[],[f40,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ~r1_orders_2(sK0,sK2,sK1) | spl6_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f82])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X3] : (r1_orders_2(sK0,sK2,sK1) | ~r2_orders_2(sK0,sK1,sK2) | ~r2_hidden(sK2,X3) | ~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(X3,sK0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  % (32184)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  fof(f454,plain,(
% 0.22/0.53    ~spl6_2 | spl6_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f453])).
% 0.22/0.53  fof(f453,plain,(
% 0.22/0.53    $false | (~spl6_2 | spl6_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f452,f28])).
% 0.22/0.53  fof(f452,plain,(
% 0.22/0.53    ~l1_orders_2(sK0) | (~spl6_2 | spl6_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f451,f29])).
% 0.22/0.53  fof(f451,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | (~spl6_2 | spl6_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f450,f30])).
% 0.22/0.53  fof(f450,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | (~spl6_2 | spl6_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f443,f79])).
% 0.22/0.53  fof(f443,plain,(
% 0.22/0.53    ~r2_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | spl6_7),
% 0.22/0.53    inference(resolution,[],[f398,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f398,plain,(
% 0.22/0.53    ~r1_orders_2(sK0,sK1,sK2) | spl6_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f397])).
% 0.22/0.53  fof(f421,plain,(
% 0.22/0.53    spl6_2 | spl6_3 | ~spl6_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f416])).
% 0.22/0.53  fof(f416,plain,(
% 0.22/0.53    $false | (spl6_2 | spl6_3 | ~spl6_7)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f28,f29,f30,f399,f80,f415,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (sQ5_eqProxy(X1,X2) | r2_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(equality_proxy_replacement,[],[f43,f55])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f415,plain,(
% 0.22/0.53    ~sQ5_eqProxy(sK1,sK2) | (spl6_3 | ~spl6_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f414,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sQ5_eqProxy(X1,X0) | ~sQ5_eqProxy(X0,X1)) )),
% 0.22/0.53    inference(equality_proxy_axiom,[],[f55])).
% 0.22/0.53  fof(f414,plain,(
% 0.22/0.53    ~sQ5_eqProxy(sK2,sK1) | ~sQ5_eqProxy(sK1,sK2) | (spl6_3 | ~spl6_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f413,f69])).
% 0.22/0.53  fof(f413,plain,(
% 0.22/0.53    ~sQ5_eqProxy(sK2,sK1) | ~sQ5_eqProxy(sK1,sK2) | ~sQ5_eqProxy(sK0,sK0) | (spl6_3 | ~spl6_7)),
% 0.22/0.53    inference(resolution,[],[f399,f370])).
% 0.22/0.53  fof(f370,plain,(
% 0.22/0.53    ( ! [X2,X3,X1] : (~r1_orders_2(X3,X1,X2) | ~sQ5_eqProxy(X2,sK1) | ~sQ5_eqProxy(X1,sK2) | ~sQ5_eqProxy(X3,sK0)) ) | spl6_3),
% 0.22/0.53    inference(resolution,[],[f84,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (r1_orders_2(X1,X3,X5) | ~sQ5_eqProxy(X2,X3) | ~sQ5_eqProxy(X4,X5) | ~r1_orders_2(X0,X2,X4) | ~sQ5_eqProxy(X0,X1)) )),
% 0.22/0.53    inference(equality_proxy_axiom,[],[f55])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ~r2_orders_2(sK0,sK1,sK2) | spl6_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f78])).
% 0.22/0.53  fof(f407,plain,(
% 0.22/0.53    ~spl6_1 | spl6_2 | spl6_3 | spl6_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f402])).
% 0.22/0.53  fof(f402,plain,(
% 0.22/0.53    $false | (~spl6_1 | spl6_2 | spl6_3 | spl6_7)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f26,f28,f380,f383,f76,f30,f29,f387,f84,f398,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f387,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_2 | spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f386,f84])).
% 0.22/0.53  fof(f386,plain,(
% 0.22/0.53    r1_orders_2(sK0,sK2,sK1) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f36,f80])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    r2_orders_2(sK0,sK1,sK2) | r1_orders_2(sK0,sK2,sK1) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    v6_orders_2(sK3,sK0) | ~spl6_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    spl6_1 <=> v6_orders_2(sK3,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.53  fof(f383,plain,(
% 0.22/0.53    r2_hidden(sK2,sK3) | (spl6_2 | spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f382,f84])).
% 0.22/0.53  fof(f382,plain,(
% 0.22/0.53    r1_orders_2(sK0,sK2,sK1) | r2_hidden(sK2,sK3) | spl6_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f38,f80])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    r2_orders_2(sK0,sK1,sK2) | r1_orders_2(sK0,sK2,sK1) | r2_hidden(sK2,sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f380,plain,(
% 0.22/0.53    r2_hidden(sK1,sK3) | (spl6_2 | spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f379,f84])).
% 0.22/0.53  fof(f379,plain,(
% 0.22/0.53    r1_orders_2(sK0,sK2,sK1) | r2_hidden(sK1,sK3) | spl6_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f37,f80])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    r2_orders_2(sK0,sK1,sK2) | r1_orders_2(sK0,sK2,sK1) | r2_hidden(sK1,sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    spl6_2 | ~spl6_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f168])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    $false | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f167,f83])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    ~r1_orders_2(sK0,sK2,sK1) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f166,f30])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK1) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f156,f29])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK1) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(resolution,[],[f147,f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(X1,sK4(sK0,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f109,f28])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_hidden(X1,sK4(sK0,X0,X1))) )),
% 0.22/0.53    inference(resolution,[],[f51,f26])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(X2,sK4(X0,X1,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    ~r2_hidden(sK1,sK4(sK0,sK2,sK1)) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f143,f29])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    ~r2_hidden(sK1,sK4(sK0,sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(resolution,[],[f142,f83])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    ( ! [X1] : (~r1_orders_2(sK0,sK2,X1) | ~r2_hidden(sK1,sK4(sK0,sK2,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f141,f26])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK4(sK0,sK2,X1)) | ~r1_orders_2(sK0,sK2,X1) | ~v3_orders_2(sK0)) ) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f140,f28])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK4(sK0,sK2,X1)) | ~r1_orders_2(sK0,sK2,X1) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0)) ) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f135,f30])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK4(sK0,sK2,X1)) | ~r1_orders_2(sK0,sK2,X1) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0)) ) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f134])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK4(sK0,sK2,X1)) | ~r1_orders_2(sK0,sK2,X1) | ~r1_orders_2(sK0,sK2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0)) ) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(resolution,[],[f132,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v6_orders_2(sK4(X0,X1,X2),X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    ( ! [X0] : (~v6_orders_2(sK4(sK0,sK2,X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK4(sK0,sK2,X0)) | ~r1_orders_2(sK0,sK2,X0)) ) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f131,f26])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | ~r2_hidden(sK1,sK4(sK0,sK2,X0)) | ~v6_orders_2(sK4(sK0,sK2,X0),sK0)) ) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f130,f28])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | ~r2_hidden(sK1,sK4(sK0,sK2,X0)) | ~v6_orders_2(sK4(sK0,sK2,X0),sK0)) ) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f129,f30])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | ~r2_hidden(sK1,sK4(sK0,sK2,X0)) | ~v6_orders_2(sK4(sK0,sK2,X0),sK0)) ) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f128])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | ~r1_orders_2(sK0,sK2,X0) | ~r2_hidden(sK1,sK4(sK0,sK2,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v6_orders_2(sK4(sK0,sK2,X0),sK0)) ) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(resolution,[],[f47,f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(sK4(sK0,sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_orders_2(sK0,sK2,X0) | ~r2_hidden(sK1,sK4(sK0,sK2,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v6_orders_2(sK4(sK0,sK2,X0),sK0)) ) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f98,f30])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X0) | ~r2_hidden(sK1,sK4(sK0,sK2,X0)) | ~m1_subset_1(sK4(sK0,sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(sK4(sK0,sK2,X0),sK0)) ) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(resolution,[],[f97,f92])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ( ! [X3] : (~r2_hidden(sK2,X3) | ~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(X3,sK0)) ) | (spl6_2 | ~spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f91,f80])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ( ! [X3] : (r2_orders_2(sK0,sK1,sK2) | ~r2_hidden(sK2,X3) | ~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(X3,sK0)) ) | ~spl6_3),
% 0.22/0.53    inference(subsumption_resolution,[],[f39,f83])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X3] : (~r1_orders_2(sK0,sK2,sK1) | r2_orders_2(sK0,sK1,sK2) | ~r2_hidden(sK2,X3) | ~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v6_orders_2(X3,sK0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(X0,sK4(sK0,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f95,f28])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_hidden(X0,sK4(sK0,X0,X1))) )),
% 0.22/0.53    inference(resolution,[],[f49,f26])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(X1,sK4(X0,X1,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl6_1 | spl6_2 | spl6_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    $false | (spl6_1 | spl6_2 | spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f87,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ~v6_orders_2(sK3,sK0) | spl6_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f74])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    v6_orders_2(sK3,sK0) | (spl6_2 | spl6_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f86,f84])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    r1_orders_2(sK0,sK2,sK1) | v6_orders_2(sK3,sK0) | spl6_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f35,f80])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    r2_orders_2(sK0,sK1,sK2) | r1_orders_2(sK0,sK2,sK1) | v6_orders_2(sK3,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (32194)------------------------------
% 0.22/0.53  % (32194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32194)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (32194)Memory used [KB]: 6524
% 0.22/0.53  % (32194)Time elapsed: 0.065 s
% 0.22/0.53  % (32194)------------------------------
% 0.22/0.53  % (32194)------------------------------
% 0.22/0.53  % (32179)Success in time 0.174 s
%------------------------------------------------------------------------------
