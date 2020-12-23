%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1643+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 375 expanded)
%              Number of leaves         :   30 ( 156 expanded)
%              Depth                    :   10
%              Number of atoms          :  637 (2261 expanded)
%              Number of equality atoms :   14 (  44 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (2629)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f851,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f82,f131,f146,f167,f168,f169,f170,f171,f175,f181,f284,f289,f294,f468,f693,f710,f838,f850])).

% (2621)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f850,plain,
    ( ~ spl9_3
    | ~ spl9_4
    | ~ spl9_10
    | spl9_15
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f844,f78,f173,f148,f104,f100])).

fof(f100,plain,
    ( spl9_3
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f104,plain,
    ( spl9_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f148,plain,
    ( spl9_10
  <=> m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f173,plain,
    ( spl9_15
  <=> ! [X1,X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f78,plain,
    ( spl9_2
  <=> r1_tarski(k3_waybel_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f844,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_2 ),
    inference(resolution,[],[f144,f62])).

fof(f62,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r1_orders_2(X0,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r1_orders_2(X0,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ( ( ! [X4] :
                          ( ~ r2_hidden(X4,X1)
                          | ~ r1_orders_2(X0,sK4(X0,X1,X2),X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r2_hidden(sK4(X0,X1,X2),X2) )
                    & ( ( r2_hidden(sK5(X0,X1,X2),X1)
                        & r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2))
                        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                      | r2_hidden(sK4(X0,X1,X2),X2) )
                    & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ! [X7] :
                              ( ~ r2_hidden(X7,X1)
                              | ~ r1_orders_2(X0,X6,X7)
                              | ~ m1_subset_1(X7,u1_struct_0(X0)) ) )
                        & ( ( r2_hidden(sK6(X0,X1,X6),X1)
                            & r1_orders_2(X0,X6,sK6(X0,X1,X6))
                            & m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X0)) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r1_orders_2(X0,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r1_orders_2(X0,X3,X5)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r1_orders_2(X0,sK4(X0,X1,X2),X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r1_orders_2(X0,sK4(X0,X1,X2),X5)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | r2_hidden(sK4(X0,X1,X2),X2) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r1_orders_2(X0,sK4(X0,X1,X2),X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r1_orders_2(X0,sK4(X0,X1,X2),sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r1_orders_2(X0,X6,X8)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( r2_hidden(sK6(X0,X1,X6),X1)
        & r1_orders_2(X0,X6,sK6(X0,X1,X6))
        & m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

% (2630)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X3,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r1_orders_2(X0,X3,X5)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ! [X7] :
                              ( ~ r2_hidden(X7,X1)
                              | ~ r1_orders_2(X0,X6,X7)
                              | ~ m1_subset_1(X7,u1_struct_0(X0)) ) )
                        & ( ? [X8] :
                              ( r2_hidden(X8,X1)
                              & r1_orders_2(X0,X6,X8)
                              & m1_subset_1(X8,u1_struct_0(X0)) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X3,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X4] :
                            ( r2_hidden(X4,X1)
                            & r1_orders_2(X0,X3,X4)
                            & m1_subset_1(X4,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ! [X4] :
                              ( ~ r2_hidden(X4,X1)
                              | ~ r1_orders_2(X0,X3,X4)
                              | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
                        & ( ? [X4] :
                              ( r2_hidden(X4,X1)
                              & r1_orders_2(X0,X3,X4)
                              & m1_subset_1(X4,u1_struct_0(X0)) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X3,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X4] :
                            ( r2_hidden(X4,X1)
                            & r1_orders_2(X0,X3,X4)
                            & m1_subset_1(X4,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ! [X4] :
                              ( ~ r2_hidden(X4,X1)
                              | ~ r1_orders_2(X0,X3,X4)
                              | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
                        & ( ? [X4] :
                              ( r2_hidden(X4,X1)
                              & r1_orders_2(X0,X3,X4)
                              & m1_subset_1(X4,u1_struct_0(X0)) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

% (2625)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_waybel_0)).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | r2_hidden(X0,sK1) )
    | ~ spl9_2 ),
    inference(resolution,[],[f79,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f79,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f838,plain,
    ( spl9_9
    | ~ spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_8
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f826,f173,f123,f108,f113,f118,f128])).

fof(f128,plain,
    ( spl9_9
  <=> r2_hidden(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f118,plain,
    ( spl9_7
  <=> r2_hidden(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f113,plain,
    ( spl9_6
  <=> m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f108,plain,
    ( spl9_5
  <=> m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f123,plain,
    ( spl9_8
  <=> r1_orders_2(sK0,sK3(sK0,sK1),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f826,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK2(sK0,sK1),sK1)
    | r2_hidden(sK3(sK0,sK1),sK1)
    | ~ spl9_8
    | ~ spl9_15 ),
    inference(resolution,[],[f125,f174])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1)
        | r2_hidden(X0,sK1) )
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f125,plain,
    ( r1_orders_2(sK0,sK3(sK0,sK1),sK2(sK0,sK1))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f710,plain,
    ( spl9_2
    | ~ spl9_87 ),
    inference(avatar_contradiction_clause,[],[f702])).

fof(f702,plain,
    ( $false
    | spl9_2
    | ~ spl9_87 ),
    inference(resolution,[],[f692,f178])).

fof(f178,plain,
    ( ~ r2_hidden(sK7(k3_waybel_0(sK0,sK1),sK1),sK1)
    | spl9_2 ),
    inference(resolution,[],[f80,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,
    ( ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f692,plain,
    ( r2_hidden(sK7(k3_waybel_0(sK0,sK1),sK1),sK1)
    | ~ spl9_87 ),
    inference(avatar_component_clause,[],[f690])).

fof(f690,plain,
    ( spl9_87
  <=> r2_hidden(sK7(k3_waybel_0(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).

fof(f693,plain,
    ( spl9_87
    | ~ spl9_31
    | ~ spl9_28
    | ~ spl9_29
    | ~ spl9_15
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f682,f286,f173,f281,f277,f291,f690])).

fof(f291,plain,
    ( spl9_31
  <=> r2_hidden(sK6(sK0,sK1,sK7(k3_waybel_0(sK0,sK1),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f277,plain,
    ( spl9_28
  <=> m1_subset_1(sK7(k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f281,plain,
    ( spl9_29
  <=> m1_subset_1(sK6(sK0,sK1,sK7(k3_waybel_0(sK0,sK1),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f286,plain,
    ( spl9_30
  <=> r1_orders_2(sK0,sK7(k3_waybel_0(sK0,sK1),sK1),sK6(sK0,sK1,sK7(k3_waybel_0(sK0,sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f682,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK7(k3_waybel_0(sK0,sK1),sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK6(sK0,sK1,sK7(k3_waybel_0(sK0,sK1),sK1)),sK1)
    | r2_hidden(sK7(k3_waybel_0(sK0,sK1),sK1),sK1)
    | ~ spl9_15
    | ~ spl9_30 ),
    inference(resolution,[],[f288,f174])).

fof(f288,plain,
    ( r1_orders_2(sK0,sK7(k3_waybel_0(sK0,sK1),sK1),sK6(sK0,sK1,sK7(k3_waybel_0(sK0,sK1),sK1)))
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f286])).

fof(f468,plain,
    ( spl9_28
    | spl9_2
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f462,f148,f78,f277])).

fof(f462,plain,
    ( m1_subset_1(sK7(k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | spl9_2
    | ~ spl9_10 ),
    inference(resolution,[],[f211,f177])).

fof(f177,plain,
    ( r2_hidden(sK7(k3_waybel_0(sK0,sK1),sK1),k3_waybel_0(sK0,sK1))
    | spl9_2 ),
    inference(resolution,[],[f80,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f211,plain,
    ( ! [X12] :
        ( ~ r2_hidden(X12,k3_waybel_0(sK0,sK1))
        | m1_subset_1(X12,u1_struct_0(sK0)) )
    | ~ spl9_10 ),
    inference(resolution,[],[f149,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f149,plain,
    ( m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f148])).

fof(f294,plain,
    ( ~ spl9_3
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_28
    | spl9_31
    | spl9_2 ),
    inference(avatar_split_clause,[],[f271,f78,f291,f277,f148,f104,f100])).

fof(f271,plain,
    ( r2_hidden(sK6(sK0,sK1,sK7(k3_waybel_0(sK0,sK1),sK1)),sK1)
    | ~ m1_subset_1(sK7(k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl9_2 ),
    inference(resolution,[],[f177,f63])).

fof(f63,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f289,plain,
    ( ~ spl9_3
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_28
    | spl9_30
    | spl9_2 ),
    inference(avatar_split_clause,[],[f270,f78,f286,f277,f148,f104,f100])).

fof(f270,plain,
    ( r1_orders_2(sK0,sK7(k3_waybel_0(sK0,sK1),sK1),sK6(sK0,sK1,sK7(k3_waybel_0(sK0,sK1),sK1)))
    | ~ m1_subset_1(sK7(k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl9_2 ),
    inference(resolution,[],[f177,f64])).

fof(f64,plain,(
    ! [X6,X0,X1] :
      ( r1_orders_2(X0,X6,sK6(X0,X1,X6))
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X6,sK6(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f284,plain,
    ( ~ spl9_3
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_28
    | spl9_29
    | spl9_2 ),
    inference(avatar_split_clause,[],[f269,f78,f281,f277,f148,f104,f100])).

fof(f269,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK7(k3_waybel_0(sK0,sK1),sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl9_2 ),
    inference(resolution,[],[f177,f65])).

fof(f65,plain,(
    ! [X6,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X6,X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f181,plain,(
    spl9_4 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl9_4 ),
    inference(resolution,[],[f106,f39])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1)
      | ~ v12_waybel_0(sK1,sK0) )
    & ( r1_tarski(k3_waybel_0(sK0,sK1),sK1)
      | v12_waybel_0(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(k3_waybel_0(X0,X1),X1)
              | ~ v12_waybel_0(X1,X0) )
            & ( r1_tarski(k3_waybel_0(X0,X1),X1)
              | v12_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(k3_waybel_0(sK0,X1),X1)
            | ~ v12_waybel_0(X1,sK0) )
          & ( r1_tarski(k3_waybel_0(sK0,X1),X1)
            | v12_waybel_0(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(k3_waybel_0(sK0,X1),X1)
          | ~ v12_waybel_0(X1,sK0) )
        & ( r1_tarski(k3_waybel_0(sK0,X1),X1)
          | v12_waybel_0(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1)
        | ~ v12_waybel_0(sK1,sK0) )
      & ( r1_tarski(k3_waybel_0(sK0,sK1),sK1)
        | v12_waybel_0(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(k3_waybel_0(X0,X1),X1)
            | ~ v12_waybel_0(X1,X0) )
          & ( r1_tarski(k3_waybel_0(X0,X1),X1)
            | v12_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(k3_waybel_0(X0,X1),X1)
            | ~ v12_waybel_0(X1,X0) )
          & ( r1_tarski(k3_waybel_0(X0,X1),X1)
            | v12_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v12_waybel_0(X1,X0)
          <~> r1_tarski(k3_waybel_0(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v12_waybel_0(X1,X0)
            <=> r1_tarski(k3_waybel_0(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> r1_tarski(k3_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_0)).

fof(f106,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl9_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f175,plain,
    ( ~ spl9_3
    | ~ spl9_1
    | spl9_15 ),
    inference(avatar_split_clause,[],[f132,f173,f74,f100])).

fof(f74,plain,
    ( spl9_1
  <=> v12_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f132,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK1)
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f39,f42])).

% (2607)Refutation not found, incomplete strategy% (2607)------------------------------
% (2607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2607)Termination reason: Refutation not found, incomplete strategy

% (2607)Memory used [KB]: 10746
% (2607)Time elapsed: 0.118 s
% (2607)------------------------------
% (2607)------------------------------
fof(f42,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X5,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r1_orders_2(X0,sK3(X0,X1),sK2(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X3,X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,X3,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X3,sK2(X0,X1))
          & r2_hidden(sK2(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,sK3(X0,X1),sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X3,X2)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_waybel_0)).

fof(f171,plain,
    ( ~ spl9_3
    | spl9_5
    | spl9_1 ),
    inference(avatar_split_clause,[],[f133,f74,f108,f100])).

fof(f133,plain,
    ( v12_waybel_0(sK1,sK0)
    | m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f39,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f170,plain,
    ( ~ spl9_3
    | spl9_6
    | spl9_1 ),
    inference(avatar_split_clause,[],[f134,f74,f113,f100])).

fof(f134,plain,
    ( v12_waybel_0(sK1,sK0)
    | m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f39,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f169,plain,
    ( ~ spl9_3
    | spl9_7
    | spl9_1 ),
    inference(avatar_split_clause,[],[f135,f74,f118,f100])).

fof(f135,plain,
    ( v12_waybel_0(sK1,sK0)
    | r2_hidden(sK2(sK0,sK1),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f39,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f168,plain,
    ( ~ spl9_3
    | spl9_8
    | spl9_1 ),
    inference(avatar_split_clause,[],[f136,f74,f123,f100])).

fof(f136,plain,
    ( v12_waybel_0(sK1,sK0)
    | r1_orders_2(sK0,sK3(sK0,sK1),sK2(sK0,sK1))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f39,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | r1_orders_2(X0,sK3(X0,X1),sK2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f167,plain,
    ( ~ spl9_3
    | spl9_10 ),
    inference(avatar_split_clause,[],[f138,f148,f100])).

fof(f138,plain,
    ( m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f39,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_waybel_0)).

fof(f146,plain,(
    spl9_3 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl9_3 ),
    inference(resolution,[],[f102,f38])).

fof(f38,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f102,plain,
    ( ~ l1_orders_2(sK0)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f131,plain,
    ( ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9
    | spl9_1 ),
    inference(avatar_split_clause,[],[f98,f74,f128,f104,f100])).

fof(f98,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl9_1 ),
    inference(resolution,[],[f76,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f82,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f40,f78,f74])).

fof(f40,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f81,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f41,f78,f74])).

fof(f41,plain,
    ( ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | ~ v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
