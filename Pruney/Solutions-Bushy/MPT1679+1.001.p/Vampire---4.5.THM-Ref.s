%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1679+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  222 (1452 expanded)
%              Number of leaves         :   25 ( 576 expanded)
%              Depth                    :   34
%              Number of atoms          : 1527 (25495 expanded)
%              Number of equality atoms :   98 (4634 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (29175)Refutation not found, incomplete strategy% (29175)------------------------------
% (29175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29175)Termination reason: Refutation not found, incomplete strategy

% (29175)Memory used [KB]: 10746
% (29175)Time elapsed: 0.105 s
% (29175)------------------------------
% (29175)------------------------------
fof(f479,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f178,f186,f197,f216,f232,f235,f238,f325,f342,f404,f478])).

fof(f478,plain,
    ( ~ spl11_2
    | spl11_8
    | spl11_9
    | ~ spl11_10 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | ~ spl11_2
    | spl11_8
    | spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f476,f375])).

fof(f375,plain,
    ( m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl11_10 ),
    inference(resolution,[],[f365,f46])).

fof(f46,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k2_yellow_0(sK2,sK3) != k2_yellow_0(sK2,sK4)
    & r2_yellow_0(sK2,sK3)
    & ! [X3] :
        ( r2_hidden(k2_yellow_0(sK2,X3),sK4)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3) )
    & ! [X4] :
        ( ( k2_yellow_0(sK2,sK5(X4)) = X4
          & r2_yellow_0(sK2,sK5(X4))
          & m1_subset_1(sK5(X4),k1_zfmisc_1(sK3))
          & v1_finset_1(sK5(X4)) )
        | ~ r2_hidden(X4,sK4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
    & ! [X6] :
        ( r2_yellow_0(sK2,X6)
        | k1_xboole_0 = X6
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X6) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f10,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
                & r2_yellow_0(X0,X1)
                & ! [X3] :
                    ( r2_hidden(k2_yellow_0(X0,X3),X2)
                    | k1_xboole_0 = X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X3) )
                & ! [X4] :
                    ( ? [X5] :
                        ( k2_yellow_0(X0,X5) = X4
                        & r2_yellow_0(X0,X5)
                        & m1_subset_1(X5,k1_zfmisc_1(X1))
                        & v1_finset_1(X5) )
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & ! [X6] :
                    ( r2_yellow_0(X0,X6)
                    | k1_xboole_0 = X6
                    | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X6) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(sK2,X1) != k2_yellow_0(sK2,X2)
              & r2_yellow_0(sK2,X1)
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(sK2,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(sK2,X5) = X4
                      & r2_yellow_0(sK2,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
              & ! [X6] :
                  ( r2_yellow_0(sK2,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_yellow_0(sK2,X1) != k2_yellow_0(sK2,X2)
            & r2_yellow_0(sK2,X1)
            & ! [X3] :
                ( r2_hidden(k2_yellow_0(sK2,X3),X2)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            & ! [X4] :
                ( ? [X5] :
                    ( k2_yellow_0(sK2,X5) = X4
                    & r2_yellow_0(sK2,X5)
                    & m1_subset_1(X5,k1_zfmisc_1(X1))
                    & v1_finset_1(X5) )
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
            & ! [X6] :
                ( r2_yellow_0(sK2,X6)
                | k1_xboole_0 = X6
                | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X6) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X2] :
          ( k2_yellow_0(sK2,X2) != k2_yellow_0(sK2,sK3)
          & r2_yellow_0(sK2,sK3)
          & ! [X3] :
              ( r2_hidden(k2_yellow_0(sK2,X3),X2)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
              | ~ v1_finset_1(X3) )
          & ! [X4] :
              ( ? [X5] :
                  ( k2_yellow_0(sK2,X5) = X4
                  & r2_yellow_0(sK2,X5)
                  & m1_subset_1(X5,k1_zfmisc_1(sK3))
                  & v1_finset_1(X5) )
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
          & ! [X6] :
              ( r2_yellow_0(sK2,X6)
              | k1_xboole_0 = X6
              | ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
              | ~ v1_finset_1(X6) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( k2_yellow_0(sK2,X2) != k2_yellow_0(sK2,sK3)
        & r2_yellow_0(sK2,sK3)
        & ! [X3] :
            ( r2_hidden(k2_yellow_0(sK2,X3),X2)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
            | ~ v1_finset_1(X3) )
        & ! [X4] :
            ( ? [X5] :
                ( k2_yellow_0(sK2,X5) = X4
                & r2_yellow_0(sK2,X5)
                & m1_subset_1(X5,k1_zfmisc_1(sK3))
                & v1_finset_1(X5) )
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
        & ! [X6] :
            ( r2_yellow_0(sK2,X6)
            | k1_xboole_0 = X6
            | ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
            | ~ v1_finset_1(X6) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( k2_yellow_0(sK2,sK3) != k2_yellow_0(sK2,sK4)
      & r2_yellow_0(sK2,sK3)
      & ! [X3] :
          ( r2_hidden(k2_yellow_0(sK2,X3),sK4)
          | k1_xboole_0 = X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
          | ~ v1_finset_1(X3) )
      & ! [X4] :
          ( ? [X5] :
              ( k2_yellow_0(sK2,X5) = X4
              & r2_yellow_0(sK2,X5)
              & m1_subset_1(X5,k1_zfmisc_1(sK3))
              & v1_finset_1(X5) )
          | ~ r2_hidden(X4,sK4)
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      & ! [X6] :
          ( r2_yellow_0(sK2,X6)
          | k1_xboole_0 = X6
          | ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
          | ~ v1_finset_1(X6) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X4] :
      ( ? [X5] :
          ( k2_yellow_0(sK2,X5) = X4
          & r2_yellow_0(sK2,X5)
          & m1_subset_1(X5,k1_zfmisc_1(sK3))
          & v1_finset_1(X5) )
     => ( k2_yellow_0(sK2,sK5(X4)) = X4
        & r2_yellow_0(sK2,sK5(X4))
        & m1_subset_1(sK5(X4),k1_zfmisc_1(sK3))
        & v1_finset_1(sK5(X4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
              & r2_yellow_0(X0,X1)
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
              & r2_yellow_0(X0,X1)
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r2_yellow_0(X0,X1)
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k2_yellow_0(X0,X5) = X4
                                    & r2_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r2_yellow_0(X0,X6) ) ) )
                 => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ) ) ),
    inference(rectify,[],[f6])).

% (29169)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r2_yellow_0(X0,X1)
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( ! [X4] :
                                ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                  & v1_finset_1(X4) )
                               => ~ ( k2_yellow_0(X0,X4) = X3
                                    & r2_yellow_0(X0,X4) ) )
                            & r2_hidden(X3,X2) ) )
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_yellow_0(X0,X3) ) ) )
                 => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r2_yellow_0(X0,X1)
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k2_yellow_0(X0,X4) = X3
                                  & r2_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_yellow_0(X0,X3) ) ) )
               => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_waybel_0)).

fof(f365,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
        | m1_subset_1(sK8(sK2,sK3,sK4),X0) )
    | ~ spl11_10 ),
    inference(resolution,[],[f177,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f177,plain,
    ( r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl11_10
  <=> r2_hidden(sK8(sK2,sK3,sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f476,plain,
    ( ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl11_2
    | spl11_8
    | spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f475,f177])).

fof(f475,plain,
    ( ~ r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl11_2
    | spl11_8
    | spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f474,f45])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f474,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl11_2
    | spl11_8
    | spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f473,f172])).

fof(f172,plain,
    ( ~ sP0(sK2,sK3)
    | spl11_9 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl11_9
  <=> sP0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f473,plain,
    ( sP0(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl11_2
    | spl11_8
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f472,f168])).

fof(f168,plain,
    ( ~ sP1(sK4,sK2,sK3)
    | spl11_8 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl11_8
  <=> sP1(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f472,plain,
    ( sP1(sK4,sK2,sK3)
    | sP0(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl11_2
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f471,f387])).

fof(f387,plain,
    ( r2_yellow_0(sK2,sK5(sK8(sK2,sK3,sK4)))
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f363,f375])).

fof(f363,plain,
    ( r2_yellow_0(sK2,sK5(sK8(sK2,sK3,sK4)))
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl11_10 ),
    inference(resolution,[],[f177,f50])).

fof(f50,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK4)
      | r2_yellow_0(sK2,sK5(X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f471,plain,
    ( ~ r2_yellow_0(sK2,sK5(sK8(sK2,sK3,sK4)))
    | sP1(sK4,sK2,sK3)
    | sP0(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f470,f437])).

fof(f437,plain,
    ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f436,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f436,plain,
    ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | v2_struct_0(sK2)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f435,f44])).

fof(f44,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f435,plain,
    ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f434,f53])).

fof(f53,plain,(
    r2_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f434,plain,
    ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f429,f74])).

fof(f74,plain,(
    ~ sQ10_eqProxy(k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,sK4)) ),
    inference(equality_proxy_replacement,[],[f54,f73])).

fof(f73,plain,(
    ! [X1,X0] :
      ( sQ10_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).

fof(f54,plain,(
    k2_yellow_0(sK2,sK3) != k2_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f429,plain,
    ( sQ10_eqProxy(k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,sK4))
    | ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2 ),
    inference(resolution,[],[f109,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,sK9(X0,X1,X2))
      | sQ10_eqProxy(k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
      | ~ r1_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f72,f73])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X2,sK9(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ( ( ~ r1_lattice3(X0,X2,sK9(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK9(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK9(X0,X1,X2))
              | r1_lattice3(X0,X1,sK9(X0,X1,X2)) )
            & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK9(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK9(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK9(X0,X1,X2))
          | r1_lattice3(X0,X1,sK9(X0,X1,X2)) )
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) )
            & r2_yellow_0(X0,X1) )
         => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_yellow_0)).

fof(f109,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl11_2
  <=> r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f470,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ r2_yellow_0(sK2,sK5(sK8(sK2,sK3,sK4)))
    | sP1(sK4,sK2,sK3)
    | sP0(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl11_2 ),
    inference(resolution,[],[f469,f49])).

fof(f49,plain,(
    ! [X4] :
      ( m1_subset_1(sK5(X4),k1_zfmisc_1(sK3))
      | ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f469,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK8(sK2,X0,sK4)),k1_zfmisc_1(X0))
        | r1_lattice3(sK2,X0,sK9(sK2,sK3,sK4))
        | ~ r2_yellow_0(sK2,sK5(sK8(sK2,X0,sK4)))
        | sP1(sK4,sK2,X0)
        | sP0(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f468,f449])).

fof(f449,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP1(sK4,sK2,X7)
        | m1_subset_1(sK8(sK2,X7,sK4),u1_struct_0(sK2))
        | sP0(sK2,X7)
        | r1_lattice3(sK2,X7,sK9(sK2,sK3,sK4)) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f448,f41])).

fof(f448,plain,
    ( ! [X7] :
        ( r1_lattice3(sK2,X7,sK9(sK2,sK3,sK4))
        | sP1(sK4,sK2,X7)
        | m1_subset_1(sK8(sK2,X7,sK4),u1_struct_0(sK2))
        | sP0(sK2,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f447,f42])).

fof(f42,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f447,plain,
    ( ! [X7] :
        ( r1_lattice3(sK2,X7,sK9(sK2,sK3,sK4))
        | sP1(sK4,sK2,X7)
        | m1_subset_1(sK8(sK2,X7,sK4),u1_struct_0(sK2))
        | sP0(sK2,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f446,f43])).

fof(f43,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f446,plain,
    ( ! [X7] :
        ( r1_lattice3(sK2,X7,sK9(sK2,sK3,sK4))
        | sP1(sK4,sK2,X7)
        | m1_subset_1(sK8(sK2,X7,sK4),u1_struct_0(sK2))
        | sP0(sK2,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f445,f44])).

fof(f445,plain,
    ( ! [X7] :
        ( r1_lattice3(sK2,X7,sK9(sK2,sK3,sK4))
        | sP1(sK4,sK2,X7)
        | m1_subset_1(sK8(sK2,X7,sK4),u1_struct_0(sK2))
        | sP0(sK2,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f444,f46])).

fof(f444,plain,
    ( ! [X7] :
        ( r1_lattice3(sK2,X7,sK9(sK2,sK3,sK4))
        | sP1(sK4,sK2,X7)
        | m1_subset_1(sK8(sK2,X7,sK4),u1_struct_0(sK2))
        | sP0(sK2,X7)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f432,f97])).

fof(f97,plain,(
    m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f96,f41])).

fof(f96,plain,
    ( m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f95,f44])).

fof(f95,plain,
    ( m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f94,f53])).

fof(f94,plain,
    ( m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f84,f74])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( sQ10_eqProxy(k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
      | m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f70,f73])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f432,plain,
    ( ! [X7] :
        ( r1_lattice3(sK2,X7,sK9(sK2,sK3,sK4))
        | ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
        | sP1(sK4,sK2,X7)
        | m1_subset_1(sK8(sK2,X7,sK4),u1_struct_0(sK2))
        | sP0(sK2,X7)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(resolution,[],[f109,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X0,X2,X3)
      | r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_lattice3(X0,X1,X3)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r1_lattice3(X0,X2,X3)
                      | ~ r1_lattice3(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ( ! [X5] :
                    ( k2_yellow_0(X0,X5) != sK8(X0,X1,X2)
                    | ~ r2_yellow_0(X0,X5)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X5) )
                & r2_hidden(sK8(X0,X1,X2),X2)
                & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( k2_yellow_0(X0,X5) != X4
              | ~ r2_yellow_0(X0,X5)
              | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X5) )
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( k2_yellow_0(X0,X5) != sK8(X0,X1,X2)
            | ~ r2_yellow_0(X0,X5)
            | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X5) )
        & r2_hidden(sK8(X0,X1,X2),X2)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_lattice3(X0,X1,X3)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r1_lattice3(X0,X2,X3)
                      | ~ r1_lattice3(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( ( r1_lattice3(X0,X1,X7)
                      | ~ r1_lattice3(X0,X2,X7) )
                    & ( r1_lattice3(X0,X2,X7)
                      | ~ r1_lattice3(X0,X1,X7) ) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <=> r1_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f14,f18,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r2_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X1))
          & v1_finset_1(X3) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <=> r1_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | ? [X3] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
                  & k1_xboole_0 != X3
                  & m1_subset_1(X3,k1_zfmisc_1(X1))
                  & v1_finset_1(X3) )
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ? [X6] :
                  ( ~ r2_yellow_0(X0,X6)
                  & k1_xboole_0 != X6
                  & m1_subset_1(X6,k1_zfmisc_1(X1))
                  & v1_finset_1(X6) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <=> r1_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | ? [X3] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
                  & k1_xboole_0 != X3
                  & m1_subset_1(X3,k1_zfmisc_1(X1))
                  & v1_finset_1(X3) )
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ? [X6] :
                  ( ~ r2_yellow_0(X0,X6)
                  & k1_xboole_0 != X6
                  & m1_subset_1(X6,k1_zfmisc_1(X1))
                  & v1_finset_1(X6) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ~ ( ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                & v1_finset_1(X5) )
                             => ~ ( k2_yellow_0(X0,X5) = X4
                                  & r2_yellow_0(X0,X5) ) )
                          & r2_hidden(X4,X2) ) )
                  & ! [X6] :
                      ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                        & v1_finset_1(X6) )
                     => ( k1_xboole_0 != X6
                       => r2_yellow_0(X0,X6) ) ) )
               => ! [X7] :
                    ( m1_subset_1(X7,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X7)
                    <=> r1_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k2_yellow_0(X0,X4) = X3
                                  & r2_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_yellow_0(X0,X3) ) ) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                    <=> r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_waybel_0)).

fof(f468,plain,
    ( ! [X0] :
        ( sP1(sK4,sK2,X0)
        | r1_lattice3(sK2,X0,sK9(sK2,sK3,sK4))
        | ~ r2_yellow_0(sK2,sK5(sK8(sK2,X0,sK4)))
        | ~ m1_subset_1(sK5(sK8(sK2,X0,sK4)),k1_zfmisc_1(X0))
        | sP0(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK8(sK2,X0,sK4),u1_struct_0(sK2)) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f467,f433])).

fof(f433,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | r2_hidden(sK8(sK2,X1,sK4),sK4)
        | sP0(sK2,X1)
        | sP1(sK4,sK2,X1)
        | r1_lattice3(sK2,X1,sK9(sK2,sK3,sK4)) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f427,f46])).

fof(f427,plain,
    ( ! [X1] :
        ( sP1(sK4,sK2,X1)
        | r2_hidden(sK8(sK2,X1,sK4),sK4)
        | sP0(sK2,X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X1,sK9(sK2,sK3,sK4)) )
    | ~ spl11_2 ),
    inference(resolution,[],[f109,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,X0,sK9(sK2,sK3,sK4))
      | sP1(X0,sK2,X1)
      | r2_hidden(sK8(sK2,X1,X0),X0)
      | sP0(sK2,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X1,sK9(sK2,sK3,sK4)) ) ),
    inference(resolution,[],[f124,f97])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X0,X1)
      | sP1(X0,sK2,X2)
      | r2_hidden(sK8(sK2,X2,X0),X0)
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1) ) ),
    inference(subsumption_resolution,[],[f123,f41])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | r2_hidden(sK8(sK2,X2,X0),X0)
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f122,f42])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | r2_hidden(sK8(sK2,X2,X0),X0)
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f121,f44])).

% (29160)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | r2_hidden(sK8(sK2,X2,X0),X0)
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | r1_lattice3(sK2,X2,X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f68,f43])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | r2_hidden(sK8(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X3)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f467,plain,
    ( ! [X0] :
        ( sP1(sK4,sK2,X0)
        | r1_lattice3(sK2,X0,sK9(sK2,sK3,sK4))
        | ~ r2_yellow_0(sK2,sK5(sK8(sK2,X0,sK4)))
        | ~ m1_subset_1(sK5(sK8(sK2,X0,sK4)),k1_zfmisc_1(X0))
        | sP0(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(sK8(sK2,X0,sK4),sK4)
        | ~ m1_subset_1(sK8(sK2,X0,sK4),u1_struct_0(sK2)) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f466,f48])).

fof(f48,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK4)
      | v1_finset_1(sK5(X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f466,plain,
    ( ! [X0] :
        ( sP1(sK4,sK2,X0)
        | r1_lattice3(sK2,X0,sK9(sK2,sK3,sK4))
        | ~ r2_yellow_0(sK2,sK5(sK8(sK2,X0,sK4)))
        | ~ m1_subset_1(sK5(sK8(sK2,X0,sK4)),k1_zfmisc_1(X0))
        | ~ v1_finset_1(sK5(sK8(sK2,X0,sK4)))
        | sP0(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(sK8(sK2,X0,sK4),sK4)
        | ~ m1_subset_1(sK8(sK2,X0,sK4),u1_struct_0(sK2)) )
    | ~ spl11_2 ),
    inference(resolution,[],[f443,f76])).

fof(f76,plain,(
    ! [X4] :
      ( sQ10_eqProxy(k2_yellow_0(sK2,sK5(X4)),X4)
      | ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(equality_proxy_replacement,[],[f51,f73])).

fof(f51,plain,(
    ! [X4] :
      ( k2_yellow_0(sK2,sK5(X4)) = X4
      | ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f443,plain,
    ( ! [X6,X5] :
        ( ~ sQ10_eqProxy(k2_yellow_0(sK2,X6),sK8(sK2,X5,sK4))
        | sP1(sK4,sK2,X5)
        | r1_lattice3(sK2,X5,sK9(sK2,sK3,sK4))
        | ~ r2_yellow_0(sK2,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
        | ~ v1_finset_1(X6)
        | sP0(sK2,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f442,f41])).

fof(f442,plain,
    ( ! [X6,X5] :
        ( r1_lattice3(sK2,X5,sK9(sK2,sK3,sK4))
        | sP1(sK4,sK2,X5)
        | ~ sQ10_eqProxy(k2_yellow_0(sK2,X6),sK8(sK2,X5,sK4))
        | ~ r2_yellow_0(sK2,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
        | ~ v1_finset_1(X6)
        | sP0(sK2,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f441,f42])).

fof(f441,plain,
    ( ! [X6,X5] :
        ( r1_lattice3(sK2,X5,sK9(sK2,sK3,sK4))
        | sP1(sK4,sK2,X5)
        | ~ sQ10_eqProxy(k2_yellow_0(sK2,X6),sK8(sK2,X5,sK4))
        | ~ r2_yellow_0(sK2,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
        | ~ v1_finset_1(X6)
        | sP0(sK2,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f440,f43])).

fof(f440,plain,
    ( ! [X6,X5] :
        ( r1_lattice3(sK2,X5,sK9(sK2,sK3,sK4))
        | sP1(sK4,sK2,X5)
        | ~ sQ10_eqProxy(k2_yellow_0(sK2,X6),sK8(sK2,X5,sK4))
        | ~ r2_yellow_0(sK2,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
        | ~ v1_finset_1(X6)
        | sP0(sK2,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f439,f44])).

fof(f439,plain,
    ( ! [X6,X5] :
        ( r1_lattice3(sK2,X5,sK9(sK2,sK3,sK4))
        | sP1(sK4,sK2,X5)
        | ~ sQ10_eqProxy(k2_yellow_0(sK2,X6),sK8(sK2,X5,sK4))
        | ~ r2_yellow_0(sK2,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
        | ~ v1_finset_1(X6)
        | sP0(sK2,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f438,f46])).

fof(f438,plain,
    ( ! [X6,X5] :
        ( r1_lattice3(sK2,X5,sK9(sK2,sK3,sK4))
        | sP1(sK4,sK2,X5)
        | ~ sQ10_eqProxy(k2_yellow_0(sK2,X6),sK8(sK2,X5,sK4))
        | ~ r2_yellow_0(sK2,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
        | ~ v1_finset_1(X6)
        | sP0(sK2,X5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f431,f97])).

fof(f431,plain,
    ( ! [X6,X5] :
        ( r1_lattice3(sK2,X5,sK9(sK2,sK3,sK4))
        | ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
        | sP1(sK4,sK2,X5)
        | ~ sQ10_eqProxy(k2_yellow_0(sK2,X6),sK8(sK2,X5,sK4))
        | ~ r2_yellow_0(sK2,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
        | ~ v1_finset_1(X6)
        | sP0(sK2,X5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(resolution,[],[f109,f80])).

fof(f80,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r1_lattice3(X0,X2,X3)
      | r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | ~ sQ10_eqProxy(k2_yellow_0(X0,X5),sK8(X0,X1,X2))
      | ~ r2_yellow_0(X0,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X5)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f69,f73])).

fof(f69,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | k2_yellow_0(X0,X5) != sK8(X0,X1,X2)
      | ~ r2_yellow_0(X0,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X5)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f404,plain,
    ( ~ spl11_1
    | spl11_8
    | spl11_9
    | ~ spl11_10 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | ~ spl11_1
    | spl11_8
    | spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f402,f41])).

fof(f402,plain,
    ( v2_struct_0(sK2)
    | ~ spl11_1
    | spl11_8
    | spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f401,f44])).

fof(f401,plain,
    ( ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_1
    | spl11_8
    | spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f400,f53])).

fof(f400,plain,
    ( ~ r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_1
    | spl11_8
    | spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f399,f105])).

fof(f105,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl11_1
  <=> r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f399,plain,
    ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_1
    | spl11_8
    | spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f394,f74])).

fof(f394,plain,
    ( sQ10_eqProxy(k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,sK4))
    | ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_1
    | spl11_8
    | spl11_9
    | ~ spl11_10 ),
    inference(resolution,[],[f390,f82])).

fof(f390,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | ~ spl11_1
    | spl11_8
    | spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f389,f375])).

fof(f389,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl11_1
    | spl11_8
    | spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f388,f168])).

fof(f388,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | sP1(sK4,sK2,sK3)
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl11_1
    | spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f379,f46])).

fof(f379,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | sP1(sK4,sK2,sK3)
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl11_1
    | spl11_9
    | ~ spl11_10 ),
    inference(resolution,[],[f291,f177])).

fof(f291,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK8(sK2,sK3,X0),sK4)
        | r1_lattice3(sK2,X0,sK9(sK2,sK3,sK4))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP1(X0,sK2,sK3)
        | ~ m1_subset_1(sK8(sK2,sK3,X0),u1_struct_0(sK2)) )
    | ~ spl11_1
    | spl11_9 ),
    inference(subsumption_resolution,[],[f290,f49])).

fof(f290,plain,
    ( ! [X0] :
        ( sP1(X0,sK2,sK3)
        | r1_lattice3(sK2,X0,sK9(sK2,sK3,sK4))
        | ~ m1_subset_1(sK5(sK8(sK2,sK3,X0)),k1_zfmisc_1(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(sK8(sK2,sK3,X0),sK4)
        | ~ m1_subset_1(sK8(sK2,sK3,X0),u1_struct_0(sK2)) )
    | ~ spl11_1
    | spl11_9 ),
    inference(subsumption_resolution,[],[f289,f50])).

fof(f289,plain,
    ( ! [X0] :
        ( sP1(X0,sK2,sK3)
        | r1_lattice3(sK2,X0,sK9(sK2,sK3,sK4))
        | ~ r2_yellow_0(sK2,sK5(sK8(sK2,sK3,X0)))
        | ~ m1_subset_1(sK5(sK8(sK2,sK3,X0)),k1_zfmisc_1(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(sK8(sK2,sK3,X0),sK4)
        | ~ m1_subset_1(sK8(sK2,sK3,X0),u1_struct_0(sK2)) )
    | ~ spl11_1
    | spl11_9 ),
    inference(subsumption_resolution,[],[f288,f48])).

fof(f288,plain,
    ( ! [X0] :
        ( sP1(X0,sK2,sK3)
        | r1_lattice3(sK2,X0,sK9(sK2,sK3,sK4))
        | ~ r2_yellow_0(sK2,sK5(sK8(sK2,sK3,X0)))
        | ~ m1_subset_1(sK5(sK8(sK2,sK3,X0)),k1_zfmisc_1(sK3))
        | ~ v1_finset_1(sK5(sK8(sK2,sK3,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(sK8(sK2,sK3,X0),sK4)
        | ~ m1_subset_1(sK8(sK2,sK3,X0),u1_struct_0(sK2)) )
    | ~ spl11_1
    | spl11_9 ),
    inference(resolution,[],[f251,f76])).

fof(f251,plain,
    ( ! [X2,X3] :
        ( ~ sQ10_eqProxy(k2_yellow_0(sK2,X3),sK8(sK2,sK3,X2))
        | sP1(X2,sK2,sK3)
        | r1_lattice3(sK2,X2,sK9(sK2,sK3,sK4))
        | ~ r2_yellow_0(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl11_1
    | spl11_9 ),
    inference(subsumption_resolution,[],[f250,f41])).

fof(f250,plain,
    ( ! [X2,X3] :
        ( r1_lattice3(sK2,X2,sK9(sK2,sK3,sK4))
        | sP1(X2,sK2,sK3)
        | ~ sQ10_eqProxy(k2_yellow_0(sK2,X3),sK8(sK2,sK3,X2))
        | ~ r2_yellow_0(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | v2_struct_0(sK2) )
    | ~ spl11_1
    | spl11_9 ),
    inference(subsumption_resolution,[],[f249,f42])).

fof(f249,plain,
    ( ! [X2,X3] :
        ( r1_lattice3(sK2,X2,sK9(sK2,sK3,sK4))
        | sP1(X2,sK2,sK3)
        | ~ sQ10_eqProxy(k2_yellow_0(sK2,X3),sK8(sK2,sK3,X2))
        | ~ r2_yellow_0(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_1
    | spl11_9 ),
    inference(subsumption_resolution,[],[f248,f43])).

fof(f248,plain,
    ( ! [X2,X3] :
        ( r1_lattice3(sK2,X2,sK9(sK2,sK3,sK4))
        | sP1(X2,sK2,sK3)
        | ~ sQ10_eqProxy(k2_yellow_0(sK2,X3),sK8(sK2,sK3,X2))
        | ~ r2_yellow_0(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_1
    | spl11_9 ),
    inference(subsumption_resolution,[],[f247,f44])).

fof(f247,plain,
    ( ! [X2,X3] :
        ( r1_lattice3(sK2,X2,sK9(sK2,sK3,sK4))
        | sP1(X2,sK2,sK3)
        | ~ sQ10_eqProxy(k2_yellow_0(sK2,X3),sK8(sK2,sK3,X2))
        | ~ r2_yellow_0(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_1
    | spl11_9 ),
    inference(subsumption_resolution,[],[f246,f45])).

fof(f246,plain,
    ( ! [X2,X3] :
        ( r1_lattice3(sK2,X2,sK9(sK2,sK3,sK4))
        | sP1(X2,sK2,sK3)
        | ~ sQ10_eqProxy(k2_yellow_0(sK2,X3),sK8(sK2,sK3,X2))
        | ~ r2_yellow_0(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_1
    | spl11_9 ),
    inference(subsumption_resolution,[],[f245,f172])).

fof(f245,plain,
    ( ! [X2,X3] :
        ( r1_lattice3(sK2,X2,sK9(sK2,sK3,sK4))
        | sP1(X2,sK2,sK3)
        | ~ sQ10_eqProxy(k2_yellow_0(sK2,X3),sK8(sK2,sK3,X2))
        | ~ r2_yellow_0(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3)
        | sP0(sK2,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f241,f97])).

fof(f241,plain,
    ( ! [X2,X3] :
        ( r1_lattice3(sK2,X2,sK9(sK2,sK3,sK4))
        | ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
        | sP1(X2,sK2,sK3)
        | ~ sQ10_eqProxy(k2_yellow_0(sK2,X3),sK8(sK2,sK3,X2))
        | ~ r2_yellow_0(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3)
        | sP0(sK2,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_1 ),
    inference(resolution,[],[f105,f81])).

fof(f81,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r1_lattice3(X0,X1,X3)
      | r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | ~ sQ10_eqProxy(k2_yellow_0(X0,X5),sK8(X0,X1,X2))
      | ~ r2_yellow_0(X0,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X5)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f66,f73])).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | k2_yellow_0(X0,X5) != sK8(X0,X1,X2)
      | ~ r2_yellow_0(X0,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X5)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f342,plain,
    ( ~ spl11_8
    | ~ spl11_12 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | ~ spl11_8
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f337,f169])).

fof(f169,plain,
    ( sP1(sK4,sK2,sK3)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f167])).

fof(f337,plain,
    ( ~ sP1(sK4,sK2,sK3)
    | ~ spl11_12 ),
    inference(resolution,[],[f192,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X1,sK6(X0,X1,X2)),X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_yellow_0(X1,sK6(X0,X1,X2)),X0)
        & k1_xboole_0 != sK6(X0,X1,X2)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X2))
        & v1_finset_1(sK6(X0,X1,X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X1,X3),X0)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X2))
          & v1_finset_1(X3) )
     => ( ~ r2_hidden(k2_yellow_0(X1,sK6(X0,X1,X2)),X0)
        & k1_xboole_0 != sK6(X0,X1,X2)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X2))
        & v1_finset_1(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X1,X3),X0)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X2))
          & v1_finset_1(X3) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X1))
          & v1_finset_1(X3) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f192,plain,
    ( r2_hidden(k2_yellow_0(sK2,sK6(sK4,sK2,sK3)),sK4)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl11_12
  <=> r2_hidden(k2_yellow_0(sK2,sK6(sK4,sK2,sK3)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f325,plain,
    ( spl11_10
    | spl11_8
    | spl11_2
    | ~ spl11_11 ),
    inference(avatar_split_clause,[],[f299,f184,f107,f167,f175])).

fof(f184,plain,
    ( spl11_11
  <=> ! [X1] :
        ( sP1(X1,sK2,sK3)
        | r1_lattice3(sK2,X1,sK9(sK2,sK3,sK4))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | r2_hidden(sK8(sK2,sK3,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f299,plain,
    ( sP1(sK4,sK2,sK3)
    | r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | spl11_2
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f296,f108])).

fof(f108,plain,
    ( ~ r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | spl11_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f296,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | sP1(sK4,sK2,sK3)
    | r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | ~ spl11_11 ),
    inference(resolution,[],[f185,f46])).

fof(f185,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X1,sK9(sK2,sK3,sK4))
        | sP1(X1,sK2,sK3)
        | r2_hidden(sK8(sK2,sK3,X1),X1) )
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f184])).

fof(f238,plain,
    ( ~ spl11_9
    | ~ spl11_17 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl11_9
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f236,f173])).

fof(f173,plain,
    ( sP0(sK2,sK3)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f171])).

fof(f236,plain,
    ( ~ sP0(sK2,sK3)
    | ~ spl11_17 ),
    inference(resolution,[],[f231,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(X0,sK7(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r2_yellow_0(X0,sK7(X0,X1))
        & k1_xboole_0 != sK7(X0,X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK7(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ~ r2_yellow_0(X0,sK7(X0,X1))
        & k1_xboole_0 != sK7(X0,X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r2_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f231,plain,
    ( r2_yellow_0(sK2,sK7(sK2,sK3))
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl11_17
  <=> r2_yellow_0(sK2,sK7(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f235,plain,
    ( ~ spl11_9
    | spl11_16 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl11_9
    | spl11_16 ),
    inference(subsumption_resolution,[],[f233,f173])).

fof(f233,plain,
    ( ~ sP0(sK2,sK3)
    | spl11_16 ),
    inference(resolution,[],[f226,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),k1_zfmisc_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f226,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3),k1_zfmisc_1(sK3))
    | spl11_16 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl11_16
  <=> m1_subset_1(sK7(sK2,sK3),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f232,plain,
    ( spl11_17
    | ~ spl11_16
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f218,f171,f224,f229])).

fof(f218,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3),k1_zfmisc_1(sK3))
    | r2_yellow_0(sK2,sK7(sK2,sK3))
    | ~ spl11_9 ),
    inference(resolution,[],[f173,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ m1_subset_1(sK7(X0,X1),k1_zfmisc_1(sK3))
      | r2_yellow_0(sK2,sK7(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f86,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_finset_1(sK7(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(sK2,sK7(X0,X1))
      | ~ m1_subset_1(sK7(X0,X1),k1_zfmisc_1(sK3))
      | ~ v1_finset_1(sK7(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f77,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ sQ10_eqProxy(k1_xboole_0,sK7(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f62,f73])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK7(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X6] :
      ( sQ10_eqProxy(k1_xboole_0,X6)
      | r2_yellow_0(sK2,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X6) ) ),
    inference(equality_proxy_replacement,[],[f47,f73])).

fof(f47,plain,(
    ! [X6] :
      ( r2_yellow_0(sK2,X6)
      | k1_xboole_0 = X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X6) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f216,plain,
    ( ~ spl11_8
    | spl11_13 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | ~ spl11_8
    | spl11_13 ),
    inference(subsumption_resolution,[],[f214,f169])).

fof(f214,plain,
    ( ~ sP1(sK4,sK2,sK3)
    | spl11_13 ),
    inference(resolution,[],[f196,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f196,plain,
    ( ~ m1_subset_1(sK6(sK4,sK2,sK3),k1_zfmisc_1(sK3))
    | spl11_13 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl11_13
  <=> m1_subset_1(sK6(sK4,sK2,sK3),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f197,plain,
    ( spl11_12
    | ~ spl11_13
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f187,f167,f194,f190])).

fof(f187,plain,
    ( ~ m1_subset_1(sK6(sK4,sK2,sK3),k1_zfmisc_1(sK3))
    | r2_hidden(k2_yellow_0(sK2,sK6(sK4,sK2,sK3)),sK4)
    | ~ spl11_8 ),
    inference(resolution,[],[f169,f93])).

fof(f93,plain,(
    ! [X4,X2,X3] :
      ( ~ sP1(X2,X3,X4)
      | ~ m1_subset_1(sK6(X2,X3,X4),k1_zfmisc_1(sK3))
      | r2_hidden(k2_yellow_0(sK2,sK6(X2,X3,X4)),sK4) ) ),
    inference(subsumption_resolution,[],[f91,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_finset_1(sK6(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f91,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(k2_yellow_0(sK2,sK6(X2,X3,X4)),sK4)
      | ~ m1_subset_1(sK6(X2,X3,X4),k1_zfmisc_1(sK3))
      | ~ v1_finset_1(sK6(X2,X3,X4))
      | ~ sP1(X2,X3,X4) ) ),
    inference(resolution,[],[f75,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ10_eqProxy(k1_xboole_0,sK6(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_proxy_replacement,[],[f58,f73])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != sK6(X0,X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X3] :
      ( sQ10_eqProxy(k1_xboole_0,X3)
      | r2_hidden(k2_yellow_0(sK2,X3),sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X3) ) ),
    inference(equality_proxy_replacement,[],[f52,f73])).

fof(f52,plain,(
    ! [X3] :
      ( r2_hidden(k2_yellow_0(sK2,X3),sK4)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f186,plain,
    ( spl11_9
    | spl11_11
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f182,f103,f184,f171])).

fof(f182,plain,
    ( ! [X1] :
        ( sP1(X1,sK2,sK3)
        | r2_hidden(sK8(sK2,sK3,X1),X1)
        | sP0(sK2,sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X1,sK9(sK2,sK3,sK4)) )
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f180,f45])).

fof(f180,plain,
    ( ! [X1] :
        ( sP1(X1,sK2,sK3)
        | r2_hidden(sK8(sK2,sK3,X1),X1)
        | sP0(sK2,sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X1,sK9(sK2,sK3,sK4)) )
    | ~ spl11_1 ),
    inference(resolution,[],[f105,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,X0,sK9(sK2,sK3,sK4))
      | sP1(X1,sK2,X0)
      | r2_hidden(sK8(sK2,X0,X1),X1)
      | sP0(sK2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X1,sK9(sK2,sK3,sK4)) ) ),
    inference(resolution,[],[f119,f97])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X0,X1)
      | sP1(X2,sK2,X0)
      | r2_hidden(sK8(sK2,X0,X2),X2)
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1) ) ),
    inference(subsumption_resolution,[],[f118,f41])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | r2_hidden(sK8(sK2,X0,X2),X2)
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f117,f42])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | r2_hidden(sK8(sK2,X0,X2),X2)
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f116,f44])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | r2_hidden(sK8(sK2,X0,X2),X2)
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | r1_lattice3(sK2,X2,X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f65,f43])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | r2_hidden(sK8(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X2,X3)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f178,plain,
    ( spl11_8
    | spl11_9
    | spl11_10
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f165,f107,f175,f171,f167])).

fof(f165,plain,
    ( r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | sP0(sK2,sK3)
    | sP1(sK4,sK2,sK3)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f159,f45])).

fof(f159,plain,
    ( r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | sP0(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | sP1(sK4,sK2,sK3)
    | ~ spl11_2 ),
    inference(resolution,[],[f158,f115])).

fof(f115,plain,
    ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f114,f41])).

fof(f114,plain,
    ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | v2_struct_0(sK2)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f113,f44])).

fof(f113,plain,
    ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f112,f53])).

fof(f112,plain,
    ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f111,f74])).

fof(f111,plain,
    ( sQ10_eqProxy(k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,sK4))
    | ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2 ),
    inference(resolution,[],[f109,f82])).

fof(f158,plain,
    ( ! [X0] :
        ( r1_lattice3(sK2,X0,sK9(sK2,sK3,sK4))
        | r2_hidden(sK8(sK2,X0,sK4),sK4)
        | sP0(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP1(sK4,sK2,X0) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f157,f46])).

fof(f157,plain,
    ( ! [X0] :
        ( sP1(sK4,sK2,X0)
        | r2_hidden(sK8(sK2,X0,sK4),sK4)
        | sP0(sK2,X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X0,sK9(sK2,sK3,sK4)) )
    | ~ spl11_2 ),
    inference(resolution,[],[f125,f109])).

fof(f110,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f101,f107,f103])).

fof(f101,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f100,f41])).

fof(f100,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f99,f44])).

fof(f99,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f98,f53])).

fof(f98,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f83,f74])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( sQ10_eqProxy(k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
      | r1_lattice3(X0,X2,sK9(X0,X1,X2))
      | r1_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f71,f73])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | r1_lattice3(X0,X2,sK9(X0,X1,X2))
      | r1_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

%------------------------------------------------------------------------------
