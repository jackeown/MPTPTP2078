%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t29_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:51 EDT 2019

% Result     : Theorem 11.35s
% Output     : Refutation 11.35s
% Verified   : 
% Statistics : Number of formulae       :  189 (1202 expanded)
%              Number of leaves         :   32 ( 413 expanded)
%              Depth                    :   28
%              Number of atoms          : 1079 (17984 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1306,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f184,f191,f198,f205,f212,f219,f226,f233,f240,f245,f754,f756,f758,f831,f1042,f1305])).

fof(f1305,plain,
    ( spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_88
    | ~ spl11_94 ),
    inference(avatar_contradiction_clause,[],[f1304])).

fof(f1304,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_88
    | ~ spl11_94 ),
    inference(subsumption_resolution,[],[f1303,f183])).

fof(f183,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl11_3
  <=> ~ r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f1303,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_88
    | ~ spl11_94 ),
    inference(subsumption_resolution,[],[f1302,f197])).

fof(f197,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl11_6
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f1302,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK3,sK1)
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_88
    | ~ spl11_94 ),
    inference(resolution,[],[f1265,f190])).

fof(f190,plain,
    ( r1_waybel_7(sK0,sK2,sK3)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl11_4
  <=> r1_waybel_7(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f1265,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl11_8
    | ~ spl11_88
    | ~ spl11_94 ),
    inference(subsumption_resolution,[],[f1264,f204])).

fof(f204,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl11_8
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f1264,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK2,X0)
        | ~ r2_hidden(sK1,sK2) )
    | ~ spl11_88
    | ~ spl11_94 ),
    inference(subsumption_resolution,[],[f1253,f108])).

fof(f108,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,
    ( ( ( ~ r2_hidden(sK3,sK1)
        & r1_waybel_7(sK0,sK2,sK3)
        & m1_subset_1(sK3,u1_struct_0(sK0))
        & r2_hidden(sK1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(sK2) )
      | ~ v4_pre_topc(sK1,sK0) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,sK1)
              | ~ r1_waybel_7(sK0,X4,X5)
              | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
          | ~ r2_hidden(sK1,X4)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
          | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
          | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          | v1_xboole_0(X4) )
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f80,f84,f83,f82,f81])).

fof(f81,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_waybel_7(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  & ~ v1_xboole_0(X2) )
              | ~ v4_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_waybel_7(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X4)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  | v1_xboole_0(X4) )
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r1_waybel_7(sK0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
                & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,sK0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r1_waybel_7(sK0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r1_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r1_waybel_7(X0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X3,sK1)
                  & r1_waybel_7(X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_hidden(sK1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X2) )
          | ~ v4_pre_topc(sK1,X0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,sK1)
                  | ~ r1_waybel_7(X0,X4,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ r2_hidden(sK1,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
              | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
              | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              | v1_xboole_0(X4) )
          | v4_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_waybel_7(X0,X2,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_hidden(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_waybel_7(X0,sK2,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & r2_hidden(X1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_waybel_7(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3,X1)
        & r1_waybel_7(X0,X2,sK3)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r1_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r1_waybel_7(X0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f79])).

fof(f79,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r1_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r1_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X2) )
                 => ( r2_hidden(X1,X2)
                   => ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r1_waybel_7(X0,X2,X3)
                         => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  & ~ v1_xboole_0(X2) )
               => ( r2_hidden(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_waybel_7(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t29_yellow19.p',t29_yellow19)).

fof(f1253,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK2,X0)
        | ~ r2_hidden(sK1,sK2) )
    | ~ spl11_88
    | ~ spl11_94 ),
    inference(superposition,[],[f830,f753])).

fof(f753,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl11_88 ),
    inference(avatar_component_clause,[],[f752])).

fof(f752,plain,
    ( spl11_88
  <=> k2_pre_topc(sK0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_88])])).

fof(f830,plain,
    ( ! [X2,X1] :
        ( r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2) )
    | ~ spl11_94 ),
    inference(avatar_component_clause,[],[f829])).

fof(f829,plain,
    ( spl11_94
  <=> ! [X1,X2] :
        ( ~ r1_waybel_7(sK0,sK2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ r2_hidden(X2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_94])])).

fof(f1042,plain,
    ( ~ spl11_20
    | spl11_87 ),
    inference(avatar_contradiction_clause,[],[f1041])).

fof(f1041,plain,
    ( $false
    | ~ spl11_20
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f1022,f747])).

fof(f747,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl11_87 ),
    inference(avatar_component_clause,[],[f746])).

fof(f746,plain,
    ( spl11_87
  <=> ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_87])])).

fof(f1022,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl11_20
    | ~ spl11_87 ),
    inference(resolution,[],[f1021,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f95,f96])).

fof(f96,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t29_yellow19.p',d3_tarski)).

fof(f1021,plain,
    ( r2_hidden(sK6(k2_pre_topc(sK0,sK1),sK1),sK1)
    | ~ spl11_20
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f1020,f850])).

fof(f850,plain,
    ( m1_subset_1(sK6(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ spl11_87 ),
    inference(resolution,[],[f770,f351])).

fof(f351,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f257,f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t29_yellow19.p',t4_subset)).

fof(f257,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f247,f107])).

fof(f107,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f247,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f108,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t29_yellow19.p',dt_k2_pre_topc)).

fof(f770,plain,
    ( r2_hidden(sK6(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1))
    | ~ spl11_87 ),
    inference(resolution,[],[f747,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f1020,plain,
    ( ~ m1_subset_1(sK6(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | r2_hidden(sK6(k2_pre_topc(sK0,sK1),sK1),sK1)
    | ~ spl11_20
    | ~ spl11_87 ),
    inference(resolution,[],[f941,f903])).

fof(f903,plain,
    ( r1_waybel_7(sK0,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),sK6(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f902,f105])).

fof(f105,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f902,plain,
    ( r1_waybel_7(sK0,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),sK6(k2_pre_topc(sK0,sK1),sK1))
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f901,f106])).

fof(f106,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f901,plain,
    ( r1_waybel_7(sK0,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),sK6(k2_pre_topc(sK0,sK1),sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f900,f107])).

fof(f900,plain,
    ( r1_waybel_7(sK0,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),sK6(k2_pre_topc(sK0,sK1),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f899,f108])).

fof(f899,plain,
    ( r1_waybel_7(sK0,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),sK6(k2_pre_topc(sK0,sK1),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f864,f850])).

fof(f864,plain,
    ( r1_waybel_7(sK0,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),sK6(k2_pre_topc(sK0,sK1),sK1))
    | ~ m1_subset_1(sK6(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(resolution,[],[f770,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_waybel_7(X0,sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r1_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      | v1_xboole_0(X3) ) )
                & ( ( r1_waybel_7(X0,sK4(X0,X1,X2),X2)
                    & r2_hidden(X1,sK4(X0,X1,X2))
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(sK4(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(sK4(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(sK4(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(sK4(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f87,f88])).

fof(f88,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_waybel_7(X0,X4,X2)
          & r2_hidden(X1,X4)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X4) )
     => ( r1_waybel_7(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK4(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK4(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK4(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r1_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      | v1_xboole_0(X3) ) )
                & ( ? [X4] :
                      ( r1_waybel_7(X0,X4,X2)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      & ~ v1_xboole_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r1_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      | v1_xboole_0(X3) ) )
                & ( ? [X3] :
                      ( r1_waybel_7(X0,X3,X2)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      & ~ v1_xboole_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t29_yellow19.p',t27_yellow19)).

fof(f941,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK0,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl11_20
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f940,f898])).

fof(f898,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f897,f105])).

fof(f897,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)))
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f896,f106])).

fof(f896,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f895,f107])).

fof(f895,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f894,f108])).

fof(f894,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f863,f850])).

fof(f863,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)))
    | ~ m1_subset_1(sK6(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(resolution,[],[f770,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | r2_hidden(X1,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f940,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(sK1,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),X0) )
    | ~ spl11_20
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f939,f888])).

fof(f888,plain,
    ( v13_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f887,f105])).

fof(f887,plain,
    ( v13_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f886,f106])).

fof(f886,plain,
    ( v13_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f885,f107])).

fof(f885,plain,
    ( v13_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f884,f108])).

fof(f884,plain,
    ( v13_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f861,f850])).

fof(f861,plain,
    ( v13_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK6(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(resolution,[],[f770,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | v13_waybel_0(sK4(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f939,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(sK1,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),X0) )
    | ~ spl11_20
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f938,f883])).

fof(f883,plain,
    ( v2_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f882,f105])).

fof(f882,plain,
    ( v2_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f881,f106])).

fof(f881,plain,
    ( v2_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f880,f107])).

fof(f880,plain,
    ( v2_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f879,f108])).

fof(f879,plain,
    ( v2_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f860,f850])).

fof(f860,plain,
    ( v2_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK6(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(resolution,[],[f770,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | v2_waybel_0(sK4(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f938,plain,
    ( ! [X0] :
        ( ~ v2_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(sK1,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),X0) )
    | ~ spl11_20
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f926,f878])).

fof(f878,plain,
    ( v1_subset_1(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f877,f105])).

fof(f877,plain,
    ( v1_subset_1(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f876,f106])).

fof(f876,plain,
    ( v1_subset_1(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f875,f107])).

fof(f875,plain,
    ( v1_subset_1(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f874,f108])).

fof(f874,plain,
    ( v1_subset_1(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f859,f850])).

fof(f859,plain,
    ( v1_subset_1(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK6(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(resolution,[],[f770,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | v1_subset_1(sK4(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f926,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(sK1,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),X0) )
    | ~ spl11_20
    | ~ spl11_87 ),
    inference(resolution,[],[f893,f244])).

fof(f244,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        | r2_hidden(X5,sK1)
        | ~ r2_hidden(sK1,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,X4,X5) )
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl11_20
  <=> ! [X5,X4] :
        ( r2_hidden(X5,sK1)
        | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ r2_hidden(sK1,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f893,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f892,f105])).

fof(f892,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f891,f106])).

fof(f891,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f890,f107])).

fof(f890,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f889,f108])).

fof(f889,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f862,f850])).

fof(f862,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK6(k2_pre_topc(sK0,sK1),sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ m1_subset_1(sK6(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_87 ),
    inference(resolution,[],[f770,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f831,plain,
    ( ~ spl11_17
    | spl11_94
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | spl11_19 ),
    inference(avatar_split_clause,[],[f827,f238,f224,f217,f210,f829,f228])).

fof(f228,plain,
    ( spl11_17
  <=> ~ v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f210,plain,
    ( spl11_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f217,plain,
    ( spl11_12
  <=> v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f224,plain,
    ( spl11_14
  <=> v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f238,plain,
    ( spl11_19
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f827,plain,
    ( ! [X2,X1] :
        ( ~ r1_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f826,f105])).

fof(f826,plain,
    ( ! [X2,X1] :
        ( ~ r1_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f825,f106])).

fof(f825,plain,
    ( ! [X2,X1] :
        ( ~ r1_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f824,f107])).

fof(f824,plain,
    ( ! [X2,X1] :
        ( ~ r1_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f788,f239])).

fof(f239,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f238])).

fof(f788,plain,
    ( ! [X2,X1] :
        ( ~ r1_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f787,f225])).

fof(f225,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f224])).

fof(f787,plain,
    ( ! [X2,X1] :
        ( ~ r1_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f772,f218])).

fof(f218,plain,
    ( v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f217])).

fof(f772,plain,
    ( ! [X2,X1] :
        ( ~ r1_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_10 ),
    inference(resolution,[],[f211,f140])).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ r1_waybel_7(X0,X3,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f211,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f210])).

fof(f758,plain,
    ( spl11_88
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f757,f176,f752])).

fof(f176,plain,
    ( spl11_1
  <=> ~ v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f757,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(subsumption_resolution,[],[f249,f107])).

fof(f249,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_pre_topc(sK0,sK1) = sK1
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f108,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t29_yellow19.p',t52_pre_topc)).

fof(f756,plain,
    ( spl11_0
    | ~ spl11_89 ),
    inference(avatar_split_clause,[],[f755,f749,f173])).

fof(f173,plain,
    ( spl11_0
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f749,plain,
    ( spl11_89
  <=> k2_pre_topc(sK0,sK1) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_89])])).

fof(f755,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f260,f107])).

fof(f260,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f250,f106])).

fof(f250,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f108,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f754,plain,
    ( ~ spl11_87
    | spl11_88 ),
    inference(avatar_split_clause,[],[f338,f752,f746])).

fof(f338,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1) ),
    inference(resolution,[],[f263,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t29_yellow19.p',d10_xboole_0)).

fof(f263,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f251,f107])).

fof(f251,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f108,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t29_yellow19.p',t48_pre_topc)).

fof(f245,plain,
    ( spl11_0
    | spl11_20 ),
    inference(avatar_split_clause,[],[f241,f243,f173])).

fof(f241,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK1)
      | ~ r1_waybel_7(sK0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | v4_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f109,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t29_yellow19.p',t7_boole)).

fof(f109,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK1)
      | ~ r1_waybel_7(sK0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | v1_xboole_0(X4)
      | v4_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f240,plain,
    ( ~ spl11_1
    | ~ spl11_19 ),
    inference(avatar_split_clause,[],[f110,f238,f176])).

fof(f110,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f233,plain,
    ( ~ spl11_1
    | spl11_16 ),
    inference(avatar_split_clause,[],[f111,f231,f176])).

fof(f231,plain,
    ( spl11_16
  <=> v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f111,plain,
    ( v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f226,plain,
    ( ~ spl11_1
    | spl11_14 ),
    inference(avatar_split_clause,[],[f112,f224,f176])).

fof(f112,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f219,plain,
    ( ~ spl11_1
    | spl11_12 ),
    inference(avatar_split_clause,[],[f113,f217,f176])).

fof(f113,plain,
    ( v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f212,plain,
    ( ~ spl11_1
    | spl11_10 ),
    inference(avatar_split_clause,[],[f114,f210,f176])).

fof(f114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f205,plain,
    ( ~ spl11_1
    | spl11_8 ),
    inference(avatar_split_clause,[],[f115,f203,f176])).

fof(f115,plain,
    ( r2_hidden(sK1,sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f198,plain,
    ( ~ spl11_1
    | spl11_6 ),
    inference(avatar_split_clause,[],[f116,f196,f176])).

fof(f116,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f191,plain,
    ( ~ spl11_1
    | spl11_4 ),
    inference(avatar_split_clause,[],[f117,f189,f176])).

fof(f117,plain,
    ( r1_waybel_7(sK0,sK2,sK3)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f184,plain,
    ( ~ spl11_1
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f118,f182,f176])).

fof(f118,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).
%------------------------------------------------------------------------------
