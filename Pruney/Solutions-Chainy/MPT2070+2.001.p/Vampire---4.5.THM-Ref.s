%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  263 (2079 expanded)
%              Number of leaves         :   26 ( 722 expanded)
%              Depth                    :   59
%              Number of atoms          : 2346 (37266 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (  10 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f501,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f111,f116,f121,f125,f306,f322,f329,f357,f500])).

fof(f500,plain,
    ( spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10
    | ~ spl8_26 ),
    inference(avatar_contradiction_clause,[],[f499])).

fof(f499,plain,
    ( $false
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f498,f80])).

fof(f80,plain,
    ( ~ r2_hidden(sK3,sK1)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl8_2
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f498,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f497,f90])).

fof(f90,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl8_4
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f497,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK3,sK1)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10
    | ~ spl8_26 ),
    inference(resolution,[],[f496,f85])).

fof(f85,plain,
    ( r2_waybel_7(sK0,sK2,sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl8_3
  <=> r2_waybel_7(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f496,plain,
    ( ! [X1] :
        ( ~ r2_waybel_7(sK0,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f495,f443])).

fof(f443,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f442,f95])).

fof(f95,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl8_5
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f442,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,sK2)
        | r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X0) )
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(resolution,[],[f393,f38])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ( ~ r2_hidden(sK3,sK1)
        & r2_waybel_7(sK0,sK2,sK3)
        & m1_subset_1(sK3,u1_struct_0(sK0))
        & r2_hidden(sK1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
        & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
        & ~ v1_xboole_0(sK2) )
      | ~ v4_pre_topc(sK1,sK0) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,sK1)
              | ~ r2_waybel_7(sK0,X4,X5)
              | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
          | ~ r2_hidden(sK1,X4)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
          | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
          | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
          | v1_xboole_0(X4) )
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r2_waybel_7(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & ~ v1_xboole_0(X2) )
              | ~ v4_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r2_waybel_7(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X4)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
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
                    & r2_waybel_7(sK0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,sK0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r2_waybel_7(sK0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X3,X1)
                  & r2_waybel_7(sK0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
              & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0)))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
              & ~ v1_xboole_0(X2) )
          | ~ v4_pre_topc(X1,sK0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X1)
                  | ~ r2_waybel_7(sK0,X4,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
              | ~ r2_hidden(X1,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
              | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
              | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
              | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
              | v1_xboole_0(X4) )
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,sK1)
                & r2_waybel_7(sK0,X2,X3)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & r2_hidden(sK1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
            & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
            & ~ v1_xboole_0(X2) )
        | ~ v4_pre_topc(sK1,sK0) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,sK1)
                | ~ r2_waybel_7(sK0,X4,X5)
                | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
            | ~ r2_hidden(sK1,X4)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
            | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
            | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
            | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
            | v1_xboole_0(X4) )
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(X3,sK1)
            & r2_waybel_7(sK0,X2,X3)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & r2_hidden(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0)))
        & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r2_hidden(X3,sK1)
          & r2_waybel_7(sK0,sK2,X3)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & r2_hidden(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
      & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ~ r2_hidden(X3,sK1)
        & r2_waybel_7(sK0,sK2,X3)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r2_hidden(sK3,sK1)
      & r2_waybel_7(sK0,sK2,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r2_waybel_7(X0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X2) )
                 => ( r2_hidden(X1,X2)
                   => ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r2_waybel_7(X0,X2,X3)
                         => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & ~ v1_xboole_0(X2) )
               => ( r2_hidden(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_waybel_7(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow19)).

fof(f393,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X1) )
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f392,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f392,plain,
    ( ! [X2,X1] :
        ( ~ r2_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f391,f36])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f391,plain,
    ( ! [X2,X1] :
        ( ~ r2_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f390,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f390,plain,
    ( ! [X2,X1] :
        ( ~ r2_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f389,f120])).

fof(f120,plain,
    ( ~ v1_xboole_0(sK2)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl8_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f389,plain,
    ( ! [X2,X1] :
        ( ~ r2_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f388,f115])).

fof(f115,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl8_9
  <=> v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f388,plain,
    ( ! [X2,X1] :
        ( ~ r2_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f387,f110])).

fof(f110,plain,
    ( v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl8_8
  <=> v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f387,plain,
    ( ! [X2,X1] :
        ( ~ r2_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f375,f105])).

fof(f105,plain,
    ( v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl8_7
  <=> v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f375,plain,
    ( ! [X2,X1] :
        ( ~ r2_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f100,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ r2_waybel_7(X0,X3,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X3) ) )
                & ( ( r2_waybel_7(X0,sK6(X0,X1,X2),X2)
                    & r2_hidden(X1,sK6(X0,X1,X2))
                    & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(sK6(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_waybel_7(X0,X4,X2)
          & r2_hidden(X1,X4)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
          & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X4) )
     => ( r2_waybel_7(X0,sK6(X0,X1,X2),X2)
        & r2_hidden(X1,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X3) ) )
                & ( ? [X4] :
                      ( r2_waybel_7(X0,X4,X2)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & ~ v1_xboole_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X3) ) )
                & ( ? [X3] :
                      ( r2_waybel_7(X0,X3,X2)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & ~ v1_xboole_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
                    ( r2_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_yellow19)).

fof(f100,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl8_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f495,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
        | ~ r2_waybel_7(sK0,sK2,X1) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f494,f462])).

fof(f462,plain,
    ( ! [X2] :
        ( ~ v2_struct_0(sK7(sK0,sK1,X2))
        | ~ r2_waybel_7(sK0,sK2,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f461,f35])).

fof(f461,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X2)
        | ~ v2_struct_0(sK7(sK0,sK1,X2))
        | v2_struct_0(sK0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f460,f36])).

fof(f460,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X2)
        | ~ v2_struct_0(sK7(sK0,sK1,X2))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f459,f37])).

fof(f459,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X2)
        | ~ v2_struct_0(sK7(sK0,sK1,X2))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f448,f38])).

fof(f448,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X2)
        | ~ v2_struct_0(sK7(sK0,sK1,X2))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(duplicate_literal_removal,[],[f446])).

fof(f446,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X2)
        | ~ v2_struct_0(sK7(sK0,sK1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(resolution,[],[f443,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ v2_struct_0(sK7(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ( r3_waybel_9(X0,sK7(X0,X1,X2),X2)
                    & r1_waybel_0(X0,sK7(X0,X1,X2),X1)
                    & l1_waybel_0(sK7(X0,X1,X2),X0)
                    & v7_waybel_0(sK7(X0,X1,X2))
                    & v4_orders_2(sK7(X0,X1,X2))
                    & ~ v2_struct_0(sK7(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X4,X2)
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r3_waybel_9(X0,sK7(X0,X1,X2),X2)
        & r1_waybel_0(X0,sK7(X0,X1,X2),X1)
        & l1_waybel_0(sK7(X0,X1,X2),X0)
        & v7_waybel_0(sK7(X0,X1,X2))
        & v4_orders_2(sK7(X0,X1,X2))
        & ~ v2_struct_0(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X4] :
                      ( r3_waybel_9(X0,X4,X2)
                      & r1_waybel_0(X0,X4,X1)
                      & l1_waybel_0(X4,X0)
                      & v7_waybel_0(X4)
                      & v4_orders_2(X4)
                      & ~ v2_struct_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X3] :
                      ( r3_waybel_9(X0,X3,X2)
                      & r1_waybel_0(X0,X3,X1)
                      & l1_waybel_0(X3,X0)
                      & v7_waybel_0(X3)
                      & v4_orders_2(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow19)).

fof(f494,plain,
    ( ! [X1] :
        ( v2_struct_0(sK7(sK0,sK1,X1))
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
        | ~ r2_waybel_7(sK0,sK2,X1) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f492,f458])).

fof(f458,plain,
    ( ! [X1] :
        ( v4_orders_2(sK7(sK0,sK1,X1))
        | ~ r2_waybel_7(sK0,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f457,f35])).

fof(f457,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X1)
        | v4_orders_2(sK7(sK0,sK1,X1))
        | v2_struct_0(sK0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f456,f36])).

fof(f456,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X1)
        | v4_orders_2(sK7(sK0,sK1,X1))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f455,f37])).

fof(f455,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X1)
        | v4_orders_2(sK7(sK0,sK1,X1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f449,f38])).

fof(f449,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X1)
        | v4_orders_2(sK7(sK0,sK1,X1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(duplicate_literal_removal,[],[f445])).

fof(f445,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X1)
        | v4_orders_2(sK7(sK0,sK1,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(resolution,[],[f443,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | v4_orders_2(sK7(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f492,plain,
    ( ! [X1] :
        ( ~ v4_orders_2(sK7(sK0,sK1,X1))
        | v2_struct_0(sK7(sK0,sK1,X1))
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
        | ~ r2_waybel_7(sK0,sK2,X1) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10
    | ~ spl8_26 ),
    inference(duplicate_literal_removal,[],[f491])).

fof(f491,plain,
    ( ! [X1] :
        ( ~ v4_orders_2(sK7(sK0,sK1,X1))
        | v2_struct_0(sK7(sK0,sK1,X1))
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
        | ~ r2_waybel_7(sK0,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10
    | ~ spl8_26 ),
    inference(resolution,[],[f485,f454])).

fof(f454,plain,
    ( ! [X0] :
        ( v7_waybel_0(sK7(sK0,sK1,X0))
        | ~ r2_waybel_7(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f453,f35])).

fof(f453,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X0)
        | v7_waybel_0(sK7(sK0,sK1,X0))
        | v2_struct_0(sK0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f452,f36])).

fof(f452,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X0)
        | v7_waybel_0(sK7(sK0,sK1,X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f451,f37])).

fof(f451,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X0)
        | v7_waybel_0(sK7(sK0,sK1,X0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(subsumption_resolution,[],[f450,f38])).

fof(f450,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X0)
        | v7_waybel_0(sK7(sK0,sK1,X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(duplicate_literal_removal,[],[f444])).

fof(f444,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK2,X0)
        | v7_waybel_0(sK7(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | spl8_10 ),
    inference(resolution,[],[f443,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | v7_waybel_0(sK7(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f485,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(sK7(sK0,sK1,X0))
        | ~ v4_orders_2(sK7(sK0,sK1,X0))
        | v2_struct_0(sK7(sK0,sK1,X0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) )
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f484,f35])).

fof(f484,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK7(sK0,sK1,X0))
        | ~ v7_waybel_0(sK7(sK0,sK1,X0))
        | v2_struct_0(sK7(sK0,sK1,X0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | v2_struct_0(sK0) )
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f483,f36])).

fof(f483,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK7(sK0,sK1,X0))
        | ~ v7_waybel_0(sK7(sK0,sK1,X0))
        | v2_struct_0(sK7(sK0,sK1,X0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f482,f37])).

fof(f482,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK7(sK0,sK1,X0))
        | ~ v7_waybel_0(sK7(sK0,sK1,X0))
        | v2_struct_0(sK7(sK0,sK1,X0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f481,f38])).

fof(f481,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK7(sK0,sK1,X0))
        | ~ v7_waybel_0(sK7(sK0,sK1,X0))
        | v2_struct_0(sK7(sK0,sK1,X0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_26 ),
    inference(duplicate_literal_removal,[],[f480])).

fof(f480,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK7(sK0,sK1,X0))
        | ~ v7_waybel_0(sK7(sK0,sK1,X0))
        | v2_struct_0(sK7(sK0,sK1,X0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_26 ),
    inference(resolution,[],[f479,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK7(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f479,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK7(sK0,sK1,X0),sK0)
        | ~ v4_orders_2(sK7(sK0,sK1,X0))
        | ~ v7_waybel_0(sK7(sK0,sK1,X0))
        | v2_struct_0(sK7(sK0,sK1,X0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) )
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f478,f35])).

fof(f478,plain,
    ( ! [X0] :
        ( v2_struct_0(sK7(sK0,sK1,X0))
        | ~ v4_orders_2(sK7(sK0,sK1,X0))
        | ~ v7_waybel_0(sK7(sK0,sK1,X0))
        | ~ l1_waybel_0(sK7(sK0,sK1,X0),sK0)
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | v2_struct_0(sK0) )
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f477,f36])).

fof(f477,plain,
    ( ! [X0] :
        ( v2_struct_0(sK7(sK0,sK1,X0))
        | ~ v4_orders_2(sK7(sK0,sK1,X0))
        | ~ v7_waybel_0(sK7(sK0,sK1,X0))
        | ~ l1_waybel_0(sK7(sK0,sK1,X0),sK0)
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f476,f37])).

fof(f476,plain,
    ( ! [X0] :
        ( v2_struct_0(sK7(sK0,sK1,X0))
        | ~ v4_orders_2(sK7(sK0,sK1,X0))
        | ~ v7_waybel_0(sK7(sK0,sK1,X0))
        | ~ l1_waybel_0(sK7(sK0,sK1,X0),sK0)
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f475,f38])).

fof(f475,plain,
    ( ! [X0] :
        ( v2_struct_0(sK7(sK0,sK1,X0))
        | ~ v4_orders_2(sK7(sK0,sK1,X0))
        | ~ v7_waybel_0(sK7(sK0,sK1,X0))
        | ~ l1_waybel_0(sK7(sK0,sK1,X0),sK0)
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_26 ),
    inference(duplicate_literal_removal,[],[f474])).

fof(f474,plain,
    ( ! [X0] :
        ( v2_struct_0(sK7(sK0,sK1,X0))
        | ~ v4_orders_2(sK7(sK0,sK1,X0))
        | ~ v7_waybel_0(sK7(sK0,sK1,X0))
        | ~ l1_waybel_0(sK7(sK0,sK1,X0),sK0)
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_26 ),
    inference(resolution,[],[f471,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,sK7(X0,X1,X2),X1)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f471,plain,
    ( ! [X2,X1] :
        ( ~ r1_waybel_0(sK0,sK7(sK0,X2,X1),sK1)
        | v2_struct_0(sK7(sK0,X2,X1))
        | ~ v4_orders_2(sK7(sK0,X2,X1))
        | ~ v7_waybel_0(sK7(sK0,X2,X1))
        | ~ l1_waybel_0(sK7(sK0,X2,X1),sK0)
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f470,f35])).

fof(f470,plain,
    ( ! [X2,X1] :
        ( r2_hidden(X1,sK1)
        | v2_struct_0(sK7(sK0,X2,X1))
        | ~ v4_orders_2(sK7(sK0,X2,X1))
        | ~ v7_waybel_0(sK7(sK0,X2,X1))
        | ~ l1_waybel_0(sK7(sK0,X2,X1),sK0)
        | ~ r1_waybel_0(sK0,sK7(sK0,X2,X1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f469,f36])).

fof(f469,plain,
    ( ! [X2,X1] :
        ( r2_hidden(X1,sK1)
        | v2_struct_0(sK7(sK0,X2,X1))
        | ~ v4_orders_2(sK7(sK0,X2,X1))
        | ~ v7_waybel_0(sK7(sK0,X2,X1))
        | ~ l1_waybel_0(sK7(sK0,X2,X1),sK0)
        | ~ r1_waybel_0(sK0,sK7(sK0,X2,X1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f465,f37])).

fof(f465,plain,
    ( ! [X2,X1] :
        ( r2_hidden(X1,sK1)
        | v2_struct_0(sK7(sK0,X2,X1))
        | ~ v4_orders_2(sK7(sK0,X2,X1))
        | ~ v7_waybel_0(sK7(sK0,X2,X1))
        | ~ l1_waybel_0(sK7(sK0,X2,X1),sK0)
        | ~ r1_waybel_0(sK0,sK7(sK0,X2,X1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_26 ),
    inference(duplicate_literal_removal,[],[f464])).

fof(f464,plain,
    ( ! [X2,X1] :
        ( r2_hidden(X1,sK1)
        | v2_struct_0(sK7(sK0,X2,X1))
        | ~ v4_orders_2(sK7(sK0,X2,X1))
        | ~ v7_waybel_0(sK7(sK0,X2,X1))
        | ~ l1_waybel_0(sK7(sK0,X2,X1),sK0)
        | ~ r1_waybel_0(sK0,sK7(sK0,X2,X1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_26 ),
    inference(resolution,[],[f356,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,sK7(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f356,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | r2_hidden(X1,sK1)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ r1_waybel_0(sK0,X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl8_26
  <=> ! [X1,X0] :
        ( ~ r3_waybel_9(sK0,X0,X1)
        | r2_hidden(X1,sK1)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ r1_waybel_0(sK0,X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f357,plain,
    ( ~ spl8_1
    | spl8_26 ),
    inference(avatar_split_clause,[],[f353,f355,f74])).

fof(f74,plain,
    ( spl8_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f353,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v4_pre_topc(sK1,sK0)
      | r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f352,f35])).

fof(f352,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v4_pre_topc(sK1,sK0)
      | r2_hidden(X1,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f351,f36])).

fof(f351,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v4_pre_topc(sK1,sK0)
      | r2_hidden(X1,sK1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f168,f37])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v4_pre_topc(sK1,sK0)
      | r2_hidden(X1,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f49,f38])).

fof(f49,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r3_waybel_9(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_waybel_0(X0,X4,X1)
      | ~ l1_waybel_0(X4,X0)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ v4_pre_topc(X1,X0)
      | r2_hidden(X5,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ( ~ r2_hidden(sK5(X0,X1),X1)
                & r3_waybel_9(X0,sK4(X0,X1),sK5(X0,X1))
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & r1_waybel_0(X0,sK4(X0,X1),X1)
                & l1_waybel_0(sK4(X0,X1),X0)
                & v7_waybel_0(sK4(X0,X1))
                & v4_orders_2(sK4(X0,X1))
                & ~ v2_struct_0(sK4(X0,X1)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r3_waybel_9(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r1_waybel_0(X0,X4,X1)
                  | ~ l1_waybel_0(X4,X0)
                  | ~ v7_waybel_0(X4)
                  | ~ v4_orders_2(X4)
                  | v2_struct_0(X4) )
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r3_waybel_9(X0,X2,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_waybel_0(X0,X2,X1)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r3_waybel_9(X0,sK4(X0,X1),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & r1_waybel_0(X0,sK4(X0,X1),X1)
        & l1_waybel_0(sK4(X0,X1),X0)
        & v7_waybel_0(sK4(X0,X1))
        & v4_orders_2(sK4(X0,X1))
        & ~ v2_struct_0(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r3_waybel_9(X0,sK4(X0,X1),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r3_waybel_9(X0,sK4(X0,X1),sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r3_waybel_9(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_waybel_0(X0,X2,X1)
                  & l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r3_waybel_9(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r1_waybel_0(X0,X4,X1)
                  | ~ l1_waybel_0(X4,X0)
                  | ~ v7_waybel_0(X4)
                  | ~ v4_orders_2(X4)
                  | v2_struct_0(X4) )
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r3_waybel_9(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_waybel_0(X0,X2,X1)
                  & l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r3_waybel_9(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r1_waybel_0(X0,X2,X1)
                  | ~ l1_waybel_0(X2,X0)
                  | ~ v7_waybel_0(X2)
                  | ~ v4_orders_2(X2)
                  | v2_struct_0(X2) )
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r3_waybel_9(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r3_waybel_9(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( r1_waybel_0(X0,X2,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r3_waybel_9(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow19)).

fof(f329,plain,
    ( spl8_1
    | ~ spl8_21 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl8_1
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f327,f35])).

fof(f327,plain,
    ( v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f326,f36])).

fof(f326,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f325,f37])).

fof(f325,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f324,f38])).

fof(f324,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f323,f76])).

fof(f76,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f323,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_21 ),
    inference(resolution,[],[f305,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f305,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl8_21
  <=> r2_hidden(sK5(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f322,plain,
    ( spl8_1
    | spl8_20 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | spl8_1
    | spl8_20 ),
    inference(subsumption_resolution,[],[f320,f35])).

fof(f320,plain,
    ( v2_struct_0(sK0)
    | spl8_1
    | spl8_20 ),
    inference(subsumption_resolution,[],[f319,f36])).

fof(f319,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_20 ),
    inference(subsumption_resolution,[],[f318,f37])).

fof(f318,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_20 ),
    inference(subsumption_resolution,[],[f317,f38])).

fof(f317,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_20 ),
    inference(subsumption_resolution,[],[f316,f76])).

fof(f316,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_20 ),
    inference(resolution,[],[f301,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f301,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | spl8_20 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl8_20
  <=> m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f306,plain,
    ( ~ spl8_20
    | spl8_21
    | spl8_1
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f297,f123,f74,f303,f299])).

fof(f123,plain,
    ( spl8_11
  <=> ! [X5,X4] :
        ( r2_hidden(X5,sK1)
        | v1_xboole_0(X4)
        | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ r2_hidden(sK1,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

% (20954)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
fof(f297,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f296,f35])).

fof(f296,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f295,f36])).

fof(f295,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f294,f37])).

fof(f294,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f293,f38])).

fof(f293,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f292,f76])).

fof(f292,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f291,f130])).

fof(f130,plain,
    ( ~ v2_struct_0(sK4(sK0,sK1))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f129,f35])).

fof(f129,plain,
    ( ~ v2_struct_0(sK4(sK0,sK1))
    | v2_struct_0(sK0)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f128,f36])).

fof(f128,plain,
    ( ~ v2_struct_0(sK4(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f127,f37])).

fof(f127,plain,
    ( ~ v2_struct_0(sK4(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f126,f76])).

fof(f126,plain,
    ( ~ v2_struct_0(sK4(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f50,f38])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(sK4(X0,X1))
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f291,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | v2_struct_0(sK4(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f290,f135])).

fof(f135,plain,
    ( v4_orders_2(sK4(sK0,sK1))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f134,f35])).

fof(f134,plain,
    ( v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK0)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f133,f36])).

fof(f133,plain,
    ( v4_orders_2(sK4(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f132,f37])).

fof(f132,plain,
    ( v4_orders_2(sK4(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f131,f76])).

fof(f131,plain,
    ( v4_orders_2(sK4(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f51,f38])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_orders_2(sK4(X0,X1))
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f290,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK4(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f289,f140])).

fof(f140,plain,
    ( v7_waybel_0(sK4(sK0,sK1))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f139,f35])).

fof(f139,plain,
    ( v7_waybel_0(sK4(sK0,sK1))
    | v2_struct_0(sK0)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f138,f36])).

fof(f138,plain,
    ( v7_waybel_0(sK4(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f137,f37])).

fof(f137,plain,
    ( v7_waybel_0(sK4(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f136,f76])).

fof(f136,plain,
    ( v7_waybel_0(sK4(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f52,f38])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v7_waybel_0(sK4(X0,X1))
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f289,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ v7_waybel_0(sK4(sK0,sK1))
    | ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK4(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f288,f145])).

fof(f145,plain,
    ( l1_waybel_0(sK4(sK0,sK1),sK0)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f144,f35])).

fof(f144,plain,
    ( l1_waybel_0(sK4(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f143,f36])).

fof(f143,plain,
    ( l1_waybel_0(sK4(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f142,f37])).

fof(f142,plain,
    ( l1_waybel_0(sK4(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f141,f76])).

fof(f141,plain,
    ( l1_waybel_0(sK4(sK0,sK1),sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f53,f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | l1_waybel_0(sK4(X0,X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f288,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ l1_waybel_0(sK4(sK0,sK1),sK0)
    | ~ v7_waybel_0(sK4(sK0,sK1))
    | ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK4(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_11 ),
    inference(duplicate_literal_removal,[],[f287])).

fof(f287,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ l1_waybel_0(sK4(sK0,sK1),sK0)
    | ~ v7_waybel_0(sK4(sK0,sK1))
    | ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK4(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_11 ),
    inference(resolution,[],[f286,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(X0,sK4(X0,X1),X1)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f286,plain,
    ( ! [X0] :
        ( ~ r1_waybel_0(sK0,sK4(sK0,X0),sK1)
        | r2_hidden(sK5(sK0,X0),sK1)
        | ~ l1_waybel_0(sK4(sK0,X0),sK0)
        | ~ v7_waybel_0(sK4(sK0,X0))
        | ~ v4_orders_2(sK4(sK0,X0))
        | v2_struct_0(sK4(sK0,X0))
        | ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f285,f164])).

fof(f164,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1))
      | ~ l1_waybel_0(sK4(sK0,X0),sK0)
      | ~ v7_waybel_0(sK4(sK0,X0))
      | ~ v4_orders_2(sK4(sK0,X0))
      | v2_struct_0(sK4(sK0,X0))
      | ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
      | ~ r1_waybel_0(sK0,sK4(sK0,X0),sK1)
      | v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f163,f35])).

% (20961)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
fof(f163,plain,(
    ! [X0] :
      ( ~ r1_waybel_0(sK0,sK4(sK0,X0),sK1)
      | ~ l1_waybel_0(sK4(sK0,X0),sK0)
      | ~ v7_waybel_0(sK4(sK0,X0))
      | ~ v4_orders_2(sK4(sK0,X0))
      | v2_struct_0(sK4(sK0,X0))
      | ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
      | r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1))
      | v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f162,f36])).

fof(f162,plain,(
    ! [X0] :
      ( ~ r1_waybel_0(sK0,sK4(sK0,X0),sK1)
      | ~ l1_waybel_0(sK4(sK0,X0),sK0)
      | ~ v7_waybel_0(sK4(sK0,X0))
      | ~ v4_orders_2(sK4(sK0,X0))
      | v2_struct_0(sK4(sK0,X0))
      | ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
      | r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1))
      | v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f159,f37])).

fof(f159,plain,(
    ! [X0] :
      ( ~ r1_waybel_0(sK0,sK4(sK0,X0),sK1)
      | ~ l1_waybel_0(sK4(sK0,X0),sK0)
      | ~ v7_waybel_0(sK4(sK0,X0))
      | ~ v4_orders_2(sK4(sK0,X0))
      | v2_struct_0(sK4(sK0,X0))
      | ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
      | r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1))
      | v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f154,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,sK4(X0,X1),sK5(X0,X1))
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f153,f35])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f152,f36])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k2_pre_topc(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f150,f37])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k2_pre_topc(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f72,f38])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r3_waybel_9(X0,X3,X2)
      | ~ r1_waybel_0(X0,X3,X1)
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
        | r2_hidden(sK5(sK0,X0),sK1)
        | ~ l1_waybel_0(sK4(sK0,X0),sK0)
        | ~ v7_waybel_0(sK4(sK0,X0))
        | ~ v4_orders_2(sK4(sK0,X0))
        | v2_struct_0(sK4(sK0,X0))
        | ~ r1_waybel_0(sK0,sK4(sK0,X0),sK1)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1)) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f284,f35])).

fof(f284,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
        | r2_hidden(sK5(sK0,X0),sK1)
        | ~ l1_waybel_0(sK4(sK0,X0),sK0)
        | ~ v7_waybel_0(sK4(sK0,X0))
        | ~ v4_orders_2(sK4(sK0,X0))
        | v2_struct_0(sK4(sK0,X0))
        | ~ r1_waybel_0(sK0,sK4(sK0,X0),sK1)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1))
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f283,f36])).

fof(f283,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
        | r2_hidden(sK5(sK0,X0),sK1)
        | ~ l1_waybel_0(sK4(sK0,X0),sK0)
        | ~ v7_waybel_0(sK4(sK0,X0))
        | ~ v4_orders_2(sK4(sK0,X0))
        | v2_struct_0(sK4(sK0,X0))
        | ~ r1_waybel_0(sK0,sK4(sK0,X0),sK1)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f282,f37])).

fof(f282,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
        | r2_hidden(sK5(sK0,X0),sK1)
        | ~ l1_waybel_0(sK4(sK0,X0),sK0)
        | ~ v7_waybel_0(sK4(sK0,X0))
        | ~ v4_orders_2(sK4(sK0,X0))
        | v2_struct_0(sK4(sK0,X0))
        | ~ r1_waybel_0(sK0,sK4(sK0,X0),sK1)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f281,f38])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
        | r2_hidden(sK5(sK0,X0),sK1)
        | ~ l1_waybel_0(sK4(sK0,X0),sK0)
        | ~ v7_waybel_0(sK4(sK0,X0))
        | ~ v4_orders_2(sK4(sK0,X0))
        | v2_struct_0(sK4(sK0,X0))
        | ~ r1_waybel_0(sK0,sK4(sK0,X0),sK1)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
        | r2_hidden(sK5(sK0,X0),sK1)
        | ~ l1_waybel_0(sK4(sK0,X0),sK0)
        | ~ v7_waybel_0(sK4(sK0,X0))
        | ~ v4_orders_2(sK4(sK0,X0))
        | v2_struct_0(sK4(sK0,X0))
        | ~ r1_waybel_0(sK0,sK4(sK0,X0),sK1)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(resolution,[],[f279,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK6(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f279,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK6(sK0,sK1,sK5(sK0,X0)))
        | ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
        | r2_hidden(sK5(sK0,X0),sK1)
        | ~ l1_waybel_0(sK4(sK0,X0),sK0)
        | ~ v7_waybel_0(sK4(sK0,X0))
        | ~ v4_orders_2(sK4(sK0,X0))
        | v2_struct_0(sK4(sK0,X0))
        | ~ r1_waybel_0(sK0,sK4(sK0,X0),sK1)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_11 ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
        | v1_xboole_0(sK6(sK0,sK1,sK5(sK0,X0)))
        | r2_hidden(sK5(sK0,X0),sK1)
        | ~ l1_waybel_0(sK4(sK0,X0),sK0)
        | ~ v7_waybel_0(sK4(sK0,X0))
        | ~ v4_orders_2(sK4(sK0,X0))
        | v2_struct_0(sK4(sK0,X0))
        | ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
        | ~ r1_waybel_0(sK0,sK4(sK0,X0),sK1)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_11 ),
    inference(resolution,[],[f277,f164])).

fof(f277,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(sK6(sK0,sK1,X0))
        | r2_hidden(X0,sK1) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f276,f35])).

fof(f276,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(sK6(sK0,sK1,X0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f275,f36])).

fof(f275,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(sK6(sK0,sK1,X0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f274,f37])).

fof(f274,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(sK6(sK0,sK1,X0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f273,f38])).

fof(f273,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(sK6(sK0,sK1,X0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(duplicate_literal_removal,[],[f272])).

fof(f272,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(sK6(sK0,sK1,X0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(resolution,[],[f257,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK6(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK1,sK6(sK0,X1,X0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(sK6(sK0,X1,X0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f256,f35])).

fof(f256,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(sK6(sK0,X1,X0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f255,f36])).

fof(f255,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(sK6(sK0,X1,X0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f254,f37])).

fof(f254,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(sK6(sK0,X1,X0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(sK6(sK0,X1,X0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(resolution,[],[f252,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,sK6(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f252,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v1_xboole_0(sK6(sK0,X0,X1))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f251,f35])).

fof(f251,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(sK6(sK0,X0,X1))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f250,f36])).

fof(f250,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(sK6(sK0,X0,X1))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f249,f37])).

fof(f249,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(sK6(sK0,X0,X1))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(duplicate_literal_removal,[],[f248])).

fof(f248,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(sK6(sK0,X0,X1))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(resolution,[],[f247,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f247,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK6(sK0,X0,X1))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f246,f35])).

fof(f246,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK6(sK0,X0,X1))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f245,f36])).

fof(f245,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK6(sK0,X0,X1))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f244,f37])).

fof(f244,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK6(sK0,X0,X1))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(duplicate_literal_removal,[],[f243])).

fof(f243,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK6(sK0,X0,X1))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(resolution,[],[f242,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f242,plain,
    ( ! [X2,X0,X1] :
        ( ~ v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK6(sK0,X0,X1))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f241,f35])).

fof(f241,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK6(sK0,X0,X1))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f240,f36])).

fof(f240,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK6(sK0,X0,X1))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f239,f37])).

fof(f239,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK6(sK0,X0,X1))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(duplicate_literal_removal,[],[f238])).

fof(f238,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK6(sK0,X0,X1))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(resolution,[],[f158,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f158,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_waybel_7(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(sK6(sK0,X0,X1))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f157,f35])).

fof(f157,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(sK6(sK0,X0,X1))
        | ~ v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v3_waybel_7(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f156,f36])).

fof(f156,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(sK6(sK0,X0,X1))
        | ~ v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v3_waybel_7(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f155,f37])).

% (20962)WARNING: option uwaf not known.
fof(f155,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(sK6(sK0,X0,X1))
        | ~ v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v3_waybel_7(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | r2_hidden(X2,sK1)
        | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_11 ),
    inference(resolution,[],[f124,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f124,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | v1_xboole_0(X4)
        | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
        | r2_hidden(X5,sK1)
        | ~ r2_hidden(sK1,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,X4,X5) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,
    ( spl8_1
    | spl8_11 ),
    inference(avatar_split_clause,[],[f39,f123,f74])).

fof(f39,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK1)
      | ~ r2_waybel_7(sK0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(X4)
      | v4_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f121,plain,
    ( ~ spl8_1
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f40,f118,f74])).

fof(f40,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f116,plain,
    ( ~ spl8_1
    | spl8_9 ),
    inference(avatar_split_clause,[],[f41,f113,f74])).

fof(f41,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f111,plain,
    ( ~ spl8_1
    | spl8_8 ),
    inference(avatar_split_clause,[],[f42,f108,f74])).

fof(f42,plain,
    ( v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f106,plain,
    ( ~ spl8_1
    | spl8_7 ),
    inference(avatar_split_clause,[],[f43,f103,f74])).

fof(f43,plain,
    ( v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f101,plain,
    ( ~ spl8_1
    | spl8_6 ),
    inference(avatar_split_clause,[],[f44,f98,f74])).

fof(f44,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f96,plain,
    ( ~ spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f45,f93,f74])).

fof(f45,plain,
    ( r2_hidden(sK1,sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f91,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f46,f88,f74])).

fof(f46,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f47,f83,f74])).

fof(f47,plain,
    ( r2_waybel_7(sK0,sK2,sK3)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f81,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f48,f78,f74])).

fof(f48,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (20973)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.20/0.47  % (20956)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.50  % (20973)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f501,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f111,f116,f121,f125,f306,f322,f329,f357,f500])).
% 0.20/0.51  fof(f500,plain,(
% 0.20/0.51    spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10 | ~spl8_26),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f499])).
% 0.20/0.51  fof(f499,plain,(
% 0.20/0.51    $false | (spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10 | ~spl8_26)),
% 0.20/0.51    inference(subsumption_resolution,[],[f498,f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ~r2_hidden(sK3,sK1) | spl8_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    spl8_2 <=> r2_hidden(sK3,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.51  fof(f498,plain,(
% 0.20/0.51    r2_hidden(sK3,sK1) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10 | ~spl8_26)),
% 0.20/0.51    inference(subsumption_resolution,[],[f497,f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl8_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    spl8_4 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.51  fof(f497,plain,(
% 0.20/0.51    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK3,sK1) | (~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10 | ~spl8_26)),
% 0.20/0.51    inference(resolution,[],[f496,f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    r2_waybel_7(sK0,sK2,sK3) | ~spl8_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    spl8_3 <=> r2_waybel_7(sK0,sK2,sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.51  fof(f496,plain,(
% 0.20/0.51    ( ! [X1] : (~r2_waybel_7(sK0,sK2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,sK1)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10 | ~spl8_26)),
% 0.20/0.51    inference(subsumption_resolution,[],[f495,f443])).
% 0.20/0.51  fof(f443,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f442,f95])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    r2_hidden(sK1,sK2) | ~spl8_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f93])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    spl8_5 <=> r2_hidden(sK1,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.51  fof(f442,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK1,sK2) | r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X0)) ) | (~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(resolution,[],[f393,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ((((~r2_hidden(sK3,sK1) & r2_waybel_7(sK0,sK2,sK3) & m1_subset_1(sK3,u1_struct_0(sK0))) & r2_hidden(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(sK2)) | ~v4_pre_topc(sK1,sK0)) & (! [X4] : (! [X5] : (r2_hidden(X5,sK1) | ~r2_waybel_7(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) | ~r2_hidden(sK1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X4)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f20,f19,f18,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(sK0,X2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,sK0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(sK0,X2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,sK0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (? [X3] : (~r2_hidden(X3,sK1) & r2_waybel_7(sK0,X2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & r2_hidden(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(sK1,sK0)) & (! [X4] : (! [X5] : (r2_hidden(X5,sK1) | ~r2_waybel_7(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) | ~r2_hidden(sK1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X4)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ? [X2] : (? [X3] : (~r2_hidden(X3,sK1) & r2_waybel_7(sK0,X2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & r2_hidden(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(X2)) => (? [X3] : (~r2_hidden(X3,sK1) & r2_waybel_7(sK0,sK2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & r2_hidden(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ? [X3] : (~r2_hidden(X3,sK1) & r2_waybel_7(sK0,sK2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) => (~r2_hidden(sK3,sK1) & r2_waybel_7(sK0,sK2,sK3) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(rectify,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f6])).
% 0.20/0.51  fof(f6,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> ! [X2] : ((! [X3] : ((r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) => (r2_hidden(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_waybel_7(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f4])).
% 0.20/0.51  fof(f4,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) => (r2_hidden(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_waybel_7(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow19)).
% 0.20/0.51  fof(f393,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,sK2) | r2_hidden(X1,k2_pre_topc(sK0,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X1)) ) | (~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f392,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f392,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r2_waybel_7(sK0,sK2,X1) | ~r2_hidden(X2,sK2) | r2_hidden(X1,k2_pre_topc(sK0,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f391,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f391,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r2_waybel_7(sK0,sK2,X1) | ~r2_hidden(X2,sK2) | r2_hidden(X1,k2_pre_topc(sK0,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f390,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f390,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r2_waybel_7(sK0,sK2,X1) | ~r2_hidden(X2,sK2) | r2_hidden(X1,k2_pre_topc(sK0,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f389,f120])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    ~v1_xboole_0(sK2) | spl8_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    spl8_10 <=> v1_xboole_0(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.51  fof(f389,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r2_waybel_7(sK0,sK2,X1) | ~r2_hidden(X2,sK2) | r2_hidden(X1,k2_pre_topc(sK0,X2)) | v1_xboole_0(sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9)),
% 0.20/0.51    inference(subsumption_resolution,[],[f388,f115])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~spl8_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f113])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    spl8_9 <=> v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.51  fof(f388,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r2_waybel_7(sK0,sK2,X1) | ~r2_hidden(X2,sK2) | r2_hidden(X1,k2_pre_topc(sK0,X2)) | ~v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_6 | ~spl8_7 | ~spl8_8)),
% 0.20/0.51    inference(subsumption_resolution,[],[f387,f110])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~spl8_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f108])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    spl8_8 <=> v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.51  fof(f387,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r2_waybel_7(sK0,sK2,X1) | ~r2_hidden(X2,sK2) | r2_hidden(X1,k2_pre_topc(sK0,X2)) | ~v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_6 | ~spl8_7)),
% 0.20/0.51    inference(subsumption_resolution,[],[f375,f105])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~spl8_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f103])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    spl8_7 <=> v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.51  fof(f375,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r2_waybel_7(sK0,sK2,X1) | ~r2_hidden(X2,sK2) | r2_hidden(X1,k2_pre_topc(sK0,X2)) | ~v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_6),
% 0.20/0.51    inference(resolution,[],[f100,f65])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | r2_hidden(X2,k2_pre_topc(X0,X1)) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3))) & ((r2_waybel_7(X0,sK6(X0,X1,X2),X2) & r2_hidden(X1,sK6(X0,X1,X2)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(sK6(X0,X1,X2))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X4] : (r2_waybel_7(X0,X4,X2) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X4)) => (r2_waybel_7(X0,sK6(X0,X1,X2),X2) & r2_hidden(X1,sK6(X0,X1,X2)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(sK6(X0,X1,X2))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3))) & (? [X4] : (r2_waybel_7(X0,X4,X2) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X4)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(rectify,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3))) & (? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_yellow19)).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~spl8_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f98])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    spl8_6 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.51  fof(f495,plain,(
% 0.20/0.51    ( ! [X1] : (r2_hidden(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k2_pre_topc(sK0,sK1)) | ~r2_waybel_7(sK0,sK2,X1)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10 | ~spl8_26)),
% 0.20/0.51    inference(subsumption_resolution,[],[f494,f462])).
% 0.20/0.51  fof(f462,plain,(
% 0.20/0.51    ( ! [X2] : (~v2_struct_0(sK7(sK0,sK1,X2)) | ~r2_waybel_7(sK0,sK2,X2) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f461,f35])).
% 0.20/0.51  fof(f461,plain,(
% 0.20/0.51    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X2) | ~v2_struct_0(sK7(sK0,sK1,X2)) | v2_struct_0(sK0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f460,f36])).
% 0.20/0.51  fof(f460,plain,(
% 0.20/0.51    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X2) | ~v2_struct_0(sK7(sK0,sK1,X2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f459,f37])).
% 0.20/0.51  fof(f459,plain,(
% 0.20/0.51    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X2) | ~v2_struct_0(sK7(sK0,sK1,X2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f448,f38])).
% 0.20/0.51  fof(f448,plain,(
% 0.20/0.51    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X2) | ~v2_struct_0(sK7(sK0,sK1,X2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f446])).
% 0.20/0.51  fof(f446,plain,(
% 0.20/0.51    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X2) | ~v2_struct_0(sK7(sK0,sK1,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(resolution,[],[f443,f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~v2_struct_0(sK7(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r3_waybel_9(X0,X3,X2) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & ((r3_waybel_9(X0,sK7(X0,X1,X2),X2) & r1_waybel_0(X0,sK7(X0,X1,X2),X1) & l1_waybel_0(sK7(X0,X1,X2),X0) & v7_waybel_0(sK7(X0,X1,X2)) & v4_orders_2(sK7(X0,X1,X2)) & ~v2_struct_0(sK7(X0,X1,X2))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X4] : (r3_waybel_9(X0,X4,X2) & r1_waybel_0(X0,X4,X1) & l1_waybel_0(X4,X0) & v7_waybel_0(X4) & v4_orders_2(X4) & ~v2_struct_0(X4)) => (r3_waybel_9(X0,sK7(X0,X1,X2),X2) & r1_waybel_0(X0,sK7(X0,X1,X2),X1) & l1_waybel_0(sK7(X0,X1,X2),X0) & v7_waybel_0(sK7(X0,X1,X2)) & v4_orders_2(sK7(X0,X1,X2)) & ~v2_struct_0(sK7(X0,X1,X2))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r3_waybel_9(X0,X3,X2) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & (? [X4] : (r3_waybel_9(X0,X4,X2) & r1_waybel_0(X0,X4,X1) & l1_waybel_0(X4,X0) & v7_waybel_0(X4) & v4_orders_2(X4) & ~v2_struct_0(X4)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(rectify,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r3_waybel_9(X0,X3,X2) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & (? [X3] : (r3_waybel_9(X0,X3,X2) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r3_waybel_9(X0,X3,X2) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r3_waybel_9(X0,X3,X2) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r3_waybel_9(X0,X3,X2) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow19)).
% 0.20/0.51  fof(f494,plain,(
% 0.20/0.51    ( ! [X1] : (v2_struct_0(sK7(sK0,sK1,X1)) | r2_hidden(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k2_pre_topc(sK0,sK1)) | ~r2_waybel_7(sK0,sK2,X1)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10 | ~spl8_26)),
% 0.20/0.51    inference(subsumption_resolution,[],[f492,f458])).
% 0.20/0.51  fof(f458,plain,(
% 0.20/0.51    ( ! [X1] : (v4_orders_2(sK7(sK0,sK1,X1)) | ~r2_waybel_7(sK0,sK2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f457,f35])).
% 0.20/0.51  fof(f457,plain,(
% 0.20/0.51    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X1) | v4_orders_2(sK7(sK0,sK1,X1)) | v2_struct_0(sK0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f456,f36])).
% 0.20/0.51  fof(f456,plain,(
% 0.20/0.51    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X1) | v4_orders_2(sK7(sK0,sK1,X1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f455,f37])).
% 0.20/0.51  fof(f455,plain,(
% 0.20/0.51    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X1) | v4_orders_2(sK7(sK0,sK1,X1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f449,f38])).
% 0.20/0.51  fof(f449,plain,(
% 0.20/0.51    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X1) | v4_orders_2(sK7(sK0,sK1,X1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f445])).
% 0.20/0.51  fof(f445,plain,(
% 0.20/0.51    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X1) | v4_orders_2(sK7(sK0,sK1,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(resolution,[],[f443,f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_pre_topc(X0,X1)) | v4_orders_2(sK7(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f492,plain,(
% 0.20/0.51    ( ! [X1] : (~v4_orders_2(sK7(sK0,sK1,X1)) | v2_struct_0(sK7(sK0,sK1,X1)) | r2_hidden(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k2_pre_topc(sK0,sK1)) | ~r2_waybel_7(sK0,sK2,X1)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10 | ~spl8_26)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f491])).
% 0.20/0.51  fof(f491,plain,(
% 0.20/0.51    ( ! [X1] : (~v4_orders_2(sK7(sK0,sK1,X1)) | v2_struct_0(sK7(sK0,sK1,X1)) | r2_hidden(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k2_pre_topc(sK0,sK1)) | ~r2_waybel_7(sK0,sK2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10 | ~spl8_26)),
% 0.20/0.51    inference(resolution,[],[f485,f454])).
% 0.20/0.51  fof(f454,plain,(
% 0.20/0.51    ( ! [X0] : (v7_waybel_0(sK7(sK0,sK1,X0)) | ~r2_waybel_7(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f453,f35])).
% 0.20/0.51  fof(f453,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X0) | v7_waybel_0(sK7(sK0,sK1,X0)) | v2_struct_0(sK0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f452,f36])).
% 0.20/0.51  fof(f452,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X0) | v7_waybel_0(sK7(sK0,sK1,X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f451,f37])).
% 0.20/0.51  fof(f451,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X0) | v7_waybel_0(sK7(sK0,sK1,X0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(subsumption_resolution,[],[f450,f38])).
% 0.20/0.51  fof(f450,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X0) | v7_waybel_0(sK7(sK0,sK1,X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f444])).
% 0.20/0.51  fof(f444,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK2,X0) | v7_waybel_0(sK7(sK0,sK1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_9 | spl8_10)),
% 0.20/0.51    inference(resolution,[],[f443,f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_pre_topc(X0,X1)) | v7_waybel_0(sK7(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f485,plain,(
% 0.20/0.51    ( ! [X0] : (~v7_waybel_0(sK7(sK0,sK1,X0)) | ~v4_orders_2(sK7(sK0,sK1,X0)) | v2_struct_0(sK7(sK0,sK1,X0)) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1))) ) | ~spl8_26),
% 0.20/0.51    inference(subsumption_resolution,[],[f484,f35])).
% 0.20/0.51  fof(f484,plain,(
% 0.20/0.51    ( ! [X0] : (~v4_orders_2(sK7(sK0,sK1,X0)) | ~v7_waybel_0(sK7(sK0,sK1,X0)) | v2_struct_0(sK7(sK0,sK1,X0)) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | v2_struct_0(sK0)) ) | ~spl8_26),
% 0.20/0.51    inference(subsumption_resolution,[],[f483,f36])).
% 0.20/0.51  fof(f483,plain,(
% 0.20/0.51    ( ! [X0] : (~v4_orders_2(sK7(sK0,sK1,X0)) | ~v7_waybel_0(sK7(sK0,sK1,X0)) | v2_struct_0(sK7(sK0,sK1,X0)) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_26),
% 0.20/0.51    inference(subsumption_resolution,[],[f482,f37])).
% 0.20/0.51  fof(f482,plain,(
% 0.20/0.51    ( ! [X0] : (~v4_orders_2(sK7(sK0,sK1,X0)) | ~v7_waybel_0(sK7(sK0,sK1,X0)) | v2_struct_0(sK7(sK0,sK1,X0)) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_26),
% 0.20/0.51    inference(subsumption_resolution,[],[f481,f38])).
% 0.20/0.51  fof(f481,plain,(
% 0.20/0.51    ( ! [X0] : (~v4_orders_2(sK7(sK0,sK1,X0)) | ~v7_waybel_0(sK7(sK0,sK1,X0)) | v2_struct_0(sK7(sK0,sK1,X0)) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_26),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f480])).
% 0.20/0.51  fof(f480,plain,(
% 0.20/0.51    ( ! [X0] : (~v4_orders_2(sK7(sK0,sK1,X0)) | ~v7_waybel_0(sK7(sK0,sK1,X0)) | v2_struct_0(sK7(sK0,sK1,X0)) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_26),
% 0.20/0.51    inference(resolution,[],[f479,f69])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (l1_waybel_0(sK7(X0,X1,X2),X0) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f479,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_waybel_0(sK7(sK0,sK1,X0),sK0) | ~v4_orders_2(sK7(sK0,sK1,X0)) | ~v7_waybel_0(sK7(sK0,sK1,X0)) | v2_struct_0(sK7(sK0,sK1,X0)) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1))) ) | ~spl8_26),
% 0.20/0.51    inference(subsumption_resolution,[],[f478,f35])).
% 0.20/0.51  fof(f478,plain,(
% 0.20/0.51    ( ! [X0] : (v2_struct_0(sK7(sK0,sK1,X0)) | ~v4_orders_2(sK7(sK0,sK1,X0)) | ~v7_waybel_0(sK7(sK0,sK1,X0)) | ~l1_waybel_0(sK7(sK0,sK1,X0),sK0) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | v2_struct_0(sK0)) ) | ~spl8_26),
% 0.20/0.51    inference(subsumption_resolution,[],[f477,f36])).
% 0.20/0.51  fof(f477,plain,(
% 0.20/0.51    ( ! [X0] : (v2_struct_0(sK7(sK0,sK1,X0)) | ~v4_orders_2(sK7(sK0,sK1,X0)) | ~v7_waybel_0(sK7(sK0,sK1,X0)) | ~l1_waybel_0(sK7(sK0,sK1,X0),sK0) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_26),
% 0.20/0.51    inference(subsumption_resolution,[],[f476,f37])).
% 0.20/0.51  fof(f476,plain,(
% 0.20/0.51    ( ! [X0] : (v2_struct_0(sK7(sK0,sK1,X0)) | ~v4_orders_2(sK7(sK0,sK1,X0)) | ~v7_waybel_0(sK7(sK0,sK1,X0)) | ~l1_waybel_0(sK7(sK0,sK1,X0),sK0) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_26),
% 0.20/0.51    inference(subsumption_resolution,[],[f475,f38])).
% 0.20/0.51  fof(f475,plain,(
% 0.20/0.51    ( ! [X0] : (v2_struct_0(sK7(sK0,sK1,X0)) | ~v4_orders_2(sK7(sK0,sK1,X0)) | ~v7_waybel_0(sK7(sK0,sK1,X0)) | ~l1_waybel_0(sK7(sK0,sK1,X0),sK0) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_26),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f474])).
% 0.20/0.51  fof(f474,plain,(
% 0.20/0.51    ( ! [X0] : (v2_struct_0(sK7(sK0,sK1,X0)) | ~v4_orders_2(sK7(sK0,sK1,X0)) | ~v7_waybel_0(sK7(sK0,sK1,X0)) | ~l1_waybel_0(sK7(sK0,sK1,X0),sK0) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_26),
% 0.20/0.51    inference(resolution,[],[f471,f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_waybel_0(X0,sK7(X0,X1,X2),X1) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f471,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r1_waybel_0(sK0,sK7(sK0,X2,X1),sK1) | v2_struct_0(sK7(sK0,X2,X1)) | ~v4_orders_2(sK7(sK0,X2,X1)) | ~v7_waybel_0(sK7(sK0,X2,X1)) | ~l1_waybel_0(sK7(sK0,X2,X1),sK0) | r2_hidden(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k2_pre_topc(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl8_26),
% 0.20/0.51    inference(subsumption_resolution,[],[f470,f35])).
% 0.20/0.51  fof(f470,plain,(
% 0.20/0.51    ( ! [X2,X1] : (r2_hidden(X1,sK1) | v2_struct_0(sK7(sK0,X2,X1)) | ~v4_orders_2(sK7(sK0,X2,X1)) | ~v7_waybel_0(sK7(sK0,X2,X1)) | ~l1_waybel_0(sK7(sK0,X2,X1),sK0) | ~r1_waybel_0(sK0,sK7(sK0,X2,X1),sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k2_pre_topc(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | ~spl8_26),
% 0.20/0.51    inference(subsumption_resolution,[],[f469,f36])).
% 0.20/0.51  fof(f469,plain,(
% 0.20/0.51    ( ! [X2,X1] : (r2_hidden(X1,sK1) | v2_struct_0(sK7(sK0,X2,X1)) | ~v4_orders_2(sK7(sK0,X2,X1)) | ~v7_waybel_0(sK7(sK0,X2,X1)) | ~l1_waybel_0(sK7(sK0,X2,X1),sK0) | ~r1_waybel_0(sK0,sK7(sK0,X2,X1),sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k2_pre_topc(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_26),
% 0.20/0.51    inference(subsumption_resolution,[],[f465,f37])).
% 0.20/0.51  fof(f465,plain,(
% 0.20/0.51    ( ! [X2,X1] : (r2_hidden(X1,sK1) | v2_struct_0(sK7(sK0,X2,X1)) | ~v4_orders_2(sK7(sK0,X2,X1)) | ~v7_waybel_0(sK7(sK0,X2,X1)) | ~l1_waybel_0(sK7(sK0,X2,X1),sK0) | ~r1_waybel_0(sK0,sK7(sK0,X2,X1),sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k2_pre_topc(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_26),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f464])).
% 0.20/0.51  fof(f464,plain,(
% 0.20/0.51    ( ! [X2,X1] : (r2_hidden(X1,sK1) | v2_struct_0(sK7(sK0,X2,X1)) | ~v4_orders_2(sK7(sK0,X2,X1)) | ~v7_waybel_0(sK7(sK0,X2,X1)) | ~l1_waybel_0(sK7(sK0,X2,X1),sK0) | ~r1_waybel_0(sK0,sK7(sK0,X2,X1),sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k2_pre_topc(sK0,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_26),
% 0.20/0.51    inference(resolution,[],[f356,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r3_waybel_9(X0,sK7(X0,X1,X2),X2) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f356,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | r2_hidden(X1,sK1) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~r1_waybel_0(sK0,X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl8_26),
% 0.20/0.51    inference(avatar_component_clause,[],[f355])).
% 0.20/0.51  fof(f355,plain,(
% 0.20/0.51    spl8_26 <=> ! [X1,X0] : (~r3_waybel_9(sK0,X0,X1) | r2_hidden(X1,sK1) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~r1_waybel_0(sK0,X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.20/0.51  fof(f357,plain,(
% 0.20/0.51    ~spl8_1 | spl8_26),
% 0.20/0.51    inference(avatar_split_clause,[],[f353,f355,f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    spl8_1 <=> v4_pre_topc(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.51  fof(f353,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,X0,sK1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v4_pre_topc(sK1,sK0) | r2_hidden(X1,sK1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f352,f35])).
% 0.20/0.51  fof(f352,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,X0,sK1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v4_pre_topc(sK1,sK0) | r2_hidden(X1,sK1) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f351,f36])).
% 0.20/0.51  fof(f351,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,X0,sK1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v4_pre_topc(sK1,sK0) | r2_hidden(X1,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f168,f37])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,X0,sK1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v4_pre_topc(sK1,sK0) | r2_hidden(X1,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f49,f38])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X4,X0,X5,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r3_waybel_9(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r1_waybel_0(X0,X4,X1) | ~l1_waybel_0(X4,X0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4) | ~v4_pre_topc(X1,X0) | r2_hidden(X5,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ((~r2_hidden(sK5(X0,X1),X1) & r3_waybel_9(X0,sK4(X0,X1),sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & r1_waybel_0(X0,sK4(X0,X1),X1) & l1_waybel_0(sK4(X0,X1),X0) & v7_waybel_0(sK4(X0,X1)) & v4_orders_2(sK4(X0,X1)) & ~v2_struct_0(sK4(X0,X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r3_waybel_9(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r1_waybel_0(X0,X4,X1) | ~l1_waybel_0(X4,X0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f25,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r3_waybel_9(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (? [X3] : (~r2_hidden(X3,X1) & r3_waybel_9(X0,sK4(X0,X1),X3) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,sK4(X0,X1),X1) & l1_waybel_0(sK4(X0,X1),X0) & v7_waybel_0(sK4(X0,X1)) & v4_orders_2(sK4(X0,X1)) & ~v2_struct_0(sK4(X0,X1))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r3_waybel_9(X0,sK4(X0,X1),X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK5(X0,X1),X1) & r3_waybel_9(X0,sK4(X0,X1),sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r3_waybel_9(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r3_waybel_9(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r1_waybel_0(X0,X4,X1) | ~l1_waybel_0(X4,X0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(rectify,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r3_waybel_9(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> ! [X2] : ((! [X3] : ((r2_hidden(X3,X1) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1)) | (~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r1_waybel_0(X0,X2,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow19)).
% 0.20/0.51  fof(f329,plain,(
% 0.20/0.51    spl8_1 | ~spl8_21),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f328])).
% 0.20/0.51  fof(f328,plain,(
% 0.20/0.51    $false | (spl8_1 | ~spl8_21)),
% 0.20/0.51    inference(subsumption_resolution,[],[f327,f35])).
% 0.20/0.51  fof(f327,plain,(
% 0.20/0.51    v2_struct_0(sK0) | (spl8_1 | ~spl8_21)),
% 0.20/0.51    inference(subsumption_resolution,[],[f326,f36])).
% 0.20/0.51  fof(f326,plain,(
% 0.20/0.51    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_21)),
% 0.20/0.51    inference(subsumption_resolution,[],[f325,f37])).
% 0.20/0.51  fof(f325,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_21)),
% 0.20/0.51    inference(subsumption_resolution,[],[f324,f38])).
% 0.20/0.51  fof(f324,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_21)),
% 0.20/0.51    inference(subsumption_resolution,[],[f323,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ~v4_pre_topc(sK1,sK0) | spl8_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f74])).
% 0.20/0.51  fof(f323,plain,(
% 0.20/0.51    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl8_21),
% 0.20/0.51    inference(resolution,[],[f305,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f305,plain,(
% 0.20/0.51    r2_hidden(sK5(sK0,sK1),sK1) | ~spl8_21),
% 0.20/0.51    inference(avatar_component_clause,[],[f303])).
% 0.20/0.51  fof(f303,plain,(
% 0.20/0.51    spl8_21 <=> r2_hidden(sK5(sK0,sK1),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.20/0.51  fof(f322,plain,(
% 0.20/0.51    spl8_1 | spl8_20),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f321])).
% 0.20/0.51  fof(f321,plain,(
% 0.20/0.51    $false | (spl8_1 | spl8_20)),
% 0.20/0.51    inference(subsumption_resolution,[],[f320,f35])).
% 0.20/0.51  fof(f320,plain,(
% 0.20/0.51    v2_struct_0(sK0) | (spl8_1 | spl8_20)),
% 0.20/0.51    inference(subsumption_resolution,[],[f319,f36])).
% 0.20/0.51  fof(f319,plain,(
% 0.20/0.51    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_20)),
% 0.20/0.51    inference(subsumption_resolution,[],[f318,f37])).
% 0.20/0.51  fof(f318,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_20)),
% 0.20/0.51    inference(subsumption_resolution,[],[f317,f38])).
% 0.20/0.51  fof(f317,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | spl8_20)),
% 0.20/0.51    inference(subsumption_resolution,[],[f316,f76])).
% 0.20/0.51  fof(f316,plain,(
% 0.20/0.51    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_20),
% 0.20/0.51    inference(resolution,[],[f301,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f301,plain,(
% 0.20/0.51    ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | spl8_20),
% 0.20/0.51    inference(avatar_component_clause,[],[f299])).
% 0.20/0.51  fof(f299,plain,(
% 0.20/0.51    spl8_20 <=> m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.20/0.51  fof(f306,plain,(
% 0.20/0.51    ~spl8_20 | spl8_21 | spl8_1 | ~spl8_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f297,f123,f74,f303,f299])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    spl8_11 <=> ! [X5,X4] : (r2_hidden(X5,sK1) | v1_xboole_0(X4) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~r2_hidden(sK1,X4) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,X4,X5))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.20/0.51  % (20954)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.20/0.51  fof(f297,plain,(
% 0.20/0.51    r2_hidden(sK5(sK0,sK1),sK1) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | (spl8_1 | ~spl8_11)),
% 0.20/0.51    inference(subsumption_resolution,[],[f296,f35])).
% 0.20/0.51  fof(f296,plain,(
% 0.20/0.51    r2_hidden(sK5(sK0,sK1),sK1) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | (spl8_1 | ~spl8_11)),
% 0.20/0.51    inference(subsumption_resolution,[],[f295,f36])).
% 0.20/0.51  fof(f295,plain,(
% 0.20/0.51    r2_hidden(sK5(sK0,sK1),sK1) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_11)),
% 0.20/0.51    inference(subsumption_resolution,[],[f294,f37])).
% 0.20/0.51  fof(f294,plain,(
% 0.20/0.51    r2_hidden(sK5(sK0,sK1),sK1) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_11)),
% 0.20/0.51    inference(subsumption_resolution,[],[f293,f38])).
% 0.20/0.51  fof(f293,plain,(
% 0.20/0.51    r2_hidden(sK5(sK0,sK1),sK1) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_11)),
% 0.20/0.51    inference(subsumption_resolution,[],[f292,f76])).
% 0.20/0.51  fof(f292,plain,(
% 0.20/0.51    r2_hidden(sK5(sK0,sK1),sK1) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_11)),
% 0.20/0.51    inference(subsumption_resolution,[],[f291,f130])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    ~v2_struct_0(sK4(sK0,sK1)) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f129,f35])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ~v2_struct_0(sK4(sK0,sK1)) | v2_struct_0(sK0) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f128,f36])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    ~v2_struct_0(sK4(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f127,f37])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    ~v2_struct_0(sK4(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f126,f76])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    ~v2_struct_0(sK4(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f50,f38])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_struct_0(sK4(X0,X1)) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f291,plain,(
% 0.20/0.51    r2_hidden(sK5(sK0,sK1),sK1) | v2_struct_0(sK4(sK0,sK1)) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_11)),
% 0.20/0.51    inference(subsumption_resolution,[],[f290,f135])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    v4_orders_2(sK4(sK0,sK1)) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f134,f35])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK0) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f133,f36])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    v4_orders_2(sK4(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f132,f37])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    v4_orders_2(sK4(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f131,f76])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    v4_orders_2(sK4(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f51,f38])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_orders_2(sK4(X0,X1)) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f290,plain,(
% 0.20/0.51    r2_hidden(sK5(sK0,sK1),sK1) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1)) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_11)),
% 0.20/0.51    inference(subsumption_resolution,[],[f289,f140])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    v7_waybel_0(sK4(sK0,sK1)) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f139,f35])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    v7_waybel_0(sK4(sK0,sK1)) | v2_struct_0(sK0) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f138,f36])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    v7_waybel_0(sK4(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f137,f37])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    v7_waybel_0(sK4(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f136,f76])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    v7_waybel_0(sK4(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f52,f38])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v7_waybel_0(sK4(X0,X1)) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f289,plain,(
% 0.20/0.51    r2_hidden(sK5(sK0,sK1),sK1) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1)) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_11)),
% 0.20/0.51    inference(subsumption_resolution,[],[f288,f145])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    l1_waybel_0(sK4(sK0,sK1),sK0) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f144,f35])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    l1_waybel_0(sK4(sK0,sK1),sK0) | v2_struct_0(sK0) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f143,f36])).
% 0.20/0.51  fof(f143,plain,(
% 0.20/0.51    l1_waybel_0(sK4(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f142,f37])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    l1_waybel_0(sK4(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f141,f76])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    l1_waybel_0(sK4(sK0,sK1),sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f53,f38])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | l1_waybel_0(sK4(X0,X1),X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f288,plain,(
% 0.20/0.52    r2_hidden(sK5(sK0,sK1),sK1) | ~l1_waybel_0(sK4(sK0,sK1),sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1)) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl8_11),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f287])).
% 0.20/0.52  fof(f287,plain,(
% 0.20/0.52    r2_hidden(sK5(sK0,sK1),sK1) | ~l1_waybel_0(sK4(sK0,sK1),sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1)) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl8_11),
% 0.20/0.52    inference(resolution,[],[f286,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_waybel_0(X0,sK4(X0,X1),X1) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f286,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_waybel_0(sK0,sK4(sK0,X0),sK1) | r2_hidden(sK5(sK0,X0),sK1) | ~l1_waybel_0(sK4(sK0,X0),sK0) | ~v7_waybel_0(sK4(sK0,X0)) | ~v4_orders_2(sK4(sK0,X0)) | v2_struct_0(sK4(sK0,X0)) | ~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f285,f164])).
% 0.20/0.52  fof(f164,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1)) | ~l1_waybel_0(sK4(sK0,X0),sK0) | ~v7_waybel_0(sK4(sK0,X0)) | ~v4_orders_2(sK4(sK0,X0)) | v2_struct_0(sK4(sK0,X0)) | ~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | ~r1_waybel_0(sK0,sK4(sK0,X0),sK1) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f163,f35])).
% 0.20/0.52  % (20961)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.20/0.52  fof(f163,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_waybel_0(sK0,sK4(sK0,X0),sK1) | ~l1_waybel_0(sK4(sK0,X0),sK0) | ~v7_waybel_0(sK4(sK0,X0)) | ~v4_orders_2(sK4(sK0,X0)) | v2_struct_0(sK4(sK0,X0)) | ~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1)) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f162,f36])).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_waybel_0(sK0,sK4(sK0,X0),sK1) | ~l1_waybel_0(sK4(sK0,X0),sK0) | ~v7_waybel_0(sK4(sK0,X0)) | ~v4_orders_2(sK4(sK0,X0)) | v2_struct_0(sK4(sK0,X0)) | ~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1)) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f159,f37])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_waybel_0(sK0,sK4(sK0,X0),sK1) | ~l1_waybel_0(sK4(sK0,X0),sK0) | ~v7_waybel_0(sK4(sK0,X0)) | ~v4_orders_2(sK4(sK0,X0)) | v2_struct_0(sK4(sK0,X0)) | ~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1)) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f154,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r3_waybel_9(X0,sK4(X0,X1),sK5(X0,X1)) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f154,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~r1_waybel_0(sK0,X0,sK1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k2_pre_topc(sK0,sK1))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f153,f35])).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~r1_waybel_0(sK0,X0,sK1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k2_pre_topc(sK0,sK1)) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f152,f36])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~r1_waybel_0(sK0,X0,sK1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k2_pre_topc(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f150,f37])).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~r1_waybel_0(sK0,X0,sK1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f72,f38])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r3_waybel_9(X0,X3,X2) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f285,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | r2_hidden(sK5(sK0,X0),sK1) | ~l1_waybel_0(sK4(sK0,X0),sK0) | ~v7_waybel_0(sK4(sK0,X0)) | ~v4_orders_2(sK4(sK0,X0)) | v2_struct_0(sK4(sK0,X0)) | ~r1_waybel_0(sK0,sK4(sK0,X0),sK1) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1))) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f284,f35])).
% 0.20/0.52  fof(f284,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | r2_hidden(sK5(sK0,X0),sK1) | ~l1_waybel_0(sK4(sK0,X0),sK0) | ~v7_waybel_0(sK4(sK0,X0)) | ~v4_orders_2(sK4(sK0,X0)) | v2_struct_0(sK4(sK0,X0)) | ~r1_waybel_0(sK0,sK4(sK0,X0),sK1) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1)) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f283,f36])).
% 0.20/0.52  fof(f283,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | r2_hidden(sK5(sK0,X0),sK1) | ~l1_waybel_0(sK4(sK0,X0),sK0) | ~v7_waybel_0(sK4(sK0,X0)) | ~v4_orders_2(sK4(sK0,X0)) | v2_struct_0(sK4(sK0,X0)) | ~r1_waybel_0(sK0,sK4(sK0,X0),sK1) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f282,f37])).
% 0.20/0.52  fof(f282,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | r2_hidden(sK5(sK0,X0),sK1) | ~l1_waybel_0(sK4(sK0,X0),sK0) | ~v7_waybel_0(sK4(sK0,X0)) | ~v4_orders_2(sK4(sK0,X0)) | v2_struct_0(sK4(sK0,X0)) | ~r1_waybel_0(sK0,sK4(sK0,X0),sK1) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f281,f38])).
% 0.20/0.52  fof(f281,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | r2_hidden(sK5(sK0,X0),sK1) | ~l1_waybel_0(sK4(sK0,X0),sK0) | ~v7_waybel_0(sK4(sK0,X0)) | ~v4_orders_2(sK4(sK0,X0)) | v2_struct_0(sK4(sK0,X0)) | ~r1_waybel_0(sK0,sK4(sK0,X0),sK1) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f280])).
% 0.20/0.52  fof(f280,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | r2_hidden(sK5(sK0,X0),sK1) | ~l1_waybel_0(sK4(sK0,X0),sK0) | ~v7_waybel_0(sK4(sK0,X0)) | ~v4_orders_2(sK4(sK0,X0)) | v2_struct_0(sK4(sK0,X0)) | ~r1_waybel_0(sK0,sK4(sK0,X0),sK1) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK5(sK0,X0),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(resolution,[],[f279,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(sK6(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f279,plain,(
% 0.20/0.52    ( ! [X0] : (v1_xboole_0(sK6(sK0,sK1,sK5(sK0,X0))) | ~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | r2_hidden(sK5(sK0,X0),sK1) | ~l1_waybel_0(sK4(sK0,X0),sK0) | ~v7_waybel_0(sK4(sK0,X0)) | ~v4_orders_2(sK4(sK0,X0)) | v2_struct_0(sK4(sK0,X0)) | ~r1_waybel_0(sK0,sK4(sK0,X0),sK1) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl8_11),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f278])).
% 0.20/0.52  fof(f278,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | v1_xboole_0(sK6(sK0,sK1,sK5(sK0,X0))) | r2_hidden(sK5(sK0,X0),sK1) | ~l1_waybel_0(sK4(sK0,X0),sK0) | ~v7_waybel_0(sK4(sK0,X0)) | ~v4_orders_2(sK4(sK0,X0)) | v2_struct_0(sK4(sK0,X0)) | ~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | ~r1_waybel_0(sK0,sK4(sK0,X0),sK1) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl8_11),
% 0.20/0.52    inference(resolution,[],[f277,f164])).
% 0.20/0.52  fof(f277,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(sK6(sK0,sK1,X0)) | r2_hidden(X0,sK1)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f276,f35])).
% 0.20/0.52  fof(f276,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(sK6(sK0,sK1,X0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f275,f36])).
% 0.20/0.52  fof(f275,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(sK6(sK0,sK1,X0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f274,f37])).
% 0.20/0.52  fof(f274,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(sK6(sK0,sK1,X0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f273,f38])).
% 0.20/0.52  fof(f273,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(sK6(sK0,sK1,X0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f272])).
% 0.20/0.52  fof(f272,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(sK6(sK0,sK1,X0)) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(resolution,[],[f257,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(X1,sK6(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f257,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK1,sK6(sK0,X1,X0)) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(sK6(sK0,X1,X0)) | ~r2_hidden(X0,k2_pre_topc(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f256,f35])).
% 0.20/0.52  fof(f256,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(sK1,sK6(sK0,X1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(sK6(sK0,X1,X0)) | ~r2_hidden(X0,k2_pre_topc(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f255,f36])).
% 0.20/0.52  fof(f255,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(sK1,sK6(sK0,X1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(sK6(sK0,X1,X0)) | ~r2_hidden(X0,k2_pre_topc(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f254,f37])).
% 0.20/0.52  fof(f254,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(sK1,sK6(sK0,X1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(sK6(sK0,X1,X0)) | ~r2_hidden(X0,k2_pre_topc(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f253])).
% 0.20/0.52  fof(f253,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(sK1,sK6(sK0,X1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(sK6(sK0,X1,X0)) | ~r2_hidden(X0,k2_pre_topc(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,k2_pre_topc(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(resolution,[],[f252,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_waybel_7(X0,sK6(X0,X1,X2),X2) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f252,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v1_xboole_0(sK6(sK0,X0,X1)) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f251,f35])).
% 0.20/0.52  fof(f251,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v1_xboole_0(sK6(sK0,X0,X1)) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f250,f36])).
% 0.20/0.52  fof(f250,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v1_xboole_0(sK6(sK0,X0,X1)) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f249,f37])).
% 0.20/0.52  fof(f249,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v1_xboole_0(sK6(sK0,X0,X1)) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f248])).
% 0.20/0.52  fof(f248,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v1_xboole_0(sK6(sK0,X0,X1)) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(resolution,[],[f247,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f247,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK6(sK0,X0,X1)) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f246,f35])).
% 0.20/0.52  fof(f246,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK6(sK0,X0,X1)) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f245,f36])).
% 0.20/0.52  fof(f245,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK6(sK0,X0,X1)) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f244,f37])).
% 0.20/0.52  fof(f244,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK6(sK0,X0,X1)) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f243])).
% 0.20/0.52  fof(f243,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK6(sK0,X0,X1)) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(resolution,[],[f242,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f242,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK6(sK0,X0,X1)) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f241,f35])).
% 0.20/0.52  fof(f241,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK6(sK0,X0,X1)) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f240,f36])).
% 0.20/0.52  fof(f240,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK6(sK0,X0,X1)) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f239,f37])).
% 0.20/0.52  fof(f239,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK6(sK0,X0,X1)) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f238])).
% 0.20/0.52  fof(f238,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK6(sK0,X0,X1)) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(resolution,[],[f158,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v3_waybel_7(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK6(sK0,X0,X1)) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f157,f35])).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v1_xboole_0(sK6(sK0,X0,X1)) | ~v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | ~v3_waybel_7(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f156,f36])).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v1_xboole_0(sK6(sK0,X0,X1)) | ~v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | ~v3_waybel_7(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f155,f37])).
% 0.20/0.52  % (20962)WARNING: option uwaf not known.
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v1_xboole_0(sK6(sK0,X0,X1)) | ~v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | ~v3_waybel_7(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | r2_hidden(X2,sK1) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_11),
% 0.20/0.52    inference(resolution,[],[f124,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v1_xboole_0(X4) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | r2_hidden(X5,sK1) | ~r2_hidden(sK1,X4) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_waybel_7(sK0,X4,X5)) ) | ~spl8_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f123])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    spl8_1 | spl8_11),
% 0.20/0.52    inference(avatar_split_clause,[],[f39,f123,f74])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X4,X5] : (r2_hidden(X5,sK1) | ~r2_waybel_7(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_hidden(sK1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X4) | v4_pre_topc(sK1,sK0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    ~spl8_1 | ~spl8_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f40,f118,f74])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ~v1_xboole_0(sK2) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    ~spl8_1 | spl8_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f41,f113,f74])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    ~spl8_1 | spl8_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f42,f108,f74])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    ~spl8_1 | spl8_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f43,f103,f74])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    ~spl8_1 | spl8_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f44,f98,f74])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    ~spl8_1 | spl8_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f45,f93,f74])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    r2_hidden(sK1,sK2) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ~spl8_1 | spl8_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f46,f88,f74])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    m1_subset_1(sK3,u1_struct_0(sK0)) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ~spl8_1 | spl8_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f47,f83,f74])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    r2_waybel_7(sK0,sK2,sK3) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ~spl8_1 | ~spl8_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f48,f78,f74])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ~r2_hidden(sK3,sK1) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (20973)------------------------------
% 0.20/0.52  % (20973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20973)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (20973)Memory used [KB]: 5756
% 0.20/0.52  % (20973)Time elapsed: 0.089 s
% 0.20/0.52  % (20952)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.20/0.52  % (20973)------------------------------
% 0.20/0.52  % (20973)------------------------------
% 0.20/0.52  % (20962)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.20/0.52  % (20958)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.52  % (20949)Success in time 0.16 s
%------------------------------------------------------------------------------
