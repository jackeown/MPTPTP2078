%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t30_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:51 EDT 2019

% Result     : Theorem 11.42s
% Output     : Refutation 11.42s
% Verified   : 
% Statistics : Number of formulae       :  185 (2284 expanded)
%              Number of leaves         :   28 ( 767 expanded)
%              Depth                    :   31
%              Number of atoms          : 1100 (36280 expanded)
%              Number of equality atoms :   23 ( 264 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5581,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f193,f200,f207,f214,f221,f228,f235,f242,f249,f254,f4377,f4414,f5580])).

fof(f5580,plain,
    ( spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | spl12_19
    | ~ spl12_844 ),
    inference(avatar_contradiction_clause,[],[f5579])).

fof(f5579,plain,
    ( $false
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_19
    | ~ spl12_844 ),
    inference(subsumption_resolution,[],[f5578,f206])).

fof(f206,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl12_6
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f5578,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_19
    | ~ spl12_844 ),
    inference(subsumption_resolution,[],[f5577,f192])).

fof(f192,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl12_3
  <=> ~ r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f5577,plain,
    ( r2_hidden(sK3,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_19
    | ~ spl12_844 ),
    inference(resolution,[],[f5069,f199])).

fof(f199,plain,
    ( r2_waybel_7(sK0,sK2,sK3)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl12_4
  <=> r2_waybel_7(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f5069,plain,
    ( ! [X0] :
        ( ~ r2_waybel_7(sK0,sK2,X0)
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_19
    | ~ spl12_844 ),
    inference(subsumption_resolution,[],[f5068,f112])).

fof(f112,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f82,f86,f85,f84,f83])).

fof(f83,plain,
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

fof(f84,plain,(
    ! [X0] :
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
     => ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X3,sK1)
                  & r2_waybel_7(X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_hidden(sK1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          | ~ v4_pre_topc(sK1,X0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,sK1)
                  | ~ r2_waybel_7(X0,X4,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ r2_hidden(sK1,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
              | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
              | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
              | v1_xboole_0(X4) )
          | v4_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ? [X2] :
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
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r2_waybel_7(X0,sK2,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & r2_hidden(X1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(X0)))
        & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_waybel_7(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3,X1)
        & r2_waybel_7(X0,X2,sK3)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
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
    inference(rectify,[],[f81])).

fof(f81,plain,(
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
    inference(flattening,[],[f80])).

fof(f80,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
                    & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X2) )
                 => ( r2_hidden(X1,X2)
                   => ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r2_waybel_7(X0,X2,X3)
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
                  & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & ~ v1_xboole_0(X2) )
               => ( r2_hidden(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_waybel_7(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t30_yellow19.p',t30_yellow19)).

fof(f5068,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_waybel_7(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_19
    | ~ spl12_844 ),
    inference(subsumption_resolution,[],[f5014,f213])).

fof(f213,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl12_8
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f5014,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(sK1,sK2)
        | ~ r2_waybel_7(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_19
    | ~ spl12_844 ),
    inference(superposition,[],[f4693,f4409])).

fof(f4409,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl12_844 ),
    inference(avatar_component_clause,[],[f4408])).

fof(f4408,plain,
    ( spl12_844
  <=> k2_pre_topc(sK0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_844])])).

fof(f4693,plain,
    ( ! [X2,X1] :
        ( r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ r2_hidden(X2,sK2)
        | ~ r2_waybel_7(sK0,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f4692,f109])).

fof(f109,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f4692,plain,
    ( ! [X2,X1] :
        ( ~ r2_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f4691,f110])).

fof(f110,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f4691,plain,
    ( ! [X2,X1] :
        ( ~ r2_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f4690,f111])).

fof(f111,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f4690,plain,
    ( ! [X2,X1] :
        ( ~ r2_waybel_7(sK0,sK2,X1)
        | ~ r2_hidden(X2,sK2)
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f4689,f248])).

fof(f248,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl12_19 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl12_19
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f4689,plain,
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
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_16 ),
    inference(subsumption_resolution,[],[f4688,f241])).

fof(f241,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl12_16
  <=> v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f4688,plain,
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
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f4687,f234])).

fof(f234,plain,
    ( v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl12_14
  <=> v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f4687,plain,
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
    | ~ spl12_10
    | ~ spl12_12 ),
    inference(subsumption_resolution,[],[f4672,f227])).

fof(f227,plain,
    ( v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl12_12
  <=> v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f4672,plain,
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
    | ~ spl12_10 ),
    inference(resolution,[],[f220,f149])).

fof(f149,plain,(
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
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
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
                & ( ( r2_waybel_7(X0,sK5(X0,X1,X2),X2)
                    & r2_hidden(X1,sK5(X0,X1,X2))
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(sK5(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f91,f92])).

fof(f92,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_waybel_7(X0,X4,X2)
          & r2_hidden(X1,X4)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
          & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X4) )
     => ( r2_waybel_7(X0,sK5(X0,X1,X2),X2)
        & r2_hidden(X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v3_waybel_7(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v13_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(sK5(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
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
    inference(rectify,[],[f90])).

fof(f90,plain,(
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
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f58,plain,(
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
                    ( r2_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t30_yellow19.p',t28_yellow19)).

fof(f220,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl12_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f4414,plain,
    ( spl12_844
    | ~ spl12_1 ),
    inference(avatar_split_clause,[],[f4413,f185,f4408])).

fof(f185,plain,
    ( spl12_1
  <=> ~ v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f4413,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(subsumption_resolution,[],[f262,f111])).

fof(f262,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_pre_topc(sK0,sK1) = sK1
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f112,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

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
    file('/export/starexec/sandbox/benchmark/yellow19__t30_yellow19.p',t52_pre_topc)).

fof(f4377,plain,
    ( spl12_1
    | ~ spl12_20 ),
    inference(avatar_contradiction_clause,[],[f4376])).

fof(f4376,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f4347,f360])).

fof(f360,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f359,f275])).

fof(f275,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f274,f111])).

fof(f274,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | ~ l1_pre_topc(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f273,f186])).

fof(f186,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f185])).

fof(f273,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f263,f110])).

fof(f263,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f112,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f359,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1) ),
    inference(resolution,[],[f276,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f96])).

fof(f96,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t30_yellow19.p',d10_xboole_0)).

fof(f276,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f264,f111])).

fof(f264,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f112,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t30_yellow19.p',t48_pre_topc)).

fof(f4347,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl12_1
    | ~ spl12_20 ),
    inference(resolution,[],[f4344,f167])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f99,f100])).

fof(f100,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f74])).

fof(f74,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t30_yellow19.p',d3_tarski)).

fof(f4344,plain,
    ( r2_hidden(sK7(k2_pre_topc(sK0,sK1),sK1),sK1)
    | ~ spl12_1
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f4343,f910])).

fof(f910,plain,
    ( m1_subset_1(sK7(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ spl12_1 ),
    inference(resolution,[],[f483,f512])).

fof(f512,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f270,f172])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t30_yellow19.p',t4_subset)).

fof(f270,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f260,f111])).

fof(f260,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f112,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t30_yellow19.p',dt_k2_pre_topc)).

fof(f483,plain,
    ( r2_hidden(sK7(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1))
    | ~ spl12_1 ),
    inference(resolution,[],[f360,f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f4343,plain,
    ( ~ m1_subset_1(sK7(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | r2_hidden(sK7(k2_pre_topc(sK0,sK1),sK1),sK1)
    | ~ spl12_1
    | ~ spl12_20 ),
    inference(resolution,[],[f2280,f956])).

fof(f956,plain,
    ( r2_waybel_7(sK0,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),sK7(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f955,f109])).

fof(f955,plain,
    ( r2_waybel_7(sK0,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),sK7(k2_pre_topc(sK0,sK1),sK1))
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f954,f110])).

fof(f954,plain,
    ( r2_waybel_7(sK0,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),sK7(k2_pre_topc(sK0,sK1),sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f953,f111])).

fof(f953,plain,
    ( r2_waybel_7(sK0,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),sK7(k2_pre_topc(sK0,sK1),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f952,f112])).

fof(f952,plain,
    ( r2_waybel_7(sK0,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),sK7(k2_pre_topc(sK0,sK1),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f917,f910])).

fof(f917,plain,
    ( r2_waybel_7(sK0,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),sK7(k2_pre_topc(sK0,sK1),sK1))
    | ~ m1_subset_1(sK7(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(resolution,[],[f483,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | r2_waybel_7(X0,sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f2280,plain,
    ( ! [X0] :
        ( ~ r2_waybel_7(sK0,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl12_1
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f2279,f951])).

fof(f951,plain,
    ( r2_hidden(sK1,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f950,f109])).

fof(f950,plain,
    ( r2_hidden(sK1,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)))
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f949,f110])).

fof(f949,plain,
    ( r2_hidden(sK1,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f948,f111])).

fof(f948,plain,
    ( r2_hidden(sK1,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f947,f112])).

fof(f947,plain,
    ( r2_hidden(sK1,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f916,f910])).

fof(f916,plain,
    ( r2_hidden(sK1,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)))
    | ~ m1_subset_1(sK7(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(resolution,[],[f483,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | r2_hidden(X1,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f2279,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(sK1,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),X0) )
    | ~ spl12_1
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f2278,f941])).

fof(f941,plain,
    ( v3_waybel_7(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f940,f109])).

fof(f940,plain,
    ( v3_waybel_7(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f939,f110])).

fof(f939,plain,
    ( v3_waybel_7(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f938,f111])).

fof(f938,plain,
    ( v3_waybel_7(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f937,f112])).

fof(f937,plain,
    ( v3_waybel_7(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f914,f910])).

fof(f914,plain,
    ( v3_waybel_7(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK7(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(resolution,[],[f483,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | v3_waybel_7(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f2278,plain,
    ( ! [X0] :
        ( ~ v3_waybel_7(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(sK1,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),X0) )
    | ~ spl12_1
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f2277,f936])).

fof(f936,plain,
    ( v13_waybel_0(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f935,f109])).

fof(f935,plain,
    ( v13_waybel_0(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f934,f110])).

fof(f934,plain,
    ( v13_waybel_0(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f933,f111])).

fof(f933,plain,
    ( v13_waybel_0(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f932,f112])).

fof(f932,plain,
    ( v13_waybel_0(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f913,f910])).

fof(f913,plain,
    ( v13_waybel_0(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK7(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(resolution,[],[f483,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | v13_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f2277,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v3_waybel_7(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(sK1,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),X0) )
    | ~ spl12_1
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f2265,f931])).

fof(f931,plain,
    ( v2_waybel_0(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f930,f109])).

fof(f930,plain,
    ( v2_waybel_0(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f929,f110])).

fof(f929,plain,
    ( v2_waybel_0(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f928,f111])).

fof(f928,plain,
    ( v2_waybel_0(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f927,f112])).

fof(f927,plain,
    ( v2_waybel_0(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f912,f910])).

fof(f912,plain,
    ( v2_waybel_0(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK7(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(resolution,[],[f483,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | v2_waybel_0(sK5(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f2265,plain,
    ( ! [X0] :
        ( ~ v2_waybel_0(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v3_waybel_7(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k3_yellow_1(k2_struct_0(sK0)))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(sK1,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),X0) )
    | ~ spl12_1
    | ~ spl12_20 ),
    inference(resolution,[],[f946,f253])).

fof(f253,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
        | r2_hidden(X5,sK1)
        | ~ r2_hidden(sK1,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,X4,X5) )
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl12_20
  <=> ! [X5,X4] :
        ( r2_hidden(X5,sK1)
        | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ r2_hidden(sK1,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_waybel_7(sK0,X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f946,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f945,f109])).

fof(f945,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f944,f110])).

fof(f944,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f943,f111])).

fof(f943,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f942,f112])).

fof(f942,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f915,f910])).

fof(f915,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK7(k2_pre_topc(sK0,sK1),sK1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ m1_subset_1(sK7(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(resolution,[],[f483,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f254,plain,
    ( spl12_0
    | spl12_20 ),
    inference(avatar_split_clause,[],[f250,f252,f182])).

fof(f182,plain,
    ( spl12_0
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f250,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK1)
      | ~ r2_waybel_7(sK0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
      | v4_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f113,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t30_yellow19.p',t7_boole)).

fof(f113,plain,(
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
    inference(cnf_transformation,[],[f87])).

fof(f249,plain,
    ( ~ spl12_1
    | ~ spl12_19 ),
    inference(avatar_split_clause,[],[f114,f247,f185])).

fof(f114,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f242,plain,
    ( ~ spl12_1
    | spl12_16 ),
    inference(avatar_split_clause,[],[f115,f240,f185])).

fof(f115,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f235,plain,
    ( ~ spl12_1
    | spl12_14 ),
    inference(avatar_split_clause,[],[f116,f233,f185])).

fof(f116,plain,
    ( v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f228,plain,
    ( ~ spl12_1
    | spl12_12 ),
    inference(avatar_split_clause,[],[f117,f226,f185])).

fof(f117,plain,
    ( v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f221,plain,
    ( ~ spl12_1
    | spl12_10 ),
    inference(avatar_split_clause,[],[f118,f219,f185])).

fof(f118,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f214,plain,
    ( ~ spl12_1
    | spl12_8 ),
    inference(avatar_split_clause,[],[f119,f212,f185])).

fof(f119,plain,
    ( r2_hidden(sK1,sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f207,plain,
    ( ~ spl12_1
    | spl12_6 ),
    inference(avatar_split_clause,[],[f120,f205,f185])).

fof(f120,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f200,plain,
    ( ~ spl12_1
    | spl12_4 ),
    inference(avatar_split_clause,[],[f121,f198,f185])).

fof(f121,plain,
    ( r2_waybel_7(sK0,sK2,sK3)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f193,plain,
    ( ~ spl12_1
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f122,f191,f185])).

fof(f122,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f87])).
%------------------------------------------------------------------------------
