%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_9__t24_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:09 EDT 2019

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 619 expanded)
%              Number of leaves         :   28 ( 245 expanded)
%              Depth                    :   36
%              Number of atoms          : 1207 (6795 expanded)
%              Number of equality atoms :   54 ( 594 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26455,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f211,f233,f254,f21621,f26454])).

fof(f26454,plain,
    ( ~ spl16_6
    | ~ spl16_8 ),
    inference(avatar_contradiction_clause,[],[f26453])).

fof(f26453,plain,
    ( $false
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(subsumption_resolution,[],[f26452,f128])).

fof(f128,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,
    ( ~ r2_hidden(sK1,k2_pre_topc(sK0,sK3))
    & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & r2_hidden(sK1,k10_yellow_6(sK0,sK2))
    & l1_waybel_0(sK2,sK0)
    & v7_waybel_0(sK2)
    & v4_orders_2(sK2)
    & ~ v2_struct_0(sK2)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f97,f96,f95,f94])).

fof(f94,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
                    & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X1,k10_yellow_6(X0,X2))
                & l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,k2_pre_topc(sK0,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK0),u1_waybel_0(sK0,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & r2_hidden(X1,k10_yellow_6(sK0,X2))
              & l1_waybel_0(X2,sK0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X1,k10_yellow_6(X0,X2))
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(sK1,k2_pre_topc(X0,X3))
                & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK1,k10_yellow_6(X0,X2))
            & l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
              & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X1,k10_yellow_6(X0,X2))
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
            & k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)) = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(X1,k10_yellow_6(X0,sK2))
        & l1_waybel_0(sK2,X0)
        & v7_waybel_0(sK2)
        & v4_orders_2(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
          & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(X1,k2_pre_topc(X0,sK3))
        & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = sK3
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X1,k10_yellow_6(X0,X2))
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X1,k10_yellow_6(X0,X2))
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( r2_hidden(X1,k10_yellow_6(X0,X2))
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                       => r2_hidden(X1,k2_pre_topc(X0,X3)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( r2_hidden(X1,k10_yellow_6(X0,X2))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                     => r2_hidden(X1,k2_pre_topc(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',t24_waybel_9)).

fof(f26452,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(subsumption_resolution,[],[f26451,f135])).

fof(f135,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f98])).

fof(f26451,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(subsumption_resolution,[],[f26450,f229])).

fof(f229,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl16_8 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl16_8
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_8])])).

fof(f26450,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f26449,f137])).

fof(f137,plain,(
    ~ r2_hidden(sK1,k2_pre_topc(sK0,sK3)) ),
    inference(cnf_transformation,[],[f98])).

fof(f26449,plain,
    ( r2_hidden(sK1,k2_pre_topc(sK0,sK3))
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl16_6 ),
    inference(duplicate_literal_removal,[],[f26448])).

fof(f26448,plain,
    ( r2_hidden(sK1,k2_pre_topc(sK0,sK3))
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | r2_hidden(sK1,k2_pre_topc(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl16_6 ),
    inference(resolution,[],[f26341,f380])).

fof(f380,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK6(X1,X2,X0))
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | r2_hidden(X0,k2_pre_topc(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f375])).

fof(f375,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK6(X1,X2,X0))
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | r2_hidden(X0,k2_pre_topc(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f191,f177])).

fof(f177,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',dt_k2_pre_topc)).

fof(f191,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X6,sK6(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | r2_hidden(X6,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f145])).

fof(f145,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r2_hidden(X6,sK6(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ( ( ( r1_xboole_0(X1,sK5(X0,X1,X2))
                        & r2_hidden(sK4(X0,X1,X2),sK5(X0,X1,X2))
                        & v3_pre_topc(sK5(X0,X1,X2),X0)
                        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                      | ~ r2_hidden(sK4(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( ~ r1_xboole_0(X1,X5)
                          | ~ r2_hidden(sK4(X0,X1,X2),X5)
                          | ~ v3_pre_topc(X5,X0)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                      | r2_hidden(sK4(X0,X1,X2),X2) )
                    & r2_hidden(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( r1_xboole_0(X1,sK6(X0,X1,X6))
                            & r2_hidden(X6,sK6(X0,X1,X6))
                            & v3_pre_topc(sK6(X0,X1,X6),X0)
                            & m1_subset_1(sK6(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X8] :
                              ( ~ r1_xboole_0(X1,X8)
                              | ~ r2_hidden(X6,X8)
                              | ~ v3_pre_topc(X8,X0)
                              | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ r2_hidden(X6,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f101,f104,f103,f102])).

fof(f102,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( r1_xboole_0(X1,X4)
                & r2_hidden(X3,X4)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( ~ r1_xboole_0(X1,X5)
                | ~ r2_hidden(X3,X5)
                | ~ v3_pre_topc(X5,X0)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X3,X2) )
          & r2_hidden(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( r1_xboole_0(X1,X4)
              & r2_hidden(sK4(X0,X1,X2),X4)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( ~ r1_xboole_0(X1,X5)
              | ~ r2_hidden(sK4(X0,X1,X2),X5)
              | ~ v3_pre_topc(X5,X0)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK4(X0,X1,X2),X2) )
        & r2_hidden(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( r1_xboole_0(X1,X4)
          & r2_hidden(X3,X4)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK5(X0,X1,X2))
        & r2_hidden(X3,sK5(X0,X1,X2))
        & v3_pre_topc(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f104,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( r1_xboole_0(X1,X7)
          & r2_hidden(X6,X7)
          & v3_pre_topc(X7,X0)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK6(X0,X1,X6))
        & r2_hidden(X6,sK6(X0,X1,X6))
        & v3_pre_topc(sK6(X0,X1,X6),X0)
        & m1_subset_1(sK6(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( r1_xboole_0(X1,X4)
                            & r2_hidden(X3,X4)
                            & v3_pre_topc(X4,X0)
                            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X5] :
                            ( ~ r1_xboole_0(X1,X5)
                            | ~ r2_hidden(X3,X5)
                            | ~ v3_pre_topc(X5,X0)
                            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        | r2_hidden(X3,X2) )
                      & r2_hidden(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ? [X7] :
                              ( r1_xboole_0(X1,X7)
                              & r2_hidden(X6,X7)
                              & v3_pre_topc(X7,X0)
                              & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X8] :
                              ( ~ r1_xboole_0(X1,X8)
                              | ~ r2_hidden(X6,X8)
                              | ~ v3_pre_topc(X8,X0)
                              | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ r2_hidden(X6,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f100])).

fof(f100,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( r1_xboole_0(X1,X4)
                            & r2_hidden(X3,X4)
                            & v3_pre_topc(X4,X0)
                            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( ~ r1_xboole_0(X1,X4)
                            | ~ r2_hidden(X3,X4)
                            | ~ v3_pre_topc(X4,X0)
                            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | r2_hidden(X3,X2) )
                      & r2_hidden(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0)
                              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X4] :
                              ( ~ r1_xboole_0(X1,X4)
                              | ~ r2_hidden(X3,X4)
                              | ~ v3_pre_topc(X4,X0)
                              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ r2_hidden(X3,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k2_pre_topc(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( r1_xboole_0(X1,X4)
                            & r2_hidden(X3,X4)
                            & v3_pre_topc(X4,X0)
                            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( ~ r1_xboole_0(X1,X4)
                            | ~ r2_hidden(X3,X4)
                            | ~ v3_pre_topc(X4,X0)
                            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                        | r2_hidden(X3,X2) )
                      & r2_hidden(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0)
                              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        & ( ! [X4] :
                              ( ~ r1_xboole_0(X1,X4)
                              | ~ r2_hidden(X3,X4)
                              | ~ v3_pre_topc(X4,X0)
                              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ r2_hidden(X3,u1_struct_0(X0)) )
                  | k2_pre_topc(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( r2_hidden(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',d13_pre_topc)).

fof(f26341,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,sK6(sK0,sK3,X0))
        | r2_hidden(X0,k2_pre_topc(sK0,sK3))
        | ~ r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f26340,f128])).

fof(f26340,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_pre_topc(sK0,sK3))
        | ~ r2_hidden(sK1,sK6(sK0,sK3,X0))
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f26339,f135])).

fof(f26339,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,k2_pre_topc(sK0,sK3))
        | ~ r2_hidden(sK1,sK6(sK0,sK3,X0))
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl16_6 ),
    inference(duplicate_literal_removal,[],[f26338])).

fof(f26338,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,k2_pre_topc(sK0,sK3))
        | ~ r2_hidden(sK1,sK6(sK0,sK3,X0))
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k2_pre_topc(sK0,sK3))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl16_6 ),
    inference(resolution,[],[f19989,f699])).

fof(f699,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(sK6(X1,X2,X0),X2)
      | r2_hidden(X0,k2_pre_topc(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f372,f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',symmetry_r1_xboole_0)).

fof(f372,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,sK6(X1,X0,X2))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | r2_hidden(X2,k2_pre_topc(X1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f367])).

fof(f367,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,sK6(X1,X0,X2))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | r2_hidden(X2,k2_pre_topc(X1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f190,f177])).

fof(f190,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_xboole_0(X1,sK6(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | r2_hidden(X6,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f146])).

fof(f146,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r1_xboole_0(X1,sK6(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f19989,plain,
    ( ! [X2,X1] :
        ( ~ r1_xboole_0(sK6(sK0,X2,X1),sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,k2_pre_topc(sK0,X2))
        | ~ r2_hidden(sK1,sK6(sK0,X2,X1))
        | ~ r2_hidden(X1,u1_struct_0(sK0)) )
    | ~ spl16_6 ),
    inference(resolution,[],[f17607,f362])).

fof(f362,plain,(
    ! [X3] :
      ( ~ r1_waybel_0(sK0,sK2,X3)
      | ~ r1_xboole_0(X3,sK3) ) ),
    inference(subsumption_resolution,[],[f361,f126])).

fof(f126,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f361,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(X3,sK3)
      | ~ r1_waybel_0(sK0,sK2,X3)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f360,f213])).

fof(f213,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f141,f128])).

fof(f141,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',dt_l1_pre_topc)).

fof(f360,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(X3,sK3)
      | ~ r1_waybel_0(sK0,sK2,X3)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f359,f130])).

fof(f130,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f98])).

fof(f359,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(X3,sK3)
      | ~ r1_waybel_0(sK0,sK2,X3)
      | v2_struct_0(sK2)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f358,f131])).

fof(f131,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f98])).

fof(f358,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(X3,sK3)
      | ~ r1_waybel_0(sK0,sK2,X3)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f357,f132])).

fof(f132,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f98])).

fof(f357,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(X3,sK3)
      | ~ r1_waybel_0(sK0,sK2,X3)
      | ~ v7_waybel_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f355,f133])).

fof(f133,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f355,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(X3,sK3)
      | ~ r1_waybel_0(sK0,sK2,X3)
      | ~ l1_waybel_0(sK2,sK0)
      | ~ v7_waybel_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f164,f326])).

fof(f326,plain,(
    r1_waybel_0(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f325,f126])).

fof(f325,plain,
    ( r1_waybel_0(sK0,sK2,sK3)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f324,f213])).

fof(f324,plain,
    ( r1_waybel_0(sK0,sK2,sK3)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f323,f130])).

fof(f323,plain,
    ( r1_waybel_0(sK0,sK2,sK3)
    | v2_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f321,f133])).

fof(f321,plain,
    ( r1_waybel_0(sK0,sK2,sK3)
    | ~ l1_waybel_0(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f165,f136])).

fof(f136,plain,(
    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = sK3 ),
    inference(cnf_transformation,[],[f98])).

fof(f165,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',t8_waybel_9)).

fof(f164,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_waybel_0(X0,X1,X3)
      | ~ r1_xboole_0(X2,X3)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ~ r1_xboole_0(X2,X3)
              | ~ r1_waybel_0(X0,X1,X3)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ~ r1_xboole_0(X2,X3)
              | ~ r1_waybel_0(X0,X1,X3)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ~ ( r1_xboole_0(X2,X3)
                & r1_waybel_0(X0,X1,X3)
                & r1_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',t26_yellow_6)).

fof(f17607,plain,
    ( ! [X120,X119] :
        ( r1_waybel_0(sK0,sK2,sK6(sK0,X119,X120))
        | ~ r2_hidden(X120,u1_struct_0(sK0))
        | ~ m1_subset_1(X119,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X120,k2_pre_topc(sK0,X119))
        | ~ r2_hidden(sK1,sK6(sK0,X119,X120)) )
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f17606,f126])).

fof(f17606,plain,
    ( ! [X120,X119] :
        ( ~ r2_hidden(sK1,sK6(sK0,X119,X120))
        | v2_struct_0(sK0)
        | ~ r2_hidden(X120,u1_struct_0(sK0))
        | ~ m1_subset_1(X119,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X120,k2_pre_topc(sK0,X119))
        | r1_waybel_0(sK0,sK2,sK6(sK0,X119,X120)) )
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f17605,f127])).

fof(f127,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f17605,plain,
    ( ! [X120,X119] :
        ( ~ r2_hidden(sK1,sK6(sK0,X119,X120))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(X120,u1_struct_0(sK0))
        | ~ m1_subset_1(X119,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X120,k2_pre_topc(sK0,X119))
        | r1_waybel_0(sK0,sK2,sK6(sK0,X119,X120)) )
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f17574,f128])).

fof(f17574,plain,
    ( ! [X120,X119] :
        ( ~ r2_hidden(sK1,sK6(sK0,X119,X120))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(X120,u1_struct_0(sK0))
        | ~ m1_subset_1(X119,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X120,k2_pre_topc(sK0,X119))
        | r1_waybel_0(sK0,sK2,sK6(sK0,X119,X120)) )
    | ~ spl16_6 ),
    inference(resolution,[],[f4091,f921])).

fof(f921,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK1)
      | r1_waybel_0(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f920,f126])).

fof(f920,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK1)
      | r1_waybel_0(sK0,sK2,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f919,f127])).

fof(f919,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK1)
      | r1_waybel_0(sK0,sK2,X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f918,f128])).

fof(f918,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK1)
      | r1_waybel_0(sK0,sK2,X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f917,f130])).

fof(f917,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK1)
      | r1_waybel_0(sK0,sK2,X0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f916,f131])).

fof(f916,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK1)
      | r1_waybel_0(sK0,sK2,X0)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f915,f132])).

fof(f915,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK1)
      | r1_waybel_0(sK0,sK2,X0)
      | ~ v7_waybel_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f912,f133])).

fof(f912,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK1)
      | r1_waybel_0(sK0,sK2,X0)
      | ~ l1_waybel_0(sK2,sK0)
      | ~ v7_waybel_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f439,f134])).

fof(f134,plain,(
    r2_hidden(sK1,k10_yellow_6(sK0,sK2)) ),
    inference(cnf_transformation,[],[f98])).

fof(f439,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,k10_yellow_6(X1,X3))
      | ~ m1_connsp_2(X0,X1,X2)
      | r1_waybel_0(X1,X3,X0)
      | ~ l1_waybel_0(X3,X1)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f438,f329])).

fof(f329,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k10_yellow_6(X3,X2))
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_waybel_0(X2,X3) ) ),
    inference(resolution,[],[f173,f185])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',t4_subset)).

fof(f173,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',dt_k10_yellow_6)).

fof(f438,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X0,X1,X2)
      | ~ r2_hidden(X2,k10_yellow_6(X1,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_waybel_0(X1,X3,X0)
      | ~ l1_waybel_0(X3,X1)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f435])).

fof(f435,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X0,X1,X2)
      | ~ r2_hidden(X2,k10_yellow_6(X1,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_waybel_0(X1,X3,X0)
      | ~ l1_waybel_0(X3,X1)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X3,X1)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f197,f173])).

fof(f197,plain,(
    ! [X6,X0,X8,X1] :
      ( ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X8,X0,X6)
      | ~ r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | r1_waybel_0(X0,X1,X8)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f157])).

fof(f157,plain,(
    ! [X6,X2,X0,X8,X1] :
      ( r1_waybel_0(X0,X1,X8)
      | ~ m1_connsp_2(X8,X0,X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK9(X0,X1,X2))
                        & m1_connsp_2(sK9(X0,X1,X2),X0,sK8(X0,X1,X2)) )
                      | ~ r2_hidden(sK8(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK8(X0,X1,X2)) )
                      | r2_hidden(sK8(X0,X1,X2),X2) )
                    & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK10(X0,X1,X6))
                            & m1_connsp_2(sK10(X0,X1,X6),X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f111,f114,f113,f112])).

fof(f112,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_waybel_0(X0,X1,X4)
                & m1_connsp_2(X4,X0,X3) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( r1_waybel_0(X0,X1,X5)
                | ~ m1_connsp_2(X5,X0,X3) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( ~ r1_waybel_0(X0,X1,X4)
              & m1_connsp_2(X4,X0,sK8(X0,X1,X2)) )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK8(X0,X1,X2)) )
          | r2_hidden(sK8(X0,X1,X2),X2) )
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f113,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK9(X0,X1,X2))
        & m1_connsp_2(sK9(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f114,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK10(X0,X1,X6))
        & m1_connsp_2(sK10(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f111,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X5] :
                            ( r1_waybel_0(X0,X1,X5)
                            | ~ m1_connsp_2(X5,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ? [X7] :
                              ( ~ r1_waybel_0(X0,X1,X7)
                              & m1_connsp_2(X7,X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f110])).

fof(f110,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f109])).

fof(f109,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_connsp_2(X4,X0,X3)
                         => r1_waybel_0(X0,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',d18_yellow_6)).

fof(f4091,plain,
    ( ! [X6,X4,X7,X5] :
        ( m1_connsp_2(sK6(X4,X5,X6),X4,X7)
        | ~ r2_hidden(X7,sK6(X4,X5,X6))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4)
        | ~ r2_hidden(X6,u1_struct_0(X4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | r2_hidden(X6,k2_pre_topc(X4,X5)) )
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f4089,f177])).

fof(f4089,plain,
    ( ! [X6,X4,X7,X5] :
        ( m1_connsp_2(sK6(X4,X5,X6),X4,X7)
        | ~ r2_hidden(X7,sK6(X4,X5,X6))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4)
        | ~ r2_hidden(X6,u1_struct_0(X4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | r2_hidden(X6,k2_pre_topc(X4,X5))
        | ~ m1_subset_1(k2_pre_topc(X4,X5),k1_zfmisc_1(u1_struct_0(X4))) )
    | ~ spl16_6 ),
    inference(duplicate_literal_removal,[],[f4086])).

fof(f4086,plain,
    ( ! [X6,X4,X7,X5] :
        ( m1_connsp_2(sK6(X4,X5,X6),X4,X7)
        | ~ r2_hidden(X7,sK6(X4,X5,X6))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4)
        | ~ r2_hidden(X6,u1_struct_0(X4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | r2_hidden(X6,k2_pre_topc(X4,X5))
        | r2_hidden(X6,k2_pre_topc(X4,X5))
        | ~ r2_hidden(X6,u1_struct_0(X4))
        | ~ m1_subset_1(k2_pre_topc(X4,X5),k1_zfmisc_1(u1_struct_0(X4)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) )
    | ~ spl16_6 ),
    inference(resolution,[],[f812,f193])).

fof(f193,plain,(
    ! [X6,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X6,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f143])).

fof(f143,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_subset_1(sK6(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f812,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        | m1_connsp_2(sK6(X0,X1,X2),X0,X3)
        | ~ r2_hidden(X3,sK6(X0,X1,X2))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ r2_hidden(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r2_hidden(X2,k2_pre_topc(X0,X1)) )
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f811,f185])).

fof(f811,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X3,sK6(X0,X1,X2))
        | m1_connsp_2(sK6(X0,X1,X2),X0,X3)
        | ~ m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ r2_hidden(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r2_hidden(X2,k2_pre_topc(X0,X1)) )
    | ~ spl16_6 ),
    inference(duplicate_literal_removal,[],[f793])).

fof(f793,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X3,sK6(X0,X1,X2))
        | m1_connsp_2(sK6(X0,X1,X2),X0,X3)
        | ~ m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ r2_hidden(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | r2_hidden(X2,k2_pre_topc(X0,X1)) )
    | ~ spl16_6 ),
    inference(superposition,[],[f156,f411])).

fof(f411,plain,
    ( ! [X6,X4,X5] :
        ( k1_tops_1(X5,sK6(X5,X6,X4)) = sK6(X5,X6,X4)
        | ~ r2_hidden(X4,u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5)
        | r2_hidden(X4,k2_pre_topc(X5,X6)) )
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f410,f177])).

fof(f410,plain,
    ( ! [X6,X4,X5] :
        ( r2_hidden(X4,k2_pre_topc(X5,X6))
        | ~ r2_hidden(X4,u1_struct_0(X5))
        | ~ m1_subset_1(k2_pre_topc(X5,X6),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5)
        | k1_tops_1(X5,sK6(X5,X6,X4)) = sK6(X5,X6,X4) )
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f407,f192])).

fof(f192,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK6(X0,X1,X6),X0)
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | r2_hidden(X6,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f144])).

fof(f144,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | v3_pre_topc(sK6(X0,X1,X6),X0)
      | ~ r2_hidden(X6,u1_struct_0(X0))
      | k2_pre_topc(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f407,plain,
    ( ! [X6,X4,X5] :
        ( r2_hidden(X4,k2_pre_topc(X5,X6))
        | ~ r2_hidden(X4,u1_struct_0(X5))
        | ~ m1_subset_1(k2_pre_topc(X5,X6),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5)
        | k1_tops_1(X5,sK6(X5,X6,X4)) = sK6(X5,X6,X4)
        | ~ v3_pre_topc(sK6(X5,X6,X4),X5) )
    | ~ spl16_6 ),
    inference(duplicate_literal_removal,[],[f403])).

fof(f403,plain,
    ( ! [X6,X4,X5] :
        ( r2_hidden(X4,k2_pre_topc(X5,X6))
        | ~ r2_hidden(X4,u1_struct_0(X5))
        | ~ m1_subset_1(k2_pre_topc(X5,X6),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | k1_tops_1(X5,sK6(X5,X6,X4)) = sK6(X5,X6,X4)
        | ~ v3_pre_topc(sK6(X5,X6,X4),X5) )
    | ~ spl16_6 ),
    inference(resolution,[],[f193,f210])).

fof(f210,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl16_6 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl16_6
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',d1_connsp_2)).

fof(f21621,plain,(
    ~ spl16_10 ),
    inference(avatar_contradiction_clause,[],[f21620])).

fof(f21620,plain,
    ( $false
    | ~ spl16_10 ),
    inference(subsumption_resolution,[],[f232,f21613])).

fof(f21613,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f21612,f133])).

fof(f21612,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_waybel_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f21611,f126])).

fof(f21611,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_waybel_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f21610,f127])).

fof(f21610,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_waybel_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f21609,f128])).

fof(f21609,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_waybel_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f21608,f130])).

fof(f21608,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_waybel_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f21607,f131])).

fof(f21607,plain,
    ( ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_waybel_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f714,f132])).

fof(f714,plain,
    ( ~ v7_waybel_0(sK2)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_waybel_0(sK2,sK0) ),
    inference(resolution,[],[f330,f134])).

fof(f330,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k10_yellow_6(X6,X5))
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ v1_xboole_0(u1_struct_0(X6))
      | ~ l1_waybel_0(X5,X6) ) ),
    inference(resolution,[],[f173,f186])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',t5_subset)).

fof(f232,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl16_10 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl16_10
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).

fof(f254,plain,(
    ~ spl16_4 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl16_4 ),
    inference(subsumption_resolution,[],[f252,f128])).

fof(f252,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl16_4 ),
    inference(subsumption_resolution,[],[f250,f127])).

fof(f250,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl16_4 ),
    inference(resolution,[],[f207,f135])).

fof(f207,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl16_4 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl16_4
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f233,plain,
    ( spl16_8
    | spl16_10 ),
    inference(avatar_split_clause,[],[f224,f231,f228])).

fof(f224,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f172,f129])).

fof(f129,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f98])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',t2_subset)).

fof(f211,plain,
    ( spl16_4
    | spl16_6 ),
    inference(avatar_split_clause,[],[f166,f209,f206])).

fof(f166,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t24_waybel_9.p',t55_tops_1)).
%------------------------------------------------------------------------------
