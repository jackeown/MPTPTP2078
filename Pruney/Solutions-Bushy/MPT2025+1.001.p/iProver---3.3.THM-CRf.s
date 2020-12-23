%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2025+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:02 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  248 (1720 expanded)
%              Number of clauses        :  151 ( 412 expanded)
%              Number of leaves         :   26 ( 603 expanded)
%              Depth                    :   30
%              Number of atoms          : 1306 (16441 expanded)
%              Number of equality atoms :  232 (1804 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ( k2_pre_topc(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f41,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( ( r2_hidden(X3,X2)
          <=> ! [X4] :
                ( ~ r1_xboole_0(X1,X4)
                | ~ r2_hidden(X3,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ r2_hidden(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f17,f42,f41])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ( ( k2_pre_topc(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k2_pre_topc(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_pre_topc(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k2_pre_topc(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f44])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k2_pre_topc(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f112,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k2_pre_topc(X1,X2))
      | ~ sP1(k2_pre_topc(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f66])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
          & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(X1,k2_pre_topc(X0,sK11))
        & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = sK11
        & m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
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
            & k2_relset_1(u1_struct_0(sK10),u1_struct_0(X0),u1_waybel_0(X0,sK10)) = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(X1,k10_yellow_6(X0,sK10))
        & l1_waybel_0(sK10,X0)
        & v7_waybel_0(sK10)
        & v4_orders_2(sK10)
        & ~ v2_struct_0(sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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
                ( ~ r2_hidden(sK9,k2_pre_topc(X0,X3))
                & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK9,k10_yellow_6(X0,X2))
            & l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
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
                  ( ~ r2_hidden(X1,k2_pre_topc(sK8,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK8),u1_waybel_0(sK8,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8))) )
              & r2_hidden(X1,k10_yellow_6(sK8,X2))
              & l1_waybel_0(X2,sK8)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(sK8)) )
      & l1_pre_topc(sK8)
      & v2_pre_topc(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ~ r2_hidden(sK9,k2_pre_topc(sK8,sK11))
    & k2_relset_1(u1_struct_0(sK10),u1_struct_0(sK8),u1_waybel_0(sK8,sK10)) = sK11
    & m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK8)))
    & r2_hidden(sK9,k10_yellow_6(sK8,sK10))
    & l1_waybel_0(sK10,sK8)
    & v7_waybel_0(sK10)
    & v4_orders_2(sK10)
    & ~ v2_struct_0(sK10)
    & m1_subset_1(sK9,u1_struct_0(sK8))
    & l1_pre_topc(sK8)
    & v2_pre_topc(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f40,f64,f63,f62,f61])).

fof(f102,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f65])).

fof(f46,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f47,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f46])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ? [X4] :
                  ( r1_xboole_0(X0,X4)
                  & r2_hidden(X3,X4)
                  & v3_pre_topc(X4,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X3,X2) )
            & ( ! [X5] :
                  ( ~ r1_xboole_0(X0,X5)
                  | ~ r2_hidden(X3,X5)
                  | ~ v3_pre_topc(X5,X1)
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X3,X2) )
            & r2_hidden(X3,u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ? [X7] :
                    ( r1_xboole_0(X0,X7)
                    & r2_hidden(X6,X7)
                    & v3_pre_topc(X7,X1)
                    & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( ! [X8] :
                    ( ~ r1_xboole_0(X0,X8)
                    | ~ r2_hidden(X6,X8)
                    | ~ v3_pre_topc(X8,X1)
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ r2_hidden(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f47])).

fof(f51,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( r1_xboole_0(X0,X7)
          & r2_hidden(X6,X7)
          & v3_pre_topc(X7,X1)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r1_xboole_0(X0,sK4(X0,X1,X6))
        & r2_hidden(X6,sK4(X0,X1,X6))
        & v3_pre_topc(sK4(X0,X1,X6),X1)
        & m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( r1_xboole_0(X0,X4)
          & r2_hidden(X3,X4)
          & v3_pre_topc(X4,X1)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r1_xboole_0(X0,sK3(X0,X1,X2))
        & r2_hidden(X3,sK3(X0,X1,X2))
        & v3_pre_topc(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( r1_xboole_0(X0,X4)
                & r2_hidden(X3,X4)
                & v3_pre_topc(X4,X1)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( ~ r1_xboole_0(X0,X5)
                | ~ r2_hidden(X3,X5)
                | ~ v3_pre_topc(X5,X1)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X3,X2) )
          & r2_hidden(X3,u1_struct_0(X1)) )
     => ( ( ? [X4] :
              ( r1_xboole_0(X0,X4)
              & r2_hidden(sK2(X0,X1,X2),X4)
              & v3_pre_topc(X4,X1)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( ~ r1_xboole_0(X0,X5)
              | ~ r2_hidden(sK2(X0,X1,X2),X5)
              | ~ v3_pre_topc(X5,X1)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK2(X0,X1,X2),X2) )
        & r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( r1_xboole_0(X0,sK3(X0,X1,X2))
              & r2_hidden(sK2(X0,X1,X2),sK3(X0,X1,X2))
              & v3_pre_topc(sK3(X0,X1,X2),X1)
              & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ! [X5] :
                ( ~ r1_xboole_0(X0,X5)
                | ~ r2_hidden(sK2(X0,X1,X2),X5)
                | ~ v3_pre_topc(X5,X1)
                | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK2(X0,X1,X2),X2) )
          & r2_hidden(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ( r1_xboole_0(X0,sK4(X0,X1,X6))
                  & r2_hidden(X6,sK4(X0,X1,X6))
                  & v3_pre_topc(sK4(X0,X1,X6),X1)
                  & m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( ! [X8] :
                    ( ~ r1_xboole_0(X0,X8)
                    | ~ r2_hidden(X6,X8)
                    | ~ v3_pre_topc(X8,X1)
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ r2_hidden(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f48,f51,f50,f49])).

fof(f72,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r1_xboole_0(X0,sK4(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f109,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f65])).

fof(f69,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f101,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f65])).

fof(f70,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | v3_pre_topc(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f111,plain,(
    ~ r2_hidden(sK9,k2_pre_topc(sK8,sK11)) ),
    inference(cnf_transformation,[],[f65])).

fof(f100,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f65])).

fof(f104,plain,(
    ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f65])).

fof(f105,plain,(
    v4_orders_2(sK10) ),
    inference(cnf_transformation,[],[f65])).

fof(f107,plain,(
    l1_waybel_0(sK10,sK8) ),
    inference(cnf_transformation,[],[f65])).

fof(f108,plain,(
    r2_hidden(sK9,k10_yellow_6(sK8,sK10)) ),
    inference(cnf_transformation,[],[f65])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f106,plain,(
    v7_waybel_0(sK10) ),
    inference(cnf_transformation,[],[f65])).

fof(f103,plain,(
    m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f65])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f58,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK7(X0,X1,X6))
        & m1_connsp_2(sK7(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK6(X0,X1,X2))
        & m1_connsp_2(sK6(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
              & m1_connsp_2(X4,X0,sK5(X0,X1,X2)) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK5(X0,X1,X2)) )
          | r2_hidden(sK5(X0,X1,X2),X2) )
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK6(X0,X1,X2))
                        & m1_connsp_2(sK6(X0,X1,X2),X0,sK5(X0,X1,X2)) )
                      | ~ r2_hidden(sK5(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK5(X0,X1,X2)) )
                      | r2_hidden(sK5(X0,X1,X2),X2) )
                    & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK7(X0,X1,X6))
                            & m1_connsp_2(sK7(X0,X1,X6),X0,X6) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f55,f58,f57,f56])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f59])).

fof(f115,plain,(
    ! [X6,X0,X8,X1] :
      ( r1_waybel_0(X0,X1,X8)
      | ~ m1_connsp_2(X8,X0,X6)
      | ~ r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f71,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r2_hidden(X6,sK4(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f91,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f110,plain,(
    k2_relset_1(u1_struct_0(sK10),u1_struct_0(sK8),u1_waybel_0(sK8,sK10)) = sK11 ),
    inference(cnf_transformation,[],[f65])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ r1_waybel_0(X0,X1,X3)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_13,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1,plain,
    ( ~ sP1(k2_pre_topc(X0,X1),X0,X1)
    | sP0(X1,X0,k2_pre_topc(X0,X1)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_536,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3)
    | X1 != X3
    | X0 != X4
    | k2_pre_topc(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_1])).

cnf(c_537,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_24])).

cnf(c_542,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_541])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1849,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_542,c_43])).

cnf(c_1850,plain,
    ( sP0(X0,sK8,k2_pre_topc(sK8,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_1849])).

cnf(c_6453,plain,
    ( sP0(X0,sK8,k2_pre_topc(sK8,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1850])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | r1_xboole_0(X0,sK4(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_6484,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) = iProver_top
    | r2_hidden(X3,u1_struct_0(X1)) != iProver_top
    | r1_xboole_0(X0,sK4(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9006,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK8,X0)) = iProver_top
    | r2_hidden(X1,u1_struct_0(sK8)) != iProver_top
    | r1_xboole_0(X0,sK4(X0,sK8,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6453,c_6484])).

cnf(c_26,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_6479,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13524,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK8,X0)) = iProver_top
    | r2_hidden(X1,u1_struct_0(sK8)) != iProver_top
    | r1_xboole_0(sK4(X0,sK8,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9006,c_6479])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_6474,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2)
    | m1_subset_1(sK4(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_6481,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | m1_subset_1(sK4(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | r2_hidden(X3,X2) = iProver_top
    | r2_hidden(X3,u1_struct_0(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9788,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(sK4(X0,sK8,X1),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK8,X0)) = iProver_top
    | r2_hidden(X1,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6453,c_6481])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X3,X2) = X2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1691,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X3,X2) = X2
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_44])).

cnf(c_1692,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK8)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_1691])).

cnf(c_1696,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1692,c_43])).

cnf(c_1697,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_1696])).

cnf(c_1831,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1697,c_43])).

cnf(c_1832,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v3_pre_topc(X1,sK8)
    | k1_tops_1(sK8,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_1831])).

cnf(c_5762,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v3_pre_topc(X0,sK8)
    | k1_tops_1(sK8,X0) = X0
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1832])).

cnf(c_6456,plain,
    ( k1_tops_1(sK8,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v3_pre_topc(X0,sK8) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5762])).

cnf(c_5764,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1832])).

cnf(c_5811,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5764])).

cnf(c_5815,plain,
    ( k1_tops_1(sK8,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v3_pre_topc(X0,sK8) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5762])).

cnf(c_5763,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1832])).

cnf(c_6455,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5763])).

cnf(c_7014,plain,
    ( sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_6474,c_6455])).

cnf(c_7731,plain,
    ( v3_pre_topc(X0,sK8) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | k1_tops_1(sK8,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6456,c_5811,c_5815,c_7014])).

cnf(c_7732,plain,
    ( k1_tops_1(sK8,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v3_pre_topc(X0,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_7731])).

cnf(c_13541,plain,
    ( k1_tops_1(sK8,sK4(X0,sK8,X1)) = sK4(X0,sK8,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v3_pre_topc(sK4(X0,sK8,X1),sK8) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK8,X0)) = iProver_top
    | r2_hidden(X1,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9788,c_7732])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2)
    | v3_pre_topc(sK4(X0,X1,X3),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | v3_pre_topc(sK4(X1,X2,X3),X2)
    | r2_hidden(X3,X4)
    | ~ r2_hidden(X3,u1_struct_0(X2))
    | X0 != X1
    | k2_pre_topc(sK8,X0) != X4
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_1850])).

cnf(c_3375,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | v3_pre_topc(sK4(X0,sK8,X1),sK8)
    | r2_hidden(X1,k2_pre_topc(sK8,X0))
    | ~ r2_hidden(X1,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_3374])).

cnf(c_3376,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v3_pre_topc(sK4(X0,sK8,X1),sK8) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK8,X0)) = iProver_top
    | r2_hidden(X1,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3375])).

cnf(c_13868,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | k1_tops_1(sK8,sK4(X0,sK8,X1)) = sK4(X0,sK8,X1)
    | r2_hidden(X1,k2_pre_topc(sK8,X0)) = iProver_top
    | r2_hidden(X1,u1_struct_0(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13541,c_3376])).

cnf(c_13869,plain,
    ( k1_tops_1(sK8,sK4(X0,sK8,X1)) = sK4(X0,sK8,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK8,X0)) = iProver_top
    | r2_hidden(X1,u1_struct_0(sK8)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13868])).

cnf(c_13874,plain,
    ( k1_tops_1(sK8,sK4(sK11,sK8,X0)) = sK4(sK11,sK8,X0)
    | r2_hidden(X0,k2_pre_topc(sK8,sK11)) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6474,c_13869])).

cnf(c_34,negated_conjecture,
    ( ~ r2_hidden(sK9,k2_pre_topc(sK8,sK11)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_6475,plain,
    ( r2_hidden(sK9,k2_pre_topc(sK8,sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_13937,plain,
    ( k1_tops_1(sK8,sK4(sK11,sK8,sK9)) = sK4(sK11,sK8,sK9)
    | r2_hidden(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13874,c_6475])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_40,negated_conjecture,
    ( v4_orders_2(sK10) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_38,negated_conjecture,
    ( l1_waybel_0(sK10,sK8) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_37,negated_conjecture,
    ( r2_hidden(sK9,k10_yellow_6(sK8,sK10)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_23,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_39,negated_conjecture,
    ( v7_waybel_0(sK10) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_944,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ l1_pre_topc(X1)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_39])).

cnf(c_945,plain,
    ( ~ l1_waybel_0(sK10,X0)
    | m1_subset_1(k10_yellow_6(X0,sK10),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK10)
    | ~ v4_orders_2(sK10)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_944])).

cnf(c_947,plain,
    ( ~ l1_waybel_0(sK10,sK8)
    | m1_subset_1(k10_yellow_6(sK8,sK10),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK10)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(sK10)
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_945])).

cnf(c_6655,plain,
    ( sP0(sK11,sK8,k2_pre_topc(sK8,sK11))
    | ~ m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_1850])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_6472,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_6478,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7152,plain,
    ( r2_hidden(sK9,u1_struct_0(sK8)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6472,c_6478])).

cnf(c_7155,plain,
    ( r2_hidden(sK9,u1_struct_0(sK8))
    | v1_xboole_0(u1_struct_0(sK8)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7152])).

cnf(c_6556,plain,
    ( ~ sP0(X0,X1,k2_pre_topc(sK8,sK11))
    | m1_subset_1(sK4(X0,X1,sK9),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK9,k2_pre_topc(sK8,sK11))
    | ~ r2_hidden(sK9,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_7303,plain,
    ( ~ sP0(sK11,sK8,k2_pre_topc(sK8,sK11))
    | m1_subset_1(sK4(sK11,sK8,sK9),k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(sK9,k2_pre_topc(sK8,sK11))
    | ~ r2_hidden(sK9,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_6556])).

cnf(c_6559,plain,
    ( ~ sP0(X0,X1,k2_pre_topc(sK8,sK11))
    | v3_pre_topc(sK4(X0,X1,sK9),X1)
    | r2_hidden(sK9,k2_pre_topc(sK8,sK11))
    | ~ r2_hidden(sK9,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_7323,plain,
    ( ~ sP0(sK11,sK8,k2_pre_topc(sK8,sK11))
    | v3_pre_topc(sK4(sK11,sK8,sK9),sK8)
    | r2_hidden(sK9,k2_pre_topc(sK8,sK11))
    | ~ r2_hidden(sK9,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_6559])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_6604,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK8,sK10),k1_zfmisc_1(X0))
    | ~ r2_hidden(sK9,k10_yellow_6(sK8,sK10))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_7589,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK8,sK10),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(sK9,k10_yellow_6(sK8,sK10))
    | ~ v1_xboole_0(u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_6604])).

cnf(c_5914,plain,
    ( k1_tops_1(sK8,X0) = X0
    | ~ v3_pre_topc(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5762,c_5764,c_5763])).

cnf(c_5915,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v3_pre_topc(X0,sK8)
    | k1_tops_1(sK8,X0) = X0 ),
    inference(renaming,[status(thm)],[c_5914])).

cnf(c_9095,plain,
    ( ~ m1_subset_1(sK4(X0,sK8,sK9),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v3_pre_topc(sK4(X0,sK8,sK9),sK8)
    | k1_tops_1(sK8,sK4(X0,sK8,sK9)) = sK4(X0,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_5915])).

cnf(c_12732,plain,
    ( ~ m1_subset_1(sK4(sK11,sK8,sK9),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v3_pre_topc(sK4(sK11,sK8,sK9),sK8)
    | k1_tops_1(sK8,sK4(sK11,sK8,sK9)) = sK4(sK11,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_9095])).

cnf(c_13956,plain,
    ( k1_tops_1(sK8,sK4(sK11,sK8,sK9)) = sK4(sK11,sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13937,c_45,c_44,c_43,c_41,c_40,c_38,c_37,c_36,c_34,c_947,c_6655,c_7155,c_7303,c_7323,c_7589,c_12732])).

cnf(c_21,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1643,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_45])).

cnf(c_1644,plain,
    ( m1_connsp_2(X0,sK8,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,k1_tops_1(sK8,X0))
    | ~ v2_pre_topc(sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1643])).

cnf(c_1648,plain,
    ( m1_connsp_2(X0,sK8,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,k1_tops_1(sK8,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1644,c_44,c_43])).

cnf(c_6460,plain,
    ( m1_connsp_2(X0,sK8,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK8,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1648])).

cnf(c_13539,plain,
    ( m1_connsp_2(sK4(X0,sK8,X1),sK8,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X2,k1_tops_1(sK8,sK4(X0,sK8,X1))) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK8,X0)) = iProver_top
    | r2_hidden(X1,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9788,c_6460])).

cnf(c_14247,plain,
    ( m1_connsp_2(sK4(sK11,sK8,sK9),sK8,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X0,sK4(sK11,sK8,sK9)) != iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK8,sK11)) = iProver_top
    | r2_hidden(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13956,c_13539])).

cnf(c_46,plain,
    ( v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_47,plain,
    ( v2_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_48,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_50,plain,
    ( v2_struct_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_51,plain,
    ( v4_orders_2(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_53,plain,
    ( l1_waybel_0(sK10,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_54,plain,
    ( r2_hidden(sK9,k10_yellow_6(sK8,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_55,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_56,plain,
    ( r2_hidden(sK9,k2_pre_topc(sK8,sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_946,plain,
    ( l1_waybel_0(sK10,X0) != iProver_top
    | m1_subset_1(k10_yellow_6(X0,sK10),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v4_orders_2(sK10) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_945])).

cnf(c_948,plain,
    ( l1_waybel_0(sK10,sK8) != iProver_top
    | m1_subset_1(k10_yellow_6(sK8,sK10),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top
    | v2_pre_topc(sK8) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK10) != iProver_top
    | l1_pre_topc(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_946])).

cnf(c_6656,plain,
    ( sP0(sK11,sK8,k2_pre_topc(sK8,sK11)) = iProver_top
    | m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6655])).

cnf(c_7304,plain,
    ( sP0(sK11,sK8,k2_pre_topc(sK8,sK11)) != iProver_top
    | m1_subset_1(sK4(sK11,sK8,sK9),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK8,sK11)) = iProver_top
    | r2_hidden(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7303])).

cnf(c_7590,plain,
    ( m1_subset_1(k10_yellow_6(sK8,sK10),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK9,k10_yellow_6(sK8,sK10)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7589])).

cnf(c_29,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_6636,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,X0) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_9120,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(sK4(sK11,sK8,sK9),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X0,sK4(sK11,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_6636])).

cnf(c_9151,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK4(sK11,sK8,sK9),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X0,sK4(sK11,sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9120])).

cnf(c_14252,plain,
    ( m1_connsp_2(sK4(sK11,sK8,sK9),sK8,X0) = iProver_top
    | r2_hidden(X0,sK4(sK11,sK8,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14247,c_46,c_47,c_48,c_50,c_51,c_53,c_54,c_55,c_56,c_948,c_6656,c_7152,c_7304,c_7590,c_9151])).

cnf(c_6473,plain,
    ( r2_hidden(sK9,k10_yellow_6(sK8,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_20,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,X3,X0)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k10_yellow_6(X1,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k10_yellow_6(X1,X3))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1211,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,X3,X0)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k10_yellow_6(X1,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k10_yellow_6(X1,X3))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ l1_pre_topc(X1)
    | sK10 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_39])).

cnf(c_1212,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK10,X0)
    | ~ l1_waybel_0(sK10,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k10_yellow_6(X1,sK10),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK10))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(sK10)
    | ~ v4_orders_2(sK10)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_1211])).

cnf(c_1216,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK10,X0)
    | ~ l1_waybel_0(sK10,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k10_yellow_6(X1,sK10),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK10))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1212,c_41,c_40])).

cnf(c_949,plain,
    ( ~ l1_waybel_0(sK10,X0)
    | m1_subset_1(k10_yellow_6(X0,sK10),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_945,c_41,c_40])).

cnf(c_1231,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK10,X0)
    | ~ l1_waybel_0(sK10,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK10))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1216,c_949])).

cnf(c_1336,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK10,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK10))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK10 != sK10
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_1231])).

cnf(c_1337,plain,
    ( ~ m1_connsp_2(X0,sK8,X1)
    | r1_waybel_0(sK8,sK10,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,k10_yellow_6(sK8,sK10))
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1336])).

cnf(c_1341,plain,
    ( ~ r2_hidden(X1,k10_yellow_6(sK8,sK10))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r1_waybel_0(sK8,sK10,X0)
    | ~ m1_connsp_2(X0,sK8,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1337,c_45,c_44,c_43])).

cnf(c_1342,plain,
    ( ~ m1_connsp_2(X0,sK8,X1)
    | r1_waybel_0(sK8,sK10,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,k10_yellow_6(sK8,sK10)) ),
    inference(renaming,[status(thm)],[c_1341])).

cnf(c_6470,plain,
    ( m1_connsp_2(X0,sK8,X1) != iProver_top
    | r1_waybel_0(sK8,sK10,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK8,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1342])).

cnf(c_8369,plain,
    ( m1_connsp_2(X0,sK8,sK9) != iProver_top
    | r1_waybel_0(sK8,sK10,X0) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6473,c_6470])).

cnf(c_49,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_9009,plain,
    ( r1_waybel_0(sK8,sK10,X0) = iProver_top
    | m1_connsp_2(X0,sK8,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8369,c_49])).

cnf(c_9010,plain,
    ( m1_connsp_2(X0,sK8,sK9) != iProver_top
    | r1_waybel_0(sK8,sK10,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_9009])).

cnf(c_14259,plain,
    ( r1_waybel_0(sK8,sK10,sK4(sK11,sK8,sK9)) = iProver_top
    | r2_hidden(sK9,sK4(sK11,sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14252,c_9010])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X3,X2)
    | r2_hidden(X3,sK4(X0,X1,X3))
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_6558,plain,
    ( ~ sP0(X0,X1,k2_pre_topc(sK8,sK11))
    | r2_hidden(sK9,sK4(X0,X1,sK9))
    | r2_hidden(sK9,k2_pre_topc(sK8,sK11))
    | ~ r2_hidden(sK9,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7265,plain,
    ( ~ sP0(sK11,sK8,k2_pre_topc(sK8,sK11))
    | r2_hidden(sK9,sK4(sK11,sK8,sK9))
    | r2_hidden(sK9,k2_pre_topc(sK8,sK11))
    | ~ r2_hidden(sK9,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_6558])).

cnf(c_7266,plain,
    ( sP0(sK11,sK8,k2_pre_topc(sK8,sK11)) != iProver_top
    | r2_hidden(sK9,sK4(sK11,sK8,sK9)) = iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK8,sK11)) = iProver_top
    | r2_hidden(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7265])).

cnf(c_14359,plain,
    ( r1_waybel_0(sK8,sK10,sK4(sK11,sK8,sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14259,c_46,c_47,c_48,c_50,c_51,c_53,c_54,c_55,c_56,c_948,c_6656,c_7152,c_7266,c_7590])).

cnf(c_25,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_33,plain,
    ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_567,plain,
    ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_25,c_33])).

cnf(c_1325,plain,
    ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK10 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_567,c_38])).

cnf(c_1326,plain,
    ( r1_waybel_0(sK8,sK10,k2_relset_1(u1_struct_0(sK10),u1_struct_0(sK8),u1_waybel_0(sK8,sK10)))
    | v2_struct_0(sK10)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1325])).

cnf(c_1328,plain,
    ( r1_waybel_0(sK8,sK10,k2_relset_1(u1_struct_0(sK10),u1_struct_0(sK8),u1_waybel_0(sK8,sK10))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1326,c_45,c_43,c_41])).

cnf(c_6471,plain,
    ( r1_waybel_0(sK8,sK10,k2_relset_1(u1_struct_0(sK10),u1_struct_0(sK8),u1_waybel_0(sK8,sK10))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1328])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK10),u1_struct_0(sK8),u1_waybel_0(sK8,sK10)) = sK11 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_6491,plain,
    ( r1_waybel_0(sK8,sK10,sK11) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6471,c_35])).

cnf(c_27,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_587,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_25,c_27])).

cnf(c_1004,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(X0)
    | sK10 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_587,c_39])).

cnf(c_1005,plain,
    ( ~ r1_waybel_0(X0,sK10,X1)
    | ~ r1_waybel_0(X0,sK10,X2)
    | ~ l1_waybel_0(sK10,X0)
    | ~ r1_xboole_0(X1,X2)
    | v2_struct_0(X0)
    | v2_struct_0(sK10)
    | ~ v4_orders_2(sK10)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_1004])).

cnf(c_1009,plain,
    ( ~ r1_waybel_0(X0,sK10,X1)
    | ~ r1_waybel_0(X0,sK10,X2)
    | ~ l1_waybel_0(sK10,X0)
    | ~ r1_xboole_0(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1005,c_41,c_40])).

cnf(c_1010,plain,
    ( ~ r1_waybel_0(X0,sK10,X1)
    | ~ r1_waybel_0(X0,sK10,X2)
    | ~ l1_waybel_0(sK10,X0)
    | ~ r1_xboole_0(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_1009])).

cnf(c_1477,plain,
    ( ~ r1_waybel_0(X0,sK10,X1)
    | ~ r1_waybel_0(X0,sK10,X2)
    | ~ r1_xboole_0(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK10 != sK10
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_1010])).

cnf(c_1478,plain,
    ( ~ r1_waybel_0(sK8,sK10,X0)
    | ~ r1_waybel_0(sK8,sK10,X1)
    | ~ r1_xboole_0(X1,X0)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1477])).

cnf(c_1482,plain,
    ( ~ r1_waybel_0(sK8,sK10,X0)
    | ~ r1_waybel_0(sK8,sK10,X1)
    | ~ r1_xboole_0(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1478,c_45,c_43])).

cnf(c_6464,plain,
    ( r1_waybel_0(sK8,sK10,X0) != iProver_top
    | r1_waybel_0(sK8,sK10,X1) != iProver_top
    | r1_xboole_0(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1482])).

cnf(c_7474,plain,
    ( r1_waybel_0(sK8,sK10,X0) != iProver_top
    | r1_xboole_0(X0,sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_6491,c_6464])).

cnf(c_14363,plain,
    ( r1_xboole_0(sK4(sK11,sK8,sK9),sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_14359,c_7474])).

cnf(c_14370,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK9,k2_pre_topc(sK8,sK11)) = iProver_top
    | r2_hidden(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13524,c_14363])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14370,c_7590,c_7152,c_948,c_56,c_55,c_54,c_53,c_51,c_50,c_48,c_47,c_46])).


%------------------------------------------------------------------------------
