%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2025+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:03 EST 2020

% Result     : Theorem 6.43s
% Output     : CNFRefutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :  257 (1917 expanded)
%              Number of clauses        :  166 ( 465 expanded)
%              Number of leaves         :   24 ( 676 expanded)
%              Depth                    :   32
%              Number of atoms          : 1353 (18510 expanded)
%              Number of equality atoms :  224 (1972 expanded)
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

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ( k2_pre_topc(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f42,plain,(
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

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f17,f43,f42])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ( ( k2_pre_topc(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k2_pre_topc(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_pre_topc(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k2_pre_topc(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k2_pre_topc(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f115,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k2_pre_topc(X1,X2))
      | ~ sP1(k2_pre_topc(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f69])).

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

fof(f93,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
          & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(X1,k2_pre_topc(X0,sK12))
        & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = sK12
        & m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
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
            & k2_relset_1(u1_struct_0(sK11),u1_struct_0(X0),u1_waybel_0(X0,sK11)) = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(X1,k10_yellow_6(X0,sK11))
        & l1_waybel_0(sK11,X0)
        & v7_waybel_0(sK11)
        & v4_orders_2(sK11)
        & ~ v2_struct_0(sK11) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
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
                ( ~ r2_hidden(sK10,k2_pre_topc(X0,X3))
                & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK10,k10_yellow_6(X0,X2))
            & l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
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
                  ( ~ r2_hidden(X1,k2_pre_topc(sK9,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK9),u1_waybel_0(sK9,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK9))) )
              & r2_hidden(X1,k10_yellow_6(sK9,X2))
              & l1_waybel_0(X2,sK9)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(sK9)) )
      & l1_pre_topc(sK9)
      & v2_pre_topc(sK9)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ~ r2_hidden(sK10,k2_pre_topc(sK9,sK12))
    & k2_relset_1(u1_struct_0(sK11),u1_struct_0(sK9),u1_waybel_0(sK9,sK11)) = sK12
    & m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK9)))
    & r2_hidden(sK10,k10_yellow_6(sK9,sK11))
    & l1_waybel_0(sK11,sK9)
    & v7_waybel_0(sK11)
    & v4_orders_2(sK11)
    & ~ v2_struct_0(sK11)
    & m1_subset_1(sK10,u1_struct_0(sK9))
    & l1_pre_topc(sK9)
    & v2_pre_topc(sK9)
    & ~ v2_struct_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12])],[f41,f67,f66,f65,f64])).

fof(f105,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f68])).

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
    inference(nnf_transformation,[],[f42])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f49,f52,f51,f50])).

fof(f75,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r1_xboole_0(X0,sK4(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f112,plain,(
    m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(cnf_transformation,[],[f68])).

fof(f72,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

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
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f104,plain,(
    v2_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f68])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | v3_pre_topc(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f114,plain,(
    ~ r2_hidden(sK10,k2_pre_topc(sK9,sK12)) ),
    inference(cnf_transformation,[],[f68])).

fof(f111,plain,(
    r2_hidden(sK10,k10_yellow_6(sK9,sK11)) ),
    inference(cnf_transformation,[],[f68])).

fof(f106,plain,(
    m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f68])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f110,plain,(
    l1_waybel_0(sK11,sK9) ),
    inference(cnf_transformation,[],[f68])).

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

fof(f92,plain,(
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

fof(f109,plain,(
    v7_waybel_0(sK11) ),
    inference(cnf_transformation,[],[f68])).

fof(f107,plain,(
    ~ v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f68])).

fof(f108,plain,(
    v4_orders_2(sK11) ),
    inference(cnf_transformation,[],[f68])).

fof(f103,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f68])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f61,plain,(
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

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

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
    inference(nnf_transformation,[],[f19])).

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
    inference(flattening,[],[f54])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f59,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK7(X0,X1,X6))
        & m1_connsp_2(sK7(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK6(X0,X1,X2))
        & m1_connsp_2(sK6(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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

fof(f60,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f56,f59,f58,f57])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f118,plain,(
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
    inference(equality_resolution,[],[f83])).

fof(f74,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r2_hidden(X6,sK4(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f94,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f113,plain,(
    k2_relset_1(u1_struct_0(sK11),u1_struct_0(sK9),u1_waybel_0(sK9,sK11)) = sK12 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_13,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1,plain,
    ( ~ sP1(k2_pre_topc(X0,X1),X0,X1)
    | sP0(X1,X0,k2_pre_topc(X0,X1)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_543,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3)
    | X1 != X3
    | X0 != X4
    | k2_pre_topc(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_1])).

cnf(c_544,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_548,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_544,c_24])).

cnf(c_549,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_548])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2221,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_549,c_43])).

cnf(c_2222,plain,
    ( sP0(X0,sK9,k2_pre_topc(sK9,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(unflattening,[status(thm)],[c_2221])).

cnf(c_6265,plain,
    ( sP0(X0_62,sK9,k2_pre_topc(sK9,X0_62))
    | ~ m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(subtyping,[status(esa)],[c_2222])).

cnf(c_7062,plain,
    ( sP0(X0_62,sK9,k2_pre_topc(sK9,X0_62)) = iProver_top
    | m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6265])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | r1_xboole_0(X0,sK4(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_6293,plain,
    ( ~ sP0(X0_62,X0_63,X1_62)
    | r2_hidden(X2_62,X1_62)
    | ~ r2_hidden(X2_62,u1_struct_0(X0_63))
    | r1_xboole_0(X0_62,sK4(X0_62,X0_63,X2_62)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_7031,plain,
    ( sP0(X0_62,X0_63,X1_62) != iProver_top
    | r2_hidden(X2_62,X1_62) = iProver_top
    | r2_hidden(X2_62,u1_struct_0(X0_63)) != iProver_top
    | r1_xboole_0(X0_62,sK4(X0_62,X0_63,X2_62)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6293])).

cnf(c_8441,plain,
    ( m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | r2_hidden(X1_62,k2_pre_topc(sK9,X0_62)) = iProver_top
    | r2_hidden(X1_62,u1_struct_0(sK9)) != iProver_top
    | r1_xboole_0(X0_62,sK4(X0_62,sK9,X1_62)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7062,c_7031])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_6284,negated_conjecture,
    ( m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_7039,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6284])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2)
    | m1_subset_1(sK4(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_6290,plain,
    ( ~ sP0(X0_62,X0_63,X1_62)
    | m1_subset_1(sK4(X0_62,X0_63,X2_62),k1_zfmisc_1(u1_struct_0(X0_63)))
    | r2_hidden(X2_62,X1_62)
    | ~ r2_hidden(X2_62,u1_struct_0(X0_63)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_7034,plain,
    ( sP0(X0_62,X0_63,X1_62) != iProver_top
    | m1_subset_1(sK4(X0_62,X0_63,X2_62),k1_zfmisc_1(u1_struct_0(X0_63))) = iProver_top
    | r2_hidden(X2_62,X1_62) = iProver_top
    | r2_hidden(X2_62,u1_struct_0(X0_63)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6290])).

cnf(c_9274,plain,
    ( m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | m1_subset_1(sK4(X0_62,sK9,X1_62),k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top
    | r2_hidden(X1_62,k2_pre_topc(sK9,X0_62)) = iProver_top
    | r2_hidden(X1_62,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7062,c_7034])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X3,X2) = X2 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2062,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X3,X2) = X2
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_44])).

cnf(c_2063,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK9)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_2062])).

cnf(c_2067,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2063,c_43])).

cnf(c_2068,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_2067])).

cnf(c_2203,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2068,c_43])).

cnf(c_2204,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v3_pre_topc(X1,sK9)
    | k1_tops_1(sK9,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_2203])).

cnf(c_6266,plain,
    ( ~ m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X1_62,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v3_pre_topc(X1_62,sK9)
    | k1_tops_1(sK9,X1_62) = X1_62 ),
    inference(subtyping,[status(esa)],[c_2204])).

cnf(c_6303,plain,
    ( ~ m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v3_pre_topc(X0_62,sK9)
    | k1_tops_1(sK9,X0_62) = X0_62
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_6266])).

cnf(c_7061,plain,
    ( k1_tops_1(sK9,X0_62) = X0_62
    | m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | v3_pre_topc(X0_62,sK9) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6303])).

cnf(c_6304,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_6266])).

cnf(c_6412,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6304])).

cnf(c_6414,plain,
    ( k1_tops_1(sK9,X0_62) = X0_62
    | m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | v3_pre_topc(X0_62,sK9) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6303])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | v3_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2087,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_44])).

cnf(c_2088,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | v3_pre_topc(X2,sK9)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK9)
    | k1_tops_1(sK9,X2) != X2 ),
    inference(unflattening,[status(thm)],[c_2087])).

cnf(c_2092,plain,
    ( ~ l1_pre_topc(X1)
    | v3_pre_topc(X2,sK9)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(sK9,X2) != X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2088,c_43])).

cnf(c_2093,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | v3_pre_topc(X2,sK9)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(sK9,X2) != X2 ),
    inference(renaming,[status(thm)],[c_2092])).

cnf(c_2185,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | v3_pre_topc(X2,sK9)
    | k1_tops_1(sK9,X2) != X2
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2093,c_43])).

cnf(c_2186,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK9)))
    | v3_pre_topc(X0,sK9)
    | k1_tops_1(sK9,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_2185])).

cnf(c_6267,plain,
    ( ~ m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X1_62,k1_zfmisc_1(u1_struct_0(sK9)))
    | v3_pre_topc(X0_62,sK9)
    | k1_tops_1(sK9,X0_62) != X0_62 ),
    inference(subtyping,[status(esa)],[c_2186])).

cnf(c_6300,plain,
    ( ~ m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_6267])).

cnf(c_7058,plain,
    ( m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6300])).

cnf(c_7530,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_7039,c_7058])).

cnf(c_8977,plain,
    ( v3_pre_topc(X0_62,sK9) != iProver_top
    | m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | k1_tops_1(sK9,X0_62) = X0_62 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7061,c_6412,c_6414,c_7530])).

cnf(c_8978,plain,
    ( k1_tops_1(sK9,X0_62) = X0_62
    | m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | v3_pre_topc(X0_62,sK9) != iProver_top ),
    inference(renaming,[status(thm)],[c_8977])).

cnf(c_13490,plain,
    ( k1_tops_1(sK9,sK4(X0_62,sK9,X1_62)) = sK4(X0_62,sK9,X1_62)
    | m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | v3_pre_topc(sK4(X0_62,sK9,X1_62),sK9) != iProver_top
    | r2_hidden(X1_62,k2_pre_topc(sK9,X0_62)) = iProver_top
    | r2_hidden(X1_62,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9274,c_8978])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2)
    | v3_pre_topc(sK4(X0,X1,X3),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_6291,plain,
    ( ~ sP0(X0_62,X0_63,X1_62)
    | v3_pre_topc(sK4(X0_62,X0_63,X2_62),X0_63)
    | r2_hidden(X2_62,X1_62)
    | ~ r2_hidden(X2_62,u1_struct_0(X0_63)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_7033,plain,
    ( sP0(X0_62,X0_63,X1_62) != iProver_top
    | v3_pre_topc(sK4(X0_62,X0_63,X2_62),X0_63) = iProver_top
    | r2_hidden(X2_62,X1_62) = iProver_top
    | r2_hidden(X2_62,u1_struct_0(X0_63)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6291])).

cnf(c_8511,plain,
    ( m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | v3_pre_topc(sK4(X0_62,sK9,X1_62),sK9) = iProver_top
    | r2_hidden(X1_62,k2_pre_topc(sK9,X0_62)) = iProver_top
    | r2_hidden(X1_62,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7062,c_7033])).

cnf(c_16585,plain,
    ( m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | k1_tops_1(sK9,sK4(X0_62,sK9,X1_62)) = sK4(X0_62,sK9,X1_62)
    | r2_hidden(X1_62,k2_pre_topc(sK9,X0_62)) = iProver_top
    | r2_hidden(X1_62,u1_struct_0(sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13490,c_8511])).

cnf(c_16586,plain,
    ( k1_tops_1(sK9,sK4(X0_62,sK9,X1_62)) = sK4(X0_62,sK9,X1_62)
    | m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | r2_hidden(X1_62,k2_pre_topc(sK9,X0_62)) = iProver_top
    | r2_hidden(X1_62,u1_struct_0(sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_16585])).

cnf(c_16595,plain,
    ( k1_tops_1(sK9,sK4(sK12,sK9,X0_62)) = sK4(sK12,sK9,X0_62)
    | r2_hidden(X0_62,k2_pre_topc(sK9,sK12)) = iProver_top
    | r2_hidden(X0_62,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7039,c_16586])).

cnf(c_34,negated_conjecture,
    ( ~ r2_hidden(sK10,k2_pre_topc(sK9,sK12)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_6286,negated_conjecture,
    ( ~ r2_hidden(sK10,k2_pre_topc(sK9,sK12)) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_7038,plain,
    ( r2_hidden(sK10,k2_pre_topc(sK9,sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6286])).

cnf(c_16978,plain,
    ( k1_tops_1(sK9,sK4(sK12,sK9,sK10)) = sK4(sK12,sK9,sK10)
    | r2_hidden(sK10,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16595,c_7038])).

cnf(c_37,negated_conjecture,
    ( r2_hidden(sK10,k10_yellow_6(sK9,sK11)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_7392,plain,
    ( sP0(sK12,sK9,k2_pre_topc(sK9,sK12))
    | ~ m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_6265])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_6282,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(subtyping,[status(esa)],[c_42])).

cnf(c_7041,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6282])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_6288,plain,
    ( ~ m1_subset_1(X0_62,X1_62)
    | r2_hidden(X0_62,X1_62)
    | v1_xboole_0(X1_62) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_7036,plain,
    ( m1_subset_1(X0_62,X1_62) != iProver_top
    | r2_hidden(X0_62,X1_62) = iProver_top
    | v1_xboole_0(X1_62) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6288])).

cnf(c_7618,plain,
    ( r2_hidden(sK10,u1_struct_0(sK9)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7041,c_7036])).

cnf(c_7633,plain,
    ( r2_hidden(sK10,u1_struct_0(sK9))
    | v1_xboole_0(u1_struct_0(sK9)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7618])).

cnf(c_38,negated_conjecture,
    ( l1_waybel_0(sK11,sK9) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_23,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_39,negated_conjecture,
    ( v7_waybel_0(sK11) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1180,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ l1_pre_topc(X1)
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_39])).

cnf(c_1181,plain,
    ( ~ l1_waybel_0(sK11,X0)
    | m1_subset_1(k10_yellow_6(X0,sK11),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK11)
    | ~ v4_orders_2(sK11)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_1180])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_40,negated_conjecture,
    ( v4_orders_2(sK11) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1185,plain,
    ( ~ l1_waybel_0(sK11,X0)
    | m1_subset_1(k10_yellow_6(X0,sK11),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1181,c_41,c_40])).

cnf(c_1971,plain,
    ( m1_subset_1(k10_yellow_6(X0,sK11),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK11 != sK11
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_1185])).

cnf(c_1972,plain,
    ( m1_subset_1(k10_yellow_6(sK9,sK11),k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_1971])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1183,plain,
    ( ~ l1_waybel_0(sK11,sK9)
    | m1_subset_1(k10_yellow_6(sK9,sK11),k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK11)
    | v2_struct_0(sK9)
    | ~ v4_orders_2(sK11)
    | ~ l1_pre_topc(sK9) ),
    inference(instantiation,[status(thm)],[c_1181])).

cnf(c_1974,plain,
    ( m1_subset_1(k10_yellow_6(sK9,sK11),k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1972,c_45,c_44,c_43,c_41,c_40,c_38,c_1183])).

cnf(c_6272,plain,
    ( m1_subset_1(k10_yellow_6(sK9,sK11),k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(subtyping,[status(esa)],[c_1974])).

cnf(c_7051,plain,
    ( m1_subset_1(k10_yellow_6(sK9,sK11),k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6272])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_6287,plain,
    ( ~ m1_subset_1(X0_62,k1_zfmisc_1(X1_62))
    | ~ r2_hidden(X2_62,X0_62)
    | ~ v1_xboole_0(X1_62) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_7037,plain,
    ( m1_subset_1(X0_62,k1_zfmisc_1(X1_62)) != iProver_top
    | r2_hidden(X2_62,X0_62) != iProver_top
    | v1_xboole_0(X1_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6287])).

cnf(c_7640,plain,
    ( r2_hidden(X0_62,k10_yellow_6(sK9,sK11)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7051,c_7037])).

cnf(c_7652,plain,
    ( ~ r2_hidden(X0_62,k10_yellow_6(sK9,sK11))
    | ~ v1_xboole_0(u1_struct_0(sK9)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7640])).

cnf(c_7654,plain,
    ( ~ r2_hidden(sK10,k10_yellow_6(sK9,sK11))
    | ~ v1_xboole_0(u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_7652])).

cnf(c_7862,plain,
    ( ~ sP0(X0_62,X0_63,k2_pre_topc(sK9,sK12))
    | v3_pre_topc(sK4(X0_62,X0_63,sK10),X0_63)
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12))
    | ~ r2_hidden(sK10,u1_struct_0(X0_63)) ),
    inference(instantiation,[status(thm)],[c_6291])).

cnf(c_8424,plain,
    ( ~ sP0(sK12,sK9,k2_pre_topc(sK9,sK12))
    | v3_pre_topc(sK4(sK12,sK9,sK10),sK9)
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12))
    | ~ r2_hidden(sK10,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_7862])).

cnf(c_6523,plain,
    ( k1_tops_1(sK9,X0_62) = X0_62
    | ~ v3_pre_topc(X0_62,sK9)
    | ~ m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6303,c_6300,c_6304])).

cnf(c_6524,plain,
    ( ~ m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v3_pre_topc(X0_62,sK9)
    | k1_tops_1(sK9,X0_62) = X0_62 ),
    inference(renaming,[status(thm)],[c_6523])).

cnf(c_9955,plain,
    ( ~ m1_subset_1(sK4(sK12,sK9,sK10),k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v3_pre_topc(sK4(sK12,sK9,sK10),sK9)
    | k1_tops_1(sK9,sK4(sK12,sK9,sK10)) = sK4(sK12,sK9,sK10) ),
    inference(instantiation,[status(thm)],[c_6524])).

cnf(c_8564,plain,
    ( ~ sP0(X0_62,X0_63,k2_pre_topc(sK9,sK12))
    | m1_subset_1(sK4(X0_62,X0_63,sK10),k1_zfmisc_1(u1_struct_0(X0_63)))
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12))
    | ~ r2_hidden(sK10,u1_struct_0(X0_63)) ),
    inference(instantiation,[status(thm)],[c_6290])).

cnf(c_9725,plain,
    ( ~ sP0(X0_62,sK9,k2_pre_topc(sK9,sK12))
    | m1_subset_1(sK4(X0_62,sK9,sK10),k1_zfmisc_1(u1_struct_0(sK9)))
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12))
    | ~ r2_hidden(sK10,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_8564])).

cnf(c_12943,plain,
    ( ~ sP0(sK12,sK9,k2_pre_topc(sK9,sK12))
    | m1_subset_1(sK4(sK12,sK9,sK10),k1_zfmisc_1(u1_struct_0(sK9)))
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12))
    | ~ r2_hidden(sK10,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_9725])).

cnf(c_17554,plain,
    ( k1_tops_1(sK9,sK4(sK12,sK9,sK10)) = sK4(sK12,sK9,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16978,c_37,c_36,c_34,c_7392,c_7633,c_7654,c_8424,c_9955,c_12943])).

cnf(c_21,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2133,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_44])).

cnf(c_2134,plain,
    ( m1_connsp_2(X0,sK9,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r2_hidden(X1,k1_tops_1(sK9,X0))
    | v2_struct_0(sK9)
    | ~ l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_2133])).

cnf(c_2138,plain,
    ( m1_connsp_2(X0,sK9,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r2_hidden(X1,k1_tops_1(sK9,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2134,c_45,c_43])).

cnf(c_6268,plain,
    ( m1_connsp_2(X0_62,sK9,X1_62)
    | ~ m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X1_62,u1_struct_0(sK9))
    | ~ r2_hidden(X1_62,k1_tops_1(sK9,X0_62)) ),
    inference(subtyping,[status(esa)],[c_2138])).

cnf(c_7055,plain,
    ( m1_connsp_2(X0_62,sK9,X1_62) = iProver_top
    | m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | m1_subset_1(X1_62,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X1_62,k1_tops_1(sK9,X0_62)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6268])).

cnf(c_13487,plain,
    ( m1_connsp_2(sK4(X0_62,sK9,X1_62),sK9,X2_62) = iProver_top
    | m1_subset_1(X0_62,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X2_62,k1_tops_1(sK9,sK4(X0_62,sK9,X1_62))) != iProver_top
    | r2_hidden(X1_62,k2_pre_topc(sK9,X0_62)) = iProver_top
    | r2_hidden(X1_62,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9274,c_7055])).

cnf(c_19897,plain,
    ( m1_connsp_2(sK4(sK12,sK9,sK10),sK9,X0_62) = iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | r2_hidden(X0_62,sK4(sK12,sK9,sK10)) != iProver_top
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12)) = iProver_top
    | r2_hidden(sK10,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17554,c_13487])).

cnf(c_54,plain,
    ( r2_hidden(sK10,k10_yellow_6(sK9,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_55,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_56,plain,
    ( r2_hidden(sK10,k2_pre_topc(sK9,sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_7653,plain,
    ( r2_hidden(sK10,k10_yellow_6(sK9,sK11)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7640])).

cnf(c_19970,plain,
    ( m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | m1_connsp_2(sK4(sK12,sK9,sK10),sK9,X0_62) = iProver_top
    | r2_hidden(X0_62,sK4(sK12,sK9,sK10)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19897,c_54,c_55,c_56,c_7618,c_7653])).

cnf(c_19971,plain,
    ( m1_connsp_2(sK4(sK12,sK9,sK10),sK9,X0_62) = iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X0_62,sK4(sK12,sK9,sK10)) != iProver_top ),
    inference(renaming,[status(thm)],[c_19970])).

cnf(c_6283,negated_conjecture,
    ( r2_hidden(sK10,k10_yellow_6(sK9,sK11)) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_7040,plain,
    ( r2_hidden(sK10,k10_yellow_6(sK9,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6283])).

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
    inference(cnf_transformation,[],[f118])).

cnf(c_1447,plain,
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
    | sK11 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_39])).

cnf(c_1448,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK11,X0)
    | ~ l1_waybel_0(sK11,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k10_yellow_6(X1,sK11),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK11))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(sK11)
    | ~ v4_orders_2(sK11)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_1447])).

cnf(c_1452,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK11,X0)
    | ~ l1_waybel_0(sK11,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k10_yellow_6(X1,sK11),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK11))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1448,c_41,c_40])).

cnf(c_1467,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK11,X0)
    | ~ l1_waybel_0(sK11,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK11))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1452,c_1185])).

cnf(c_1788,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK11,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK11))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK11 != sK11
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_1467])).

cnf(c_1789,plain,
    ( ~ m1_connsp_2(X0,sK9,X1)
    | r1_waybel_0(sK9,sK11,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r2_hidden(X1,k10_yellow_6(sK9,sK11))
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_1788])).

cnf(c_1793,plain,
    ( ~ r2_hidden(X1,k10_yellow_6(sK9,sK11))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | r1_waybel_0(sK9,sK11,X0)
    | ~ m1_connsp_2(X0,sK9,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1789,c_45,c_44,c_43])).

cnf(c_1794,plain,
    ( ~ m1_connsp_2(X0,sK9,X1)
    | r1_waybel_0(sK9,sK11,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r2_hidden(X1,k10_yellow_6(sK9,sK11)) ),
    inference(renaming,[status(thm)],[c_1793])).

cnf(c_6280,plain,
    ( ~ m1_connsp_2(X0_62,sK9,X1_62)
    | r1_waybel_0(sK9,sK11,X0_62)
    | ~ m1_subset_1(X1_62,u1_struct_0(sK9))
    | ~ r2_hidden(X1_62,k10_yellow_6(sK9,sK11)) ),
    inference(subtyping,[status(esa)],[c_1794])).

cnf(c_7043,plain,
    ( m1_connsp_2(X0_62,sK9,X1_62) != iProver_top
    | r1_waybel_0(sK9,sK11,X0_62) = iProver_top
    | m1_subset_1(X1_62,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X1_62,k10_yellow_6(sK9,sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6280])).

cnf(c_9050,plain,
    ( m1_connsp_2(X0_62,sK9,sK10) != iProver_top
    | r1_waybel_0(sK9,sK11,X0_62) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7040,c_7043])).

cnf(c_49,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_9055,plain,
    ( r1_waybel_0(sK9,sK11,X0_62) = iProver_top
    | m1_connsp_2(X0_62,sK9,sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9050,c_49])).

cnf(c_9056,plain,
    ( m1_connsp_2(X0_62,sK9,sK10) != iProver_top
    | r1_waybel_0(sK9,sK11,X0_62) = iProver_top ),
    inference(renaming,[status(thm)],[c_9055])).

cnf(c_19984,plain,
    ( r1_waybel_0(sK9,sK11,sK4(sK12,sK9,sK10)) = iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(sK10,sK4(sK12,sK9,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19971,c_9056])).

cnf(c_7393,plain,
    ( sP0(sK12,sK9,k2_pre_topc(sK9,sK12)) = iProver_top
    | m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7392])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X3,X2)
    | r2_hidden(X3,sK4(X0,X1,X3))
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_6292,plain,
    ( ~ sP0(X0_62,X0_63,X1_62)
    | r2_hidden(X2_62,X1_62)
    | r2_hidden(X2_62,sK4(X0_62,X0_63,X2_62))
    | ~ r2_hidden(X2_62,u1_struct_0(X0_63)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_8137,plain,
    ( ~ sP0(X0_62,X0_63,k2_pre_topc(sK9,sK12))
    | r2_hidden(sK10,sK4(X0_62,X0_63,sK10))
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12))
    | ~ r2_hidden(sK10,u1_struct_0(X0_63)) ),
    inference(instantiation,[status(thm)],[c_6292])).

cnf(c_8414,plain,
    ( ~ sP0(sK12,sK9,k2_pre_topc(sK9,sK12))
    | r2_hidden(sK10,sK4(sK12,sK9,sK10))
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12))
    | ~ r2_hidden(sK10,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_8137])).

cnf(c_8415,plain,
    ( sP0(sK12,sK9,k2_pre_topc(sK9,sK12)) != iProver_top
    | r2_hidden(sK10,sK4(sK12,sK9,sK10)) = iProver_top
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12)) = iProver_top
    | r2_hidden(sK10,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8414])).

cnf(c_20167,plain,
    ( r1_waybel_0(sK9,sK11,sK4(sK12,sK9,sK10)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19984,c_49,c_54,c_55,c_56,c_7393,c_7618,c_7653,c_8415])).

cnf(c_25,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_28,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_594,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_25,c_28])).

cnf(c_1240,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(X0)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_594,c_39])).

cnf(c_1241,plain,
    ( ~ r1_waybel_0(X0,sK11,X1)
    | ~ r1_waybel_0(X0,sK11,X2)
    | ~ l1_waybel_0(sK11,X0)
    | ~ r1_xboole_0(X1,X2)
    | v2_struct_0(X0)
    | v2_struct_0(sK11)
    | ~ v4_orders_2(sK11)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_1240])).

cnf(c_1245,plain,
    ( ~ r1_waybel_0(X0,sK11,X1)
    | ~ r1_waybel_0(X0,sK11,X2)
    | ~ l1_waybel_0(sK11,X0)
    | ~ r1_xboole_0(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1241,c_41,c_40])).

cnf(c_1246,plain,
    ( ~ r1_waybel_0(X0,sK11,X1)
    | ~ r1_waybel_0(X0,sK11,X2)
    | ~ l1_waybel_0(sK11,X0)
    | ~ r1_xboole_0(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_1245])).

cnf(c_1929,plain,
    ( ~ r1_waybel_0(X0,sK11,X1)
    | ~ r1_waybel_0(X0,sK11,X2)
    | ~ r1_xboole_0(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK11 != sK11
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_1246])).

cnf(c_1930,plain,
    ( ~ r1_waybel_0(sK9,sK11,X0)
    | ~ r1_waybel_0(sK9,sK11,X1)
    | ~ r1_xboole_0(X1,X0)
    | v2_struct_0(sK9)
    | ~ l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_1929])).

cnf(c_1934,plain,
    ( ~ r1_waybel_0(sK9,sK11,X0)
    | ~ r1_waybel_0(sK9,sK11,X1)
    | ~ r1_xboole_0(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1930,c_45,c_43])).

cnf(c_6274,plain,
    ( ~ r1_waybel_0(sK9,sK11,X0_62)
    | ~ r1_waybel_0(sK9,sK11,X1_62)
    | ~ r1_xboole_0(X1_62,X0_62) ),
    inference(subtyping,[status(esa)],[c_1934])).

cnf(c_7049,plain,
    ( r1_waybel_0(sK9,sK11,X0_62) != iProver_top
    | r1_waybel_0(sK9,sK11,X1_62) != iProver_top
    | r1_xboole_0(X1_62,X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6274])).

cnf(c_20173,plain,
    ( r1_waybel_0(sK9,sK11,X0_62) != iProver_top
    | r1_xboole_0(X0_62,sK4(sK12,sK9,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20167,c_7049])).

cnf(c_20540,plain,
    ( r1_waybel_0(sK9,sK11,sK12) != iProver_top
    | m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12)) = iProver_top
    | r2_hidden(sK10,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8441,c_20173])).

cnf(c_33,plain,
    ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_574,plain,
    ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_25,c_33])).

cnf(c_1777,plain,
    ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK11 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_574,c_38])).

cnf(c_1778,plain,
    ( r1_waybel_0(sK9,sK11,k2_relset_1(u1_struct_0(sK11),u1_struct_0(sK9),u1_waybel_0(sK9,sK11)))
    | v2_struct_0(sK11)
    | v2_struct_0(sK9)
    | ~ l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_1777])).

cnf(c_1780,plain,
    ( r1_waybel_0(sK9,sK11,k2_relset_1(u1_struct_0(sK11),u1_struct_0(sK9),u1_waybel_0(sK9,sK11))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1778,c_45,c_43,c_41])).

cnf(c_6281,plain,
    ( r1_waybel_0(sK9,sK11,k2_relset_1(u1_struct_0(sK11),u1_struct_0(sK9),u1_waybel_0(sK9,sK11))) ),
    inference(subtyping,[status(esa)],[c_1780])).

cnf(c_7042,plain,
    ( r1_waybel_0(sK9,sK11,k2_relset_1(u1_struct_0(sK11),u1_struct_0(sK9),u1_waybel_0(sK9,sK11))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6281])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK11),u1_struct_0(sK9),u1_waybel_0(sK9,sK11)) = sK12 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_6285,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK11),u1_struct_0(sK9),u1_waybel_0(sK9,sK11)) = sK12 ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_7085,plain,
    ( r1_waybel_0(sK9,sK11,sK12) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7042,c_6285])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20540,c_7653,c_7618,c_7085,c_56,c_55,c_54])).


%------------------------------------------------------------------------------
