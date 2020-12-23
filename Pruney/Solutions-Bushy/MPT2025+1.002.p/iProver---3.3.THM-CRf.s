%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2025+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:02 EST 2020

% Result     : Theorem 43.53s
% Output     : CNFRefutation 43.53s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 728 expanded)
%              Number of clauses        :  106 ( 158 expanded)
%              Number of leaves         :   26 ( 269 expanded)
%              Depth                    :   20
%              Number of atoms          : 1169 (7459 expanded)
%              Number of equality atoms :   91 ( 710 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

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
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
          & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(X1,k2_pre_topc(X0,sK12))
        & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = sK12
        & m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
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

fof(f73,plain,(
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

fof(f72,plain,
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

fof(f76,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12])],[f49,f75,f74,f73,f72])).

fof(f122,plain,(
    l1_waybel_0(sK11,sK9) ),
    inference(cnf_transformation,[],[f76])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f103,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f107,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f121,plain,(
    v7_waybel_0(sK11) ),
    inference(cnf_transformation,[],[f76])).

fof(f119,plain,(
    ~ v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f76])).

fof(f120,plain,(
    v4_orders_2(sK11) ),
    inference(cnf_transformation,[],[f76])).

fof(f115,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f76])).

fof(f117,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f76])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f67,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK7(X0,X1,X6))
        & m1_connsp_2(sK7(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK6(X0,X1,X2))
        & m1_connsp_2(sK6(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
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

fof(f68,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f64,f67,f66,f65])).

fof(f91,plain,(
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
    inference(cnf_transformation,[],[f68])).

fof(f130,plain,(
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
    inference(equality_resolution,[],[f91])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f116,plain,(
    v2_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f76])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f69,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f50,plain,(
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

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f50])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f60,plain,(
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

fof(f59,plain,(
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

fof(f58,plain,(
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

fof(f61,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f57,f60,f59,f58])).

fof(f82,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r2_hidden(X6,sK4(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f118,plain,(
    m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f76])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | v3_pre_topc(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f83,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | r1_xboole_0(X0,sK4(X0,X1,X6))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f80,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_subset_1(sK4(X0,X1,X6),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ( k2_pre_topc(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f51,f50])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ( ( k2_pre_topc(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k2_pre_topc(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_pre_topc(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k2_pre_topc(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f53])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k2_pre_topc(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f127,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k2_pre_topc(X1,X2))
      | ~ sP1(k2_pre_topc(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f77])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f125,plain,(
    k2_relset_1(u1_struct_0(sK11),u1_struct_0(sK9),u1_waybel_0(sK9,sK11)) = sK12 ),
    inference(cnf_transformation,[],[f76])).

fof(f126,plain,(
    ~ r2_hidden(sK10,k2_pre_topc(sK9,sK12)) ),
    inference(cnf_transformation,[],[f76])).

fof(f124,plain,(
    m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(cnf_transformation,[],[f76])).

fof(f123,plain,(
    r2_hidden(sK10,k10_yellow_6(sK9,sK11)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_42,negated_conjecture,
    ( l1_waybel_0(sK11,sK9) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_26,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_30,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_648,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_26,c_30])).

cnf(c_43,negated_conjecture,
    ( v7_waybel_0(sK11) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1294,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(X0)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_648,c_43])).

cnf(c_1295,plain,
    ( ~ r1_waybel_0(X0,sK11,X1)
    | ~ r1_waybel_0(X0,sK11,X2)
    | ~ l1_waybel_0(sK11,X0)
    | ~ r1_xboole_0(X1,X2)
    | v2_struct_0(X0)
    | v2_struct_0(sK11)
    | ~ v4_orders_2(sK11)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_1294])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_44,negated_conjecture,
    ( v4_orders_2(sK11) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1299,plain,
    ( ~ r1_waybel_0(X0,sK11,X1)
    | ~ r1_waybel_0(X0,sK11,X2)
    | ~ l1_waybel_0(sK11,X0)
    | ~ r1_xboole_0(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1295,c_45,c_44])).

cnf(c_1300,plain,
    ( ~ r1_waybel_0(X0,sK11,X1)
    | ~ r1_waybel_0(X0,sK11,X2)
    | ~ l1_waybel_0(sK11,X0)
    | ~ r1_xboole_0(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_1299])).

cnf(c_1983,plain,
    ( ~ r1_waybel_0(X0,sK11,X1)
    | ~ r1_waybel_0(X0,sK11,X2)
    | ~ r1_xboole_0(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK11 != sK11
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_1300])).

cnf(c_1984,plain,
    ( ~ r1_waybel_0(sK9,sK11,X0)
    | ~ r1_waybel_0(sK9,sK11,X1)
    | ~ r1_xboole_0(X1,X0)
    | v2_struct_0(sK9)
    | ~ l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_1983])).

cnf(c_49,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_47,negated_conjecture,
    ( l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1988,plain,
    ( ~ r1_waybel_0(sK9,sK11,X0)
    | ~ r1_waybel_0(sK9,sK11,X1)
    | ~ r1_xboole_0(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1984,c_49,c_47])).

cnf(c_102301,plain,
    ( ~ r1_waybel_0(sK9,sK11,X0)
    | ~ r1_waybel_0(sK9,sK11,sK4(X0,X1,sK10))
    | ~ r1_xboole_0(X0,sK4(X0,X1,sK10)) ),
    inference(instantiation,[status(thm)],[c_1988])).

cnf(c_125836,plain,
    ( ~ r1_waybel_0(sK9,sK11,sK4(sK12,sK9,sK10))
    | ~ r1_waybel_0(sK9,sK11,sK12)
    | ~ r1_xboole_0(sK12,sK4(sK12,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_102301])).

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
    inference(cnf_transformation,[],[f130])).

cnf(c_1501,plain,
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
    inference(resolution_lifted,[status(thm)],[c_20,c_43])).

cnf(c_1502,plain,
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
    inference(unflattening,[status(thm)],[c_1501])).

cnf(c_1506,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK11,X0)
    | ~ l1_waybel_0(sK11,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k10_yellow_6(X1,sK11),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK11))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1502,c_45,c_44])).

cnf(c_23,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1234,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ l1_pre_topc(X1)
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_43])).

cnf(c_1235,plain,
    ( ~ l1_waybel_0(sK11,X0)
    | m1_subset_1(k10_yellow_6(X0,sK11),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK11)
    | ~ v4_orders_2(sK11)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_1234])).

cnf(c_1239,plain,
    ( ~ l1_waybel_0(sK11,X0)
    | m1_subset_1(k10_yellow_6(X0,sK11),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1235,c_45,c_44])).

cnf(c_1521,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK11,X0)
    | ~ l1_waybel_0(sK11,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK11))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1506,c_1239])).

cnf(c_1842,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_waybel_0(X1,sK11,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k10_yellow_6(X1,sK11))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK11 != sK11
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_1521])).

cnf(c_1843,plain,
    ( ~ m1_connsp_2(X0,sK9,X1)
    | r1_waybel_0(sK9,sK11,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r2_hidden(X1,k10_yellow_6(sK9,sK11))
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | ~ l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_1842])).

cnf(c_48,negated_conjecture,
    ( v2_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1847,plain,
    ( ~ r2_hidden(X1,k10_yellow_6(sK9,sK11))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | r1_waybel_0(sK9,sK11,X0)
    | ~ m1_connsp_2(X0,sK9,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1843,c_49,c_48,c_47])).

cnf(c_1848,plain,
    ( ~ m1_connsp_2(X0,sK9,X1)
    | r1_waybel_0(sK9,sK11,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r2_hidden(X1,k10_yellow_6(sK9,sK11)) ),
    inference(renaming,[status(thm)],[c_1847])).

cnf(c_73718,plain,
    ( ~ m1_connsp_2(X0,sK9,sK10)
    | r1_waybel_0(sK9,sK11,X0)
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ r2_hidden(sK10,k10_yellow_6(sK9,sK11)) ),
    inference(instantiation,[status(thm)],[c_1848])).

cnf(c_95185,plain,
    ( ~ m1_connsp_2(sK4(sK12,sK9,sK10),sK9,sK10)
    | r1_waybel_0(sK9,sK11,sK4(sK12,sK9,sK10))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ r2_hidden(sK10,k10_yellow_6(sK9,sK11)) ),
    inference(instantiation,[status(thm)],[c_73718])).

cnf(c_21,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2149,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_49])).

cnf(c_2150,plain,
    ( m1_connsp_2(X0,sK9,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r2_hidden(X1,k1_tops_1(sK9,X0))
    | ~ v2_pre_topc(sK9)
    | ~ l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_2149])).

cnf(c_2154,plain,
    ( m1_connsp_2(X0,sK9,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r2_hidden(X1,k1_tops_1(sK9,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2150,c_48,c_47])).

cnf(c_73894,plain,
    ( m1_connsp_2(X0,sK9,sK10)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ r2_hidden(sK10,k1_tops_1(sK9,X0)) ),
    inference(instantiation,[status(thm)],[c_2154])).

cnf(c_84398,plain,
    ( m1_connsp_2(sK4(sK12,sK9,sK10),sK9,sK10)
    | ~ m1_subset_1(sK4(sK12,sK9,sK10),k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ r2_hidden(sK10,k1_tops_1(sK9,sK4(sK12,sK9,sK10))) ),
    inference(instantiation,[status(thm)],[c_73894])).

cnf(c_6731,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_73978,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK10,X2)
    | X2 != X1
    | sK10 != X0 ),
    inference(instantiation,[status(thm)],[c_6731])).

cnf(c_74706,plain,
    ( ~ r2_hidden(sK10,X0)
    | r2_hidden(sK10,X1)
    | X1 != X0
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_73978])).

cnf(c_76705,plain,
    ( ~ r2_hidden(sK10,X0)
    | r2_hidden(sK10,k1_tops_1(sK9,X1))
    | k1_tops_1(sK9,X1) != X0
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_74706])).

cnf(c_77876,plain,
    ( ~ r2_hidden(sK10,sK4(sK12,sK9,sK10))
    | r2_hidden(sK10,k1_tops_1(sK9,sK4(sK12,sK9,sK10)))
    | k1_tops_1(sK9,sK4(sK12,sK9,sK10)) != sK4(sK12,sK9,sK10)
    | sK10 != sK10 ),
    inference(instantiation,[status(thm)],[c_76705])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X3,X2)
    | r2_hidden(X3,sK4(X0,X1,X3))
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_7586,plain,
    ( ~ sP0(X0,X1,k2_pre_topc(sK9,sK12))
    | r2_hidden(sK10,sK4(X0,X1,sK10))
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12))
    | ~ r2_hidden(sK10,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_55993,plain,
    ( ~ sP0(sK12,sK9,k2_pre_topc(sK9,sK12))
    | r2_hidden(sK10,sK4(sK12,sK9,sK10))
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12))
    | ~ r2_hidden(sK10,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_7586])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X3,X2) = X2 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2197,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X3,X2) = X2
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_48])).

cnf(c_2198,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK9)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_2197])).

cnf(c_2202,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2198,c_47])).

cnf(c_2203,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_2202])).

cnf(c_2337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2203,c_47])).

cnf(c_2338,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v3_pre_topc(X1,sK9)
    | k1_tops_1(sK9,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_2337])).

cnf(c_6720,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v3_pre_topc(X0,sK9)
    | k1_tops_1(sK9,X0) = X0
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_2338])).

cnf(c_6722,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2338])).

cnf(c_6721,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_2338])).

cnf(c_6882,plain,
    ( k1_tops_1(sK9,X0) = X0
    | ~ v3_pre_topc(X0,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6720,c_6722,c_6721])).

cnf(c_6883,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v3_pre_topc(X0,sK9)
    | k1_tops_1(sK9,X0) = X0 ),
    inference(renaming,[status(thm)],[c_6882])).

cnf(c_13480,plain,
    ( ~ m1_subset_1(sK4(X0,sK9,sK10),k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v3_pre_topc(sK4(X0,sK9,sK10),sK9)
    | k1_tops_1(sK9,sK4(X0,sK9,sK10)) = sK4(X0,sK9,sK10) ),
    inference(instantiation,[status(thm)],[c_6883])).

cnf(c_26985,plain,
    ( ~ m1_subset_1(sK4(sK12,sK9,sK10),k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v3_pre_topc(sK4(sK12,sK9,sK10),sK9)
    | k1_tops_1(sK9,sK4(sK12,sK9,sK10)) = sK4(sK12,sK9,sK10) ),
    inference(instantiation,[status(thm)],[c_13480])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_7632,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK9,sK11),k1_zfmisc_1(X0))
    | ~ r2_hidden(sK10,k10_yellow_6(sK9,sK11))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_11657,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK9,sK11),k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ r2_hidden(sK10,k10_yellow_6(sK9,sK11))
    | ~ v1_xboole_0(u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_7632])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_7492,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_7499,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_9199,plain,
    ( r2_hidden(sK10,u1_struct_0(sK9)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7492,c_7499])).

cnf(c_9208,plain,
    ( r2_hidden(sK10,u1_struct_0(sK9))
    | v1_xboole_0(u1_struct_0(sK9)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9199])).

cnf(c_6726,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_8286,plain,
    ( sK10 = sK10 ),
    inference(instantiation,[status(thm)],[c_6726])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2)
    | v3_pre_topc(sK4(X0,X1,X3),X1)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_7587,plain,
    ( ~ sP0(X0,X1,k2_pre_topc(sK9,sK12))
    | v3_pre_topc(sK4(X0,X1,sK10),X1)
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12))
    | ~ r2_hidden(sK10,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8197,plain,
    ( ~ sP0(sK12,sK9,k2_pre_topc(sK9,sK12))
    | v3_pre_topc(sK4(sK12,sK9,sK10),sK9)
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12))
    | ~ r2_hidden(sK10,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_7587])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | r1_xboole_0(X0,sK4(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_7585,plain,
    ( ~ sP0(X0,X1,k2_pre_topc(sK9,sK12))
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12))
    | ~ r2_hidden(sK10,u1_struct_0(X1))
    | r1_xboole_0(X0,sK4(X0,X1,sK10)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_8187,plain,
    ( ~ sP0(sK12,sK9,k2_pre_topc(sK9,sK12))
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12))
    | ~ r2_hidden(sK10,u1_struct_0(sK9))
    | r1_xboole_0(sK12,sK4(sK12,sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_7585])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2)
    | m1_subset_1(sK4(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_7584,plain,
    ( ~ sP0(X0,X1,k2_pre_topc(sK9,sK12))
    | m1_subset_1(sK4(X0,X1,sK10),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12))
    | ~ r2_hidden(sK10,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8149,plain,
    ( ~ sP0(sK12,sK9,k2_pre_topc(sK9,sK12))
    | m1_subset_1(sK4(sK12,sK9,sK10),k1_zfmisc_1(u1_struct_0(sK9)))
    | r2_hidden(sK10,k2_pre_topc(sK9,sK12))
    | ~ r2_hidden(sK10,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_7584])).

cnf(c_13,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1,plain,
    ( ~ sP1(k2_pre_topc(X0,X1),X0,X1)
    | sP0(X1,X0,k2_pre_topc(X0,X1)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_597,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3)
    | X1 != X3
    | X0 != X4
    | k2_pre_topc(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_1])).

cnf(c_598,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_598,c_25])).

cnf(c_603,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_602])).

cnf(c_2355,plain,
    ( sP0(X0,X1,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_603,c_47])).

cnf(c_2356,plain,
    ( sP0(X0,sK9,k2_pre_topc(sK9,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(unflattening,[status(thm)],[c_2355])).

cnf(c_7797,plain,
    ( sP0(sK12,sK9,k2_pre_topc(sK9,sK12))
    | ~ m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_2356])).

cnf(c_37,plain,
    ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_628,plain,
    ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_26,c_37])).

cnf(c_1831,plain,
    ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK11 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_628,c_42])).

cnf(c_1832,plain,
    ( r1_waybel_0(sK9,sK11,k2_relset_1(u1_struct_0(sK11),u1_struct_0(sK9),u1_waybel_0(sK9,sK11)))
    | v2_struct_0(sK11)
    | v2_struct_0(sK9)
    | ~ l1_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_1831])).

cnf(c_1834,plain,
    ( r1_waybel_0(sK9,sK11,k2_relset_1(u1_struct_0(sK11),u1_struct_0(sK9),u1_waybel_0(sK9,sK11))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1832,c_49,c_47,c_45])).

cnf(c_7491,plain,
    ( r1_waybel_0(sK9,sK11,k2_relset_1(u1_struct_0(sK11),u1_struct_0(sK9),u1_waybel_0(sK9,sK11))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1834])).

cnf(c_39,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK11),u1_struct_0(sK9),u1_waybel_0(sK9,sK11)) = sK12 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_7513,plain,
    ( r1_waybel_0(sK9,sK11,sK12) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7491,c_39])).

cnf(c_7546,plain,
    ( r1_waybel_0(sK9,sK11,sK12) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7513])).

cnf(c_1237,plain,
    ( ~ l1_waybel_0(sK11,sK9)
    | m1_subset_1(k10_yellow_6(sK9,sK11),k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK11)
    | v2_struct_0(sK9)
    | ~ v4_orders_2(sK11)
    | ~ l1_pre_topc(sK9) ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_38,negated_conjecture,
    ( ~ r2_hidden(sK10,k2_pre_topc(sK9,sK12)) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_41,negated_conjecture,
    ( r2_hidden(sK10,k10_yellow_6(sK9,sK11)) ),
    inference(cnf_transformation,[],[f123])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_125836,c_95185,c_84398,c_77876,c_55993,c_26985,c_11657,c_9208,c_8286,c_8197,c_8187,c_8149,c_7797,c_7546,c_1237,c_38,c_40,c_41,c_42,c_44,c_45,c_46,c_47,c_48,c_49])).


%------------------------------------------------------------------------------
