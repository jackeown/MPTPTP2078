%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1952+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:55 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  188 (6943 expanded)
%              Number of clauses        :  106 (1136 expanded)
%              Number of leaves         :   16 (2149 expanded)
%              Depth                    :   32
%              Number of atoms          : 1068 (104152 expanded)
%              Number of equality atoms :  227 (2821 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( r1_waybel_0(X1,X5,X3)
                  | ~ r2_hidden(k4_tarski(X5,X4),X2)
                  | ~ l1_waybel_0(X5,X1)
                  | ~ v7_waybel_0(X5)
                  | ~ v4_orders_2(X5)
                  | v2_struct_0(X5) )
              | ~ r2_hidden(X4,X3)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & X0 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r1_waybel_0(X1,X5,X3)
                    & r2_hidden(k4_tarski(X5,X4),X2)
                    & l1_waybel_0(X5,X1)
                    & v7_waybel_0(X5)
                    & v4_orders_2(X5)
                    & ~ v2_struct_0(X5) )
                & r2_hidden(X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            | X0 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ? [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( r1_waybel_0(X1,X5,X3)
                    | ~ r2_hidden(k4_tarski(X5,X4),X2)
                    | ~ l1_waybel_0(X5,X1)
                    | ~ v7_waybel_0(X5)
                    | ~ v4_orders_2(X5)
                    | v2_struct_0(X5) )
                | ~ r2_hidden(X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r1_waybel_0(X0,X5,X3)
                    & r2_hidden(k4_tarski(X5,X4),X1)
                    & l1_waybel_0(X5,X0)
                    & v7_waybel_0(X5)
                    & v4_orders_2(X5)
                    & ~ v2_struct_0(X5) )
                & r2_hidden(X4,X3)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( r1_waybel_0(X0,X8,X6)
                    | ~ r2_hidden(k4_tarski(X8,X7),X1)
                    | ~ l1_waybel_0(X8,X0)
                    | ~ v7_waybel_0(X8)
                    | ~ v4_orders_2(X8)
                    | v2_struct_0(X8) )
                | ~ r2_hidden(X7,X6)
                | ~ m1_subset_1(X7,u1_struct_0(X0)) )
            & X2 = X6
            & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( r1_waybel_0(X0,X8,X6)
                  | ~ r2_hidden(k4_tarski(X8,X7),X1)
                  | ~ l1_waybel_0(X8,X0)
                  | ~ v7_waybel_0(X8)
                  | ~ v4_orders_2(X8)
                  | v2_struct_0(X8) )
              | ~ r2_hidden(X7,X6)
              | ~ m1_subset_1(X7,u1_struct_0(X0)) )
          & X2 = X6
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X7] :
            ( ! [X8] :
                ( r1_waybel_0(X0,X8,sK4(X0,X1,X2))
                | ~ r2_hidden(k4_tarski(X8,X7),X1)
                | ~ l1_waybel_0(X8,X0)
                | ~ v7_waybel_0(X8)
                | ~ v4_orders_2(X8)
                | v2_struct_0(X8) )
            | ~ r2_hidden(X7,sK4(X0,X1,X2))
            | ~ m1_subset_1(X7,u1_struct_0(X0)) )
        & sK4(X0,X1,X2) = X2
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X4,X3,X1,X0] :
      ( ? [X5] :
          ( ~ r1_waybel_0(X0,X5,X3)
          & r2_hidden(k4_tarski(X5,X4),X1)
          & l1_waybel_0(X5,X0)
          & v7_waybel_0(X5)
          & v4_orders_2(X5)
          & ~ v2_struct_0(X5) )
     => ( ~ r1_waybel_0(X0,sK3(X0,X1,X3),X3)
        & r2_hidden(k4_tarski(sK3(X0,X1,X3),X4),X1)
        & l1_waybel_0(sK3(X0,X1,X3),X0)
        & v7_waybel_0(sK3(X0,X1,X3))
        & v4_orders_2(sK3(X0,X1,X3))
        & ~ v2_struct_0(sK3(X0,X1,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r1_waybel_0(X0,X5,X3)
              & r2_hidden(k4_tarski(X5,X4),X1)
              & l1_waybel_0(X5,X0)
              & v7_waybel_0(X5)
              & v4_orders_2(X5)
              & ~ v2_struct_0(X5) )
          & r2_hidden(X4,X3)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ? [X5] :
            ( ~ r1_waybel_0(X0,X5,X3)
            & r2_hidden(k4_tarski(X5,sK2(X0,X1,X3)),X1)
            & l1_waybel_0(X5,X0)
            & v7_waybel_0(X5)
            & v4_orders_2(X5)
            & ~ v2_struct_0(X5) )
        & r2_hidden(sK2(X0,X1,X3),X3)
        & m1_subset_1(sK2(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ( ~ r1_waybel_0(X0,sK3(X0,X1,X3),X3)
              & r2_hidden(k4_tarski(sK3(X0,X1,X3),sK2(X0,X1,X3)),X1)
              & l1_waybel_0(sK3(X0,X1,X3),X0)
              & v7_waybel_0(sK3(X0,X1,X3))
              & v4_orders_2(sK3(X0,X1,X3))
              & ~ v2_struct_0(sK3(X0,X1,X3))
              & r2_hidden(sK2(X0,X1,X3),X3)
              & m1_subset_1(sK2(X0,X1,X3),u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ( ! [X7] :
              ( ! [X8] :
                  ( r1_waybel_0(X0,X8,sK4(X0,X1,X2))
                  | ~ r2_hidden(k4_tarski(X8,X7),X1)
                  | ~ l1_waybel_0(X8,X0)
                  | ~ v7_waybel_0(X8)
                  | ~ v4_orders_2(X8)
                  | v2_struct_0(X8) )
              | ~ r2_hidden(X7,sK4(X0,X1,X2))
              | ~ m1_subset_1(X7,u1_struct_0(X0)) )
          & sK4(X0,X1,X2) = X2
          & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f32,f31,f30])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | l1_waybel_0(sK3(X0,X1,X3),X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1,X3)
      | l1_waybel_0(sK3(X0,X1,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X3),sK2(X0,X1,X3)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1,X3)
      | r2_hidden(k4_tarski(sK3(X0,X1,X3),sK2(X0,X1,X3)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m4_yellow_6(X1,X0)
            & v8_yellow_6(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1))))
             => ( v3_pre_topc(X2,k13_yellow_6(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                     => ! [X4] :
                          ( ( l1_waybel_0(X4,X0)
                            & v7_waybel_0(X4)
                            & v4_orders_2(X4)
                            & ~ v2_struct_0(X4) )
                         => ( r2_hidden(k4_tarski(X4,X3),X1)
                           => r1_waybel_0(X0,X4,X2) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m4_yellow_6(X1,X0)
              & v8_yellow_6(X1,X0) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1))))
               => ( v3_pre_topc(X2,k13_yellow_6(X0,X1))
                <=> ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => ! [X4] :
                            ( ( l1_waybel_0(X4,X0)
                              & v7_waybel_0(X4)
                              & v4_orders_2(X4)
                              & ~ v2_struct_0(X4) )
                           => ( r2_hidden(k4_tarski(X4,X3),X1)
                             => r1_waybel_0(X0,X4,X2) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m4_yellow_6(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1))))
               => ( v3_pre_topc(X2,k13_yellow_6(X0,X1))
                <=> ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => ! [X4] :
                            ( ( l1_waybel_0(X4,X0)
                              & v7_waybel_0(X4)
                              & v4_orders_2(X4)
                              & ~ v2_struct_0(X4) )
                           => ( r2_hidden(k4_tarski(X4,X3),X1)
                             => r1_waybel_0(X0,X4,X2) ) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_pre_topc(X2,k13_yellow_6(X0,X1))
              <~> ! [X3] :
                    ( ! [X4] :
                        ( r1_waybel_0(X0,X4,X2)
                        | ~ r2_hidden(k4_tarski(X4,X3),X1)
                        | ~ l1_waybel_0(X4,X0)
                        | ~ v7_waybel_0(X4)
                        | ~ v4_orders_2(X4)
                        | v2_struct_0(X4) )
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
          & m4_yellow_6(X1,X0) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_pre_topc(X2,k13_yellow_6(X0,X1))
              <~> ! [X3] :
                    ( ! [X4] :
                        ( r1_waybel_0(X0,X4,X2)
                        | ~ r2_hidden(k4_tarski(X4,X3),X1)
                        | ~ l1_waybel_0(X4,X0)
                        | ~ v7_waybel_0(X4)
                        | ~ v4_orders_2(X4)
                        | v2_struct_0(X4) )
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
          & m4_yellow_6(X1,X0) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_waybel_0(X0,X4,X2)
                        & r2_hidden(k4_tarski(X4,X3),X1)
                        & l1_waybel_0(X4,X0)
                        & v7_waybel_0(X4)
                        & v4_orders_2(X4)
                        & ~ v2_struct_0(X4) )
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
              & ( ! [X3] :
                    ( ! [X4] :
                        ( r1_waybel_0(X0,X4,X2)
                        | ~ r2_hidden(k4_tarski(X4,X3),X1)
                        | ~ l1_waybel_0(X4,X0)
                        | ~ v7_waybel_0(X4)
                        | ~ v4_orders_2(X4)
                        | v2_struct_0(X4) )
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
          & m4_yellow_6(X1,X0) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_waybel_0(X0,X4,X2)
                        & r2_hidden(k4_tarski(X4,X3),X1)
                        & l1_waybel_0(X4,X0)
                        & v7_waybel_0(X4)
                        & v4_orders_2(X4)
                        & ~ v2_struct_0(X4) )
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
              & ( ! [X3] :
                    ( ! [X4] :
                        ( r1_waybel_0(X0,X4,X2)
                        | ~ r2_hidden(k4_tarski(X4,X3),X1)
                        | ~ l1_waybel_0(X4,X0)
                        | ~ v7_waybel_0(X4)
                        | ~ v4_orders_2(X4)
                        | v2_struct_0(X4) )
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
          & m4_yellow_6(X1,X0) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_waybel_0(X0,X4,X2)
                        & r2_hidden(k4_tarski(X4,X3),X1)
                        & l1_waybel_0(X4,X0)
                        & v7_waybel_0(X4)
                        & v4_orders_2(X4)
                        & ~ v2_struct_0(X4) )
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
              & ( ! [X5] :
                    ( ! [X6] :
                        ( r1_waybel_0(X0,X6,X2)
                        | ~ r2_hidden(k4_tarski(X6,X5),X1)
                        | ~ l1_waybel_0(X6,X0)
                        | ~ v7_waybel_0(X6)
                        | ~ v4_orders_2(X6)
                        | v2_struct_0(X6) )
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
          & m4_yellow_6(X1,X0) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f35])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X4,X2)
          & r2_hidden(k4_tarski(X4,X3),X1)
          & l1_waybel_0(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( ~ r1_waybel_0(X0,sK9,X2)
        & r2_hidden(k4_tarski(sK9,X3),X1)
        & l1_waybel_0(sK9,X0)
        & v7_waybel_0(sK9)
        & v4_orders_2(sK9)
        & ~ v2_struct_0(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r1_waybel_0(X0,X4,X2)
              & r2_hidden(k4_tarski(X4,X3),X1)
              & l1_waybel_0(X4,X0)
              & v7_waybel_0(X4)
              & v4_orders_2(X4)
              & ~ v2_struct_0(X4) )
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ~ r1_waybel_0(X0,X4,X2)
            & r2_hidden(k4_tarski(X4,sK8),X1)
            & l1_waybel_0(X4,X0)
            & v7_waybel_0(X4)
            & v4_orders_2(X4)
            & ~ v2_struct_0(X4) )
        & r2_hidden(sK8,X2)
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ? [X4] :
                    ( ~ r1_waybel_0(X0,X4,X2)
                    & r2_hidden(k4_tarski(X4,X3),X1)
                    & l1_waybel_0(X4,X0)
                    & v7_waybel_0(X4)
                    & v4_orders_2(X4)
                    & ~ v2_struct_0(X4) )
                & r2_hidden(X3,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
          & ( ! [X5] :
                ( ! [X6] :
                    ( r1_waybel_0(X0,X6,X2)
                    | ~ r2_hidden(k4_tarski(X6,X5),X1)
                    | ~ l1_waybel_0(X6,X0)
                    | ~ v7_waybel_0(X6)
                    | ~ v4_orders_2(X6)
                    | v2_struct_0(X6) )
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            | v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
     => ( ( ? [X3] :
              ( ? [X4] :
                  ( ~ r1_waybel_0(X0,X4,sK7)
                  & r2_hidden(k4_tarski(X4,X3),X1)
                  & l1_waybel_0(X4,X0)
                  & v7_waybel_0(X4)
                  & v4_orders_2(X4)
                  & ~ v2_struct_0(X4) )
              & r2_hidden(X3,sK7)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v3_pre_topc(sK7,k13_yellow_6(X0,X1)) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( r1_waybel_0(X0,X6,sK7)
                  | ~ r2_hidden(k4_tarski(X6,X5),X1)
                  | ~ l1_waybel_0(X6,X0)
                  | ~ v7_waybel_0(X6)
                  | ~ v4_orders_2(X6)
                  | v2_struct_0(X6) )
              | ~ r2_hidden(X5,sK7)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | v3_pre_topc(sK7,k13_yellow_6(X0,X1)) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_waybel_0(X0,X4,X2)
                        & r2_hidden(k4_tarski(X4,X3),X1)
                        & l1_waybel_0(X4,X0)
                        & v7_waybel_0(X4)
                        & v4_orders_2(X4)
                        & ~ v2_struct_0(X4) )
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
              & ( ! [X5] :
                    ( ! [X6] :
                        ( r1_waybel_0(X0,X6,X2)
                        | ~ r2_hidden(k4_tarski(X6,X5),X1)
                        | ~ l1_waybel_0(X6,X0)
                        | ~ v7_waybel_0(X6)
                        | ~ v4_orders_2(X6)
                        | v2_struct_0(X6) )
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
          & m4_yellow_6(X1,X0) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_waybel_0(X0,X4,X2)
                      & r2_hidden(k4_tarski(X4,X3),sK6)
                      & l1_waybel_0(X4,X0)
                      & v7_waybel_0(X4)
                      & v4_orders_2(X4)
                      & ~ v2_struct_0(X4) )
                  & r2_hidden(X3,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X2,k13_yellow_6(X0,sK6)) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( r1_waybel_0(X0,X6,X2)
                      | ~ r2_hidden(k4_tarski(X6,X5),sK6)
                      | ~ l1_waybel_0(X6,X0)
                      | ~ v7_waybel_0(X6)
                      | ~ v4_orders_2(X6)
                      | v2_struct_0(X6) )
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | v3_pre_topc(X2,k13_yellow_6(X0,sK6)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,sK6)))) )
        & m4_yellow_6(sK6,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ? [X4] :
                          ( ~ r1_waybel_0(X0,X4,X2)
                          & r2_hidden(k4_tarski(X4,X3),X1)
                          & l1_waybel_0(X4,X0)
                          & v7_waybel_0(X4)
                          & v4_orders_2(X4)
                          & ~ v2_struct_0(X4) )
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
                & ( ! [X5] :
                      ( ! [X6] :
                          ( r1_waybel_0(X0,X6,X2)
                          | ~ r2_hidden(k4_tarski(X6,X5),X1)
                          | ~ l1_waybel_0(X6,X0)
                          | ~ v7_waybel_0(X6)
                          | ~ v4_orders_2(X6)
                          | v2_struct_0(X6) )
                      | ~ r2_hidden(X5,X2)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | v3_pre_topc(X2,k13_yellow_6(X0,X1)) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(X0,X1)))) )
            & m4_yellow_6(X1,X0) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_waybel_0(sK5,X4,X2)
                        & r2_hidden(k4_tarski(X4,X3),X1)
                        & l1_waybel_0(X4,sK5)
                        & v7_waybel_0(X4)
                        & v4_orders_2(X4)
                        & ~ v2_struct_0(X4) )
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(sK5)) )
                | ~ v3_pre_topc(X2,k13_yellow_6(sK5,X1)) )
              & ( ! [X5] :
                    ( ! [X6] :
                        ( r1_waybel_0(sK5,X6,X2)
                        | ~ r2_hidden(k4_tarski(X6,X5),X1)
                        | ~ l1_waybel_0(X6,sK5)
                        | ~ v7_waybel_0(X6)
                        | ~ v4_orders_2(X6)
                        | v2_struct_0(X6) )
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(sK5)) )
                | v3_pre_topc(X2,k13_yellow_6(sK5,X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k13_yellow_6(sK5,X1)))) )
          & m4_yellow_6(X1,sK5) )
      & l1_struct_0(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ( ~ r1_waybel_0(sK5,sK9,sK7)
        & r2_hidden(k4_tarski(sK9,sK8),sK6)
        & l1_waybel_0(sK9,sK5)
        & v7_waybel_0(sK9)
        & v4_orders_2(sK9)
        & ~ v2_struct_0(sK9)
        & r2_hidden(sK8,sK7)
        & m1_subset_1(sK8,u1_struct_0(sK5)) )
      | ~ v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) )
    & ( ! [X5] :
          ( ! [X6] :
              ( r1_waybel_0(sK5,X6,sK7)
              | ~ r2_hidden(k4_tarski(X6,X5),sK6)
              | ~ l1_waybel_0(X6,sK5)
              | ~ v7_waybel_0(X6)
              | ~ v4_orders_2(X6)
              | v2_struct_0(X6) )
          | ~ r2_hidden(X5,sK7)
          | ~ m1_subset_1(X5,u1_struct_0(sK5)) )
      | v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k13_yellow_6(sK5,sK6))))
    & m4_yellow_6(sK6,sK5)
    & l1_struct_0(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f36,f41,f40,f39,f38,f37])).

fof(f69,plain,(
    ! [X6,X5] :
      ( r1_waybel_0(sK5,X6,sK7)
      | ~ r2_hidden(k4_tarski(X6,X5),sK6)
      | ~ l1_waybel_0(X6,sK5)
      | ~ v7_waybel_0(X6)
      | ~ v4_orders_2(X6)
      | v2_struct_0(X6)
      | ~ r2_hidden(X5,sK7)
      | ~ m1_subset_1(X5,u1_struct_0(sK5))
      | v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | ~ v2_struct_0(sK3(X0,X1,X3))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1,X3)
      | ~ v2_struct_0(sK3(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | v7_waybel_0(sK3(X0,X1,X3))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1,X3)
      | v7_waybel_0(sK3(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | v4_orders_2(sK3(X0,X1,X3))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1,X3)
      | v4_orders_2(sK3(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f68,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k13_yellow_6(sK5,sK6)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m4_yellow_6(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k13_yellow_6(X0,X1) = X2
              <=> ( u1_pre_topc(X2) = a_2_1_yellow_6(X0,X1)
                  & u1_struct_0(X0) = u1_struct_0(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k13_yellow_6(X0,X1) = X2
              <=> ( u1_pre_topc(X2) = a_2_1_yellow_6(X0,X1)
                  & u1_struct_0(X0) = u1_struct_0(X2) ) )
              | ~ l1_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m4_yellow_6(X1,X0) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k13_yellow_6(X0,X1) = X2
              <=> ( u1_pre_topc(X2) = a_2_1_yellow_6(X0,X1)
                  & u1_struct_0(X0) = u1_struct_0(X2) ) )
              | ~ l1_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m4_yellow_6(X1,X0) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k13_yellow_6(X0,X1) = X2
                  | u1_pre_topc(X2) != a_2_1_yellow_6(X0,X1)
                  | u1_struct_0(X0) != u1_struct_0(X2) )
                & ( ( u1_pre_topc(X2) = a_2_1_yellow_6(X0,X1)
                    & u1_struct_0(X0) = u1_struct_0(X2) )
                  | k13_yellow_6(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m4_yellow_6(X1,X0) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k13_yellow_6(X0,X1) = X2
                  | u1_pre_topc(X2) != a_2_1_yellow_6(X0,X1)
                  | u1_struct_0(X0) != u1_struct_0(X2) )
                & ( ( u1_pre_topc(X2) = a_2_1_yellow_6(X0,X1)
                    & u1_struct_0(X0) = u1_struct_0(X2) )
                  | k13_yellow_6(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m4_yellow_6(X1,X0) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(X2)
      | k13_yellow_6(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m4_yellow_6(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k13_yellow_6(X0,X1))
      | ~ l1_pre_topc(k13_yellow_6(X0,X1))
      | ~ v1_pre_topc(k13_yellow_6(X0,X1))
      | ~ m4_yellow_6(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m4_yellow_6(X1,X0)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k13_yellow_6(X0,X1))
        & v1_pre_topc(k13_yellow_6(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k13_yellow_6(X0,X1))
        & v1_pre_topc(k13_yellow_6(X0,X1)) )
      | ~ m4_yellow_6(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k13_yellow_6(X0,X1))
        & v1_pre_topc(k13_yellow_6(X0,X1)) )
      | ~ m4_yellow_6(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k13_yellow_6(X0,X1))
      | ~ m4_yellow_6(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k13_yellow_6(X0,X1))
      | ~ m4_yellow_6(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    m4_yellow_6(sK6,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | ~ r1_waybel_0(X0,sK3(X0,X1,X3),X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1,X3)
      | ~ r1_waybel_0(X0,sK3(X0,X1,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m4_yellow_6(X2,X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X3)
                 => ! [X5] :
                      ( ( l1_waybel_0(X5,X1)
                        & v7_waybel_0(X5)
                        & v4_orders_2(X5)
                        & ~ v2_struct_0(X5) )
                     => ( r2_hidden(k4_tarski(X5,X4),X2)
                       => r1_waybel_0(X1,X5,X3) ) ) ) )
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( r1_waybel_0(X1,X5,X3)
                    | ~ r2_hidden(k4_tarski(X5,X4),X2)
                    | ~ l1_waybel_0(X5,X1)
                    | ~ v7_waybel_0(X5)
                    | ~ v4_orders_2(X5)
                    | v2_struct_0(X5) )
                | ~ r2_hidden(X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( r1_waybel_0(X1,X5,X3)
                    | ~ r2_hidden(k4_tarski(X5,X4),X2)
                    | ~ l1_waybel_0(X5,X1)
                    | ~ v7_waybel_0(X5)
                    | ~ v4_orders_2(X5)
                    | v2_struct_0(X5) )
                | ~ r2_hidden(X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f21,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f15,f21,f20])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ m4_yellow_6(X2,X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_1_yellow_6(X1,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_1_yellow_6(X1,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_yellow_6(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_yellow_6(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f26])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_yellow_6(X2,X1))
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( u1_pre_topc(X2) = a_2_1_yellow_6(X0,X1)
      | k13_yellow_6(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m4_yellow_6(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k13_yellow_6(X0,X1)) = a_2_1_yellow_6(X0,X1)
      | ~ l1_pre_topc(k13_yellow_6(X0,X1))
      | ~ v1_pre_topc(k13_yellow_6(X0,X1))
      | ~ m4_yellow_6(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X3),X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1,X3)
      | r2_hidden(sK2(X0,X1,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(equality_resolution,[],[f56])).

fof(f76,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK6)
    | ~ v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) ),
    inference(cnf_transformation,[],[f42])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | ~ r2_hidden(X0,a_2_1_yellow_6(X2,X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sK4(X0,X1,X2) = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r1_waybel_0(X0,X8,sK4(X0,X1,X2))
      | ~ r2_hidden(k4_tarski(X8,X7),X1)
      | ~ l1_waybel_0(X8,X0)
      | ~ v7_waybel_0(X8)
      | ~ v4_orders_2(X8)
      | v2_struct_0(X8)
      | ~ r2_hidden(X7,sK4(X0,X1,X2))
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,
    ( ~ r1_waybel_0(sK5,sK9,sK7)
    | ~ v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,
    ( l1_waybel_0(sK9,sK5)
    | ~ v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,
    ( v7_waybel_0(sK9)
    | ~ v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,
    ( v4_orders_2(sK9)
    | ~ v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,
    ( ~ v2_struct_0(sK9)
    | ~ v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,
    ( r2_hidden(sK8,sK7)
    | ~ v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_11,plain,
    ( sP0(X0,X1,X2)
    | l1_waybel_0(sK3(X0,X1,X2),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_5743,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | l1_waybel_0(sK3(X0,X1,X2),X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( sP0(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_5744,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_30,negated_conjecture,
    ( r1_waybel_0(sK5,X0,sK7)
    | ~ l1_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X1,sK7)
    | ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | v3_pre_topc(sK7,k13_yellow_6(sK5,sK6))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_5725,plain,
    ( r1_waybel_0(sK5,X0,sK7) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7793,plain,
    ( r1_waybel_0(sK5,sK3(X0,sK6,X1),sK7) = iProver_top
    | sP0(X0,sK6,X1) = iProver_top
    | l1_waybel_0(sK3(X0,sK6,X1),sK5) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK2(X0,sK6,X1),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK2(X0,sK6,X1),sK7) != iProver_top
    | v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) = iProver_top
    | v4_orders_2(sK3(X0,sK6,X1)) != iProver_top
    | v7_waybel_0(sK3(X0,sK6,X1)) != iProver_top
    | v2_struct_0(sK3(X0,sK6,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5744,c_5725])).

cnf(c_14,plain,
    ( sP0(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_struct_0(sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_5740,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(sK3(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,plain,
    ( sP0(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | v7_waybel_0(sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_5742,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v7_waybel_0(sK3(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( sP0(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | v4_orders_2(sK3(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_5741,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v4_orders_2(sK3(X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k13_yellow_6(sK5,sK6)))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_5724,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k13_yellow_6(sK5,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2,plain,
    ( ~ m4_yellow_6(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_pre_topc(k13_yellow_6(X1,X0))
    | ~ l1_pre_topc(k13_yellow_6(X1,X0))
    | u1_struct_0(k13_yellow_6(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_6,plain,
    ( ~ m4_yellow_6(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_pre_topc(k13_yellow_6(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_5,plain,
    ( ~ m4_yellow_6(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | l1_pre_topc(k13_yellow_6(X1,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_219,plain,
    ( ~ m4_yellow_6(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | u1_struct_0(k13_yellow_6(X1,X0)) = u1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_6,c_5])).

cnf(c_32,negated_conjecture,
    ( m4_yellow_6(sK6,sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_652,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(k13_yellow_6(X0,X1)) = u1_struct_0(X0)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_219,c_32])).

cnf(c_653,plain,
    ( v2_struct_0(sK5)
    | ~ l1_struct_0(sK5)
    | u1_struct_0(k13_yellow_6(sK5,sK6)) = u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33,negated_conjecture,
    ( l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_655,plain,
    ( u1_struct_0(k13_yellow_6(sK5,sK6)) = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_653,c_34,c_33])).

cnf(c_5752,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5724,c_655])).

cnf(c_21,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5734,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6662,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5752,c_5734])).

cnf(c_8022,plain,
    ( r1_waybel_0(sK5,sK3(X0,sK6,X1),sK7) = iProver_top
    | sP0(X0,sK6,X1) = iProver_top
    | l1_waybel_0(sK3(X0,sK6,X1),sK5) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(sK2(X0,sK6,X1),sK7) != iProver_top
    | v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7793,c_5740,c_5742,c_5741,c_6662])).

cnf(c_9,plain,
    ( ~ r1_waybel_0(X0,sK3(X0,X1,X2),X2)
    | sP0(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_5745,plain,
    ( r1_waybel_0(X0,sK3(X0,X1,X2),X2) != iProver_top
    | sP0(X0,X1,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8026,plain,
    ( sP0(sK5,sK6,sK7) = iProver_top
    | l1_waybel_0(sK3(sK5,sK6,sK7),sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK2(sK5,sK6,sK7),sK7) != iProver_top
    | v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8022,c_5745])).

cnf(c_20,plain,
    ( sP1(X0,X1,X2)
    | ~ m4_yellow_6(X1,X2)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | r2_hidden(X0,a_2_1_yellow_6(X2,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_470,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X2,a_2_1_yellow_6(X0,X1))
    | ~ m4_yellow_6(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_20,c_7])).

cnf(c_608,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_hidden(X2,a_2_1_yellow_6(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_470,c_32])).

cnf(c_609,plain,
    ( ~ sP0(sK5,sK6,X0)
    | r2_hidden(X0,a_2_1_yellow_6(sK5,sK6))
    | v2_struct_0(sK5)
    | ~ l1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_613,plain,
    ( ~ sP0(sK5,sK6,X0)
    | r2_hidden(X0,a_2_1_yellow_6(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_34,c_33])).

cnf(c_2911,plain,
    ( ~ sP0(sK5,sK6,X0)
    | r2_hidden(X0,a_2_1_yellow_6(sK5,sK6)) ),
    inference(prop_impl,[status(thm)],[c_34,c_33,c_609])).

cnf(c_5722,plain,
    ( sP0(sK5,sK6,X0) != iProver_top
    | r2_hidden(X0,a_2_1_yellow_6(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2911])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_671,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | l1_pre_topc(k13_yellow_6(X0,X1))
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_32])).

cnf(c_672,plain,
    ( v2_struct_0(sK5)
    | ~ l1_struct_0(sK5)
    | l1_pre_topc(k13_yellow_6(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_671])).

cnf(c_674,plain,
    ( l1_pre_topc(k13_yellow_6(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_672,c_34,c_33])).

cnf(c_744,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | k13_yellow_6(sK5,sK6) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_674])).

cnf(c_745,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k13_yellow_6(sK5,sK6))))
    | ~ r2_hidden(X0,u1_pre_topc(k13_yellow_6(sK5,sK6)))
    | v3_pre_topc(X0,k13_yellow_6(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_5719,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k13_yellow_6(sK5,sK6)))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(k13_yellow_6(sK5,sK6))) != iProver_top
    | v3_pre_topc(X0,k13_yellow_6(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_1,plain,
    ( ~ m4_yellow_6(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_pre_topc(k13_yellow_6(X1,X0))
    | ~ l1_pre_topc(k13_yellow_6(X1,X0))
    | u1_pre_topc(k13_yellow_6(X1,X0)) = a_2_1_yellow_6(X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_226,plain,
    ( ~ m4_yellow_6(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | u1_pre_topc(k13_yellow_6(X1,X0)) = a_2_1_yellow_6(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1,c_6,c_5])).

cnf(c_644,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_pre_topc(k13_yellow_6(X0,X1)) = a_2_1_yellow_6(X0,X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_226,c_32])).

cnf(c_645,plain,
    ( v2_struct_0(sK5)
    | ~ l1_struct_0(sK5)
    | u1_pre_topc(k13_yellow_6(sK5,sK6)) = a_2_1_yellow_6(sK5,sK6) ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_647,plain,
    ( u1_pre_topc(k13_yellow_6(sK5,sK6)) = a_2_1_yellow_6(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_645,c_34,c_33])).

cnf(c_5851,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0,a_2_1_yellow_6(sK5,sK6)) != iProver_top
    | v3_pre_topc(X0,k13_yellow_6(sK5,sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5719,c_647,c_655])).

cnf(c_6474,plain,
    ( sP0(sK5,sK6,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_pre_topc(X0,k13_yellow_6(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5722,c_5851])).

cnf(c_6533,plain,
    ( sP0(sK5,sK6,sK7) != iProver_top
    | v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5752,c_6474])).

cnf(c_15,plain,
    ( sP0(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(sK2(X0,X1,X2),X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_6203,plain,
    ( sP0(X0,X1,sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(sK2(X0,X1,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_7893,plain,
    ( sP0(sK5,sK6,sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK2(sK5,sK6,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_6203])).

cnf(c_7894,plain,
    ( sP0(sK5,sK6,sK7) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK2(sK5,sK6,sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7893])).

cnf(c_8364,plain,
    ( l1_waybel_0(sK3(sK5,sK6,sK7),sK5) != iProver_top
    | v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8026,c_5752,c_6533,c_7894])).

cnf(c_8370,plain,
    ( sP0(sK5,sK6,sK7) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5743,c_8364])).

cnf(c_8409,plain,
    ( v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8370,c_5752,c_6533])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(k4_tarski(sK9,sK8),sK6)
    | ~ v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_5732,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK6) = iProver_top
    | v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8415,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_8409,c_5732])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_729,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | k13_yellow_6(sK5,sK6) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_674])).

cnf(c_730,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k13_yellow_6(sK5,sK6))))
    | r2_hidden(X0,u1_pre_topc(k13_yellow_6(sK5,sK6)))
    | ~ v3_pre_topc(X0,k13_yellow_6(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_5720,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k13_yellow_6(sK5,sK6)))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(k13_yellow_6(sK5,sK6))) = iProver_top
    | v3_pre_topc(X0,k13_yellow_6(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_5858,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0,a_2_1_yellow_6(sK5,sK6)) = iProver_top
    | v3_pre_topc(X0,k13_yellow_6(sK5,sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5720,c_647,c_655])).

cnf(c_8422,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK7,a_2_1_yellow_6(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8409,c_5858])).

cnf(c_8894,plain,
    ( r2_hidden(sK7,a_2_1_yellow_6(sK5,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8422,c_5752])).

cnf(c_8,plain,
    ( ~ sP1(X0,X1,X2)
    | sP0(X2,X1,X0)
    | ~ r2_hidden(X0,a_2_1_yellow_6(X2,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_450,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(X2,a_2_1_yellow_6(X0,X1))
    | ~ m4_yellow_6(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_20,c_8])).

cnf(c_626,plain,
    ( sP0(X0,X1,X2)
    | ~ r2_hidden(X2,a_2_1_yellow_6(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_450,c_32])).

cnf(c_627,plain,
    ( sP0(sK5,sK6,X0)
    | ~ r2_hidden(X0,a_2_1_yellow_6(sK5,sK6))
    | v2_struct_0(sK5)
    | ~ l1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_631,plain,
    ( sP0(sK5,sK6,X0)
    | ~ r2_hidden(X0,a_2_1_yellow_6(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_627,c_34,c_33])).

cnf(c_2909,plain,
    ( sP0(sK5,sK6,X0)
    | ~ r2_hidden(X0,a_2_1_yellow_6(sK5,sK6)) ),
    inference(prop_impl,[status(thm)],[c_34,c_33,c_627])).

cnf(c_5721,plain,
    ( sP0(sK5,sK6,X0) = iProver_top
    | r2_hidden(X0,a_2_1_yellow_6(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2909])).

cnf(c_8900,plain,
    ( sP0(sK5,sK6,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_8894,c_5721])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1,X2)
    | sK4(X0,X1,X2) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5736,plain,
    ( sK4(X0,X1,X2) = X2
    | sP0(X0,X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8967,plain,
    ( sK4(sK5,sK6,sK7) = sK7 ),
    inference(superposition,[status(thm)],[c_8900,c_5736])).

cnf(c_17,plain,
    ( r1_waybel_0(X0,X1,sK4(X0,X2,X3))
    | ~ sP0(X0,X2,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r2_hidden(X4,sK4(X0,X2,X3))
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_5737,plain,
    ( r1_waybel_0(X0,X1,sK4(X0,X2,X3)) = iProver_top
    | sP0(X0,X2,X3) != iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X4,sK4(X0,X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X1,X4),X2) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9044,plain,
    ( r1_waybel_0(sK5,X0,sK4(sK5,sK6,sK7)) = iProver_top
    | sP0(sK5,sK6,sK7) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8967,c_5737])).

cnf(c_9055,plain,
    ( r1_waybel_0(sK5,X0,sK7) = iProver_top
    | sP0(sK5,sK6,sK7) != iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9044,c_8967])).

cnf(c_6676,plain,
    ( sP0(sK5,sK6,sK7)
    | ~ r2_hidden(sK7,a_2_1_yellow_6(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2909])).

cnf(c_6677,plain,
    ( sP0(sK5,sK6,sK7) = iProver_top
    | r2_hidden(sK7,a_2_1_yellow_6(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6676])).

cnf(c_9284,plain,
    ( r1_waybel_0(sK5,X0,sK7) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9055,c_5752,c_6677,c_8422])).

cnf(c_9298,plain,
    ( r1_waybel_0(sK5,X0,sK7) = iProver_top
    | l1_waybel_0(X0,sK5) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9284,c_6662])).

cnf(c_9303,plain,
    ( r1_waybel_0(sK5,sK9,sK7) = iProver_top
    | l1_waybel_0(sK9,sK5) != iProver_top
    | r2_hidden(sK8,sK7) != iProver_top
    | v4_orders_2(sK9) != iProver_top
    | v7_waybel_0(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_8415,c_9298])).

cnf(c_22,negated_conjecture,
    ( ~ r1_waybel_0(sK5,sK9,sK7)
    | ~ v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_49,plain,
    ( r1_waybel_0(sK5,sK9,sK7) != iProver_top
    | v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_24,negated_conjecture,
    ( l1_waybel_0(sK9,sK5)
    | ~ v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_47,plain,
    ( l1_waybel_0(sK9,sK5) = iProver_top
    | v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( ~ v3_pre_topc(sK7,k13_yellow_6(sK5,sK6))
    | v7_waybel_0(sK9) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_46,plain,
    ( v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) != iProver_top
    | v7_waybel_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( ~ v3_pre_topc(sK7,k13_yellow_6(sK5,sK6))
    | v4_orders_2(sK9) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_45,plain,
    ( v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) != iProver_top
    | v4_orders_2(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_27,negated_conjecture,
    ( ~ v3_pre_topc(sK7,k13_yellow_6(sK5,sK6))
    | ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_44,plain,
    ( v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) != iProver_top
    | v2_struct_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK8,sK7)
    | ~ v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_43,plain,
    ( r2_hidden(sK8,sK7) = iProver_top
    | v3_pre_topc(sK7,k13_yellow_6(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9303,c_8409,c_49,c_47,c_46,c_45,c_44,c_43])).


%------------------------------------------------------------------------------
