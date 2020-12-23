%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1624+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:00 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  141 (1197 expanded)
%              Number of clauses        :   86 ( 336 expanded)
%              Number of leaves         :   14 ( 401 expanded)
%              Depth                    :   31
%              Number of atoms          :  703 (8266 expanded)
%              Number of equality atoms :  276 (2275 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X4,X3)
                                & r1_orders_2(X0,X4,X2)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ( v2_waybel_0(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f15,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,X2)
                  & r2_hidden(X4,X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f8,f16,f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ( ( v2_waybel_0(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v2_waybel_0(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( v2_waybel_0(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_waybel_0(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f18])).

fof(f31,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v2_waybel_0(X0,X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_waybel_0(X2,X0)
                        & X2 = X3 )
                     => v2_waybel_0(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( ( v2_waybel_0(X2,X0)
                          & X2 = X3 )
                       => v2_waybel_0(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_waybel_0(X3,X1)
                  & v2_waybel_0(X2,X0)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_waybel_0(X3,X1)
                  & v2_waybel_0(X2,X0)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ v2_waybel_0(X3,X1)
          & v2_waybel_0(X2,X0)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_waybel_0(sK8,X1)
        & v2_waybel_0(X2,X0)
        & sK8 = X2
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_waybel_0(X3,X1)
              & v2_waybel_0(X2,X0)
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ~ v2_waybel_0(X3,X1)
            & v2_waybel_0(sK7,X0)
            & sK7 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_waybel_0(X3,X1)
                  & v2_waybel_0(X2,X0)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_waybel_0(X3,sK6)
                & v2_waybel_0(X2,X0)
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_waybel_0(X3,X1)
                    & v2_waybel_0(X2,X0)
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_waybel_0(X3,X1)
                  & v2_waybel_0(X2,sK5)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) )
          & g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ v2_waybel_0(sK8,sK6)
    & v2_waybel_0(sK7,sK5)
    & sK7 = sK8
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    & g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) = g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6))
    & l1_orders_2(sK6)
    & l1_orders_2(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f14,f29,f28,f27,f26])).

fof(f54,plain,(
    v2_waybel_0(sK7,sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f30])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X4,X3)
                    | ~ r1_orders_2(X0,X4,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( r1_orders_2(X0,X4,X3)
                    & r1_orders_2(X0,X4,X2)
                    & r2_hidden(X4,X1)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X4,X3)
                    | ~ r1_orders_2(X0,X4,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ? [X7] :
                    ( r1_orders_2(X0,X7,X6)
                    & r1_orders_2(X0,X7,X5)
                    & r2_hidden(X7,X1)
                    & m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X6,X5,X1,X0] :
      ( ? [X7] :
          ( r1_orders_2(X0,X7,X6)
          & r1_orders_2(X0,X7,X5)
          & r2_hidden(X7,X1)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,sK4(X0,X1,X5,X6),X6)
        & r1_orders_2(X0,sK4(X0,X1,X5,X6),X5)
        & r2_hidden(sK4(X0,X1,X5,X6),X1)
        & m1_subset_1(sK4(X0,X1,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_orders_2(X0,X4,X3)
              | ~ r1_orders_2(X0,X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r1_orders_2(X0,X4,sK3(X0,X1))
            | ~ r1_orders_2(X0,X4,X2)
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  | ~ r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                | ~ r1_orders_2(X0,X4,sK2(X0,X1))
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X3,X1)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X4] :
              ( ~ r1_orders_2(X0,X4,sK3(X0,X1))
              | ~ r1_orders_2(X0,X4,sK2(X0,X1))
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X1)
          & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
          & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( r1_orders_2(X0,sK4(X0,X1,X5,X6),X6)
                  & r1_orders_2(X0,sK4(X0,X1,X5,X6),X5)
                  & r2_hidden(sK4(X0,X1,X5,X6),X1)
                  & m1_subset_1(sK4(X0,X1,X5,X6),u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f24,f23,f22])).

fof(f34,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(sK4(X0,X1,X5,X6),X1)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    ! [X6,X0,X5,X1] :
      ( r1_orders_2(X0,sK4(X0,X1,X5,X6),X6)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) = g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X6,X0,X5,X1] :
      ( m1_subset_1(sK4(X0,X1,X5,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => ( ( r2_orders_2(X0,X2,X3)
                                 => r2_orders_2(X1,X4,X5) )
                                & ( r1_orders_2(X0,X2,X3)
                                 => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f59,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f49,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f35,plain,(
    ! [X6,X0,X5,X1] :
      ( r1_orders_2(X0,sK4(X0,X1,X5,X6),X5)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_orders_2(X0,X4,sK3(X0,X1))
      | ~ r1_orders_2(X0,X4,sK2(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X0,X1)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    ~ v2_waybel_0(sK8,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP1(X0,X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ v2_waybel_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_18,negated_conjecture,
    ( v2_waybel_0(sK7,sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_263,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | sK5 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_264,plain,
    ( ~ sP1(sK7,sK5)
    | sP0(sK5,sK7) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_297,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP0(sK5,sK7)
    | ~ l1_orders_2(X1)
    | sK5 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_264])).

cnf(c_298,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | sP0(sK5,sK7)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_300,plain,
    ( sP0(sK5,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_298,c_24,c_21])).

cnf(c_2346,plain,
    ( sP0(sK5,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_19,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2373,plain,
    ( sP0(sK5,sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2346,c_19])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,X3)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(sK4(X1,X3,X2,X0),X3)
    | ~ sP0(X1,X3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2357,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(X0,X3) != iProver_top
    | r2_hidden(sK4(X1,X3,X0,X2),X3) = iProver_top
    | sP0(X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X2,X1)
    | ~ sP0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2359,plain,
    ( r1_orders_2(X0,sK4(X0,X1,X2,X3),X3) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X3,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | sP0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_22,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) = g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2353,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3081,plain,
    ( g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK5) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_2353])).

cnf(c_12,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_38,plain,
    ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | ~ l1_orders_2(sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3082,plain,
    ( g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK5) = X0
    | m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_2353])).

cnf(c_3099,plain,
    ( ~ m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK5) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3082])).

cnf(c_3103,plain,
    ( u1_struct_0(sK5) = X0
    | g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3081,c_24,c_38,c_3099])).

cnf(c_3104,plain,
    ( g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK5) = X0 ),
    inference(renaming,[status(thm)],[c_3103])).

cnf(c_3109,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK6) ),
    inference(equality_resolution,[status(thm)],[c_3104])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK4(X1,X3,X2,X0),u1_struct_0(X1))
    | ~ r2_hidden(X0,X3)
    | ~ r2_hidden(X2,X3)
    | ~ sP0(X1,X3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2356,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK4(X1,X3,X0,X2),u1_struct_0(X1)) = iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(X0,X3) != iProver_top
    | sP0(X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3504,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK4(sK5,X2,X0,X1),u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | sP0(sK5,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3109,c_2356])).

cnf(c_3505,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK4(sK5,X2,X0,X1),u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | sP0(sK5,X2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3504,c_3109])).

cnf(c_16,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X3)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2352,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | r1_orders_2(X1,X2,X3) != iProver_top
    | r1_orders_2(X0,X2,X3) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3338,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK5))
    | r1_orders_2(X0,X1,X2) = iProver_top
    | r1_orders_2(sK5,X1,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3109,c_2352])).

cnf(c_3194,plain,
    ( g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK5)) = g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) ),
    inference(demodulation,[status(thm)],[c_3109,c_22])).

cnf(c_3349,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6))
    | r1_orders_2(X0,X1,X2) = iProver_top
    | r1_orders_2(sK5,X1,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3338,c_3109,c_3194])).

cnf(c_25,plain,
    ( l1_orders_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3538,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_orders_2(sK5,X1,X2) != iProver_top
    | r1_orders_2(X0,X1,X2) = iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3349,c_25])).

cnf(c_3539,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK6),u1_orders_2(sK6))
    | r1_orders_2(X0,X1,X2) = iProver_top
    | r1_orders_2(sK5,X1,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3538])).

cnf(c_3551,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | r1_orders_2(sK6,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3539])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_26,plain,
    ( l1_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4049,plain,
    ( m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r1_orders_2(sK6,X0,X1) = iProver_top
    | r1_orders_2(sK5,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3551,c_26])).

cnf(c_4050,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | r1_orders_2(sK6,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4049])).

cnf(c_4301,plain,
    ( r1_orders_2(sK5,sK4(sK5,X0,X1,X2),X3) != iProver_top
    | r1_orders_2(sK6,sK4(sK5,X0,X1,X2),X3) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | sP0(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3505,c_4050])).

cnf(c_4871,plain,
    ( r1_orders_2(sK6,sK4(sK5,X0,X1,X2),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | sP0(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2359,c_4301])).

cnf(c_4896,plain,
    ( r1_orders_2(sK6,sK4(sK5,X0,X1,X2),X2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | sP0(sK5,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4871,c_3109])).

cnf(c_8,plain,
    ( r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X2,X1)
    | ~ sP0(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2358,plain,
    ( r1_orders_2(X0,sK4(X0,X1,X2,X3),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X3,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | sP0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4872,plain,
    ( r1_orders_2(sK6,sK4(sK5,X0,X1,X2),X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | sP0(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2358,c_4301])).

cnf(c_4881,plain,
    ( r1_orders_2(sK6,sK4(sK5,X0,X1,X2),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | sP0(sK5,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4872,c_3109])).

cnf(c_2,plain,
    ( ~ r1_orders_2(X0,X1,sK2(X0,X2))
    | ~ r1_orders_2(X0,X1,sK3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X2)
    | sP0(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2364,plain,
    ( r1_orders_2(X0,X1,sK2(X0,X2)) != iProver_top
    | r1_orders_2(X0,X1,sK3(X0,X2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | sP0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4914,plain,
    ( r1_orders_2(sK6,sK4(sK5,X0,sK2(sK6,X1),X2),sK3(sK6,X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK4(sK5,X0,sK2(sK6,X1),X2),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK2(sK6,X1),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(sK4(sK5,X0,sK2(sK6,X1),X2),X1) != iProver_top
    | r2_hidden(sK2(sK6,X1),X0) != iProver_top
    | sP0(sK5,X0) != iProver_top
    | sP0(sK6,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4881,c_2364])).

cnf(c_6,plain,
    ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
    | sP0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2360,plain,
    ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) = iProver_top
    | sP0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6020,plain,
    ( r1_orders_2(sK6,sK4(sK5,X0,sK2(sK6,X1),X2),sK3(sK6,X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(sK4(sK5,X0,sK2(sK6,X1),X2),X1) != iProver_top
    | r2_hidden(sK2(sK6,X1),X0) != iProver_top
    | sP0(sK5,X0) != iProver_top
    | sP0(sK6,X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4914,c_2360,c_3505])).

cnf(c_6024,plain,
    ( m1_subset_1(sK2(sK6,X0),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK3(sK6,X0),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK4(sK5,X1,sK2(sK6,X0),sK3(sK6,X0)),X0) != iProver_top
    | r2_hidden(sK2(sK6,X0),X1) != iProver_top
    | r2_hidden(sK3(sK6,X0),X1) != iProver_top
    | sP0(sK5,X1) != iProver_top
    | sP0(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4896,c_6020])).

cnf(c_5,plain,
    ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
    | sP0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3460,plain,
    ( m1_subset_1(sK3(sK6,X0),u1_struct_0(sK6))
    | sP0(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3461,plain,
    ( m1_subset_1(sK3(sK6,X0),u1_struct_0(sK6)) = iProver_top
    | sP0(sK6,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3460])).

cnf(c_3459,plain,
    ( m1_subset_1(sK2(sK6,X0),u1_struct_0(sK6))
    | sP0(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3465,plain,
    ( m1_subset_1(sK2(sK6,X0),u1_struct_0(sK6)) = iProver_top
    | sP0(sK6,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3459])).

cnf(c_6118,plain,
    ( r2_hidden(sK4(sK5,X1,sK2(sK6,X0),sK3(sK6,X0)),X0) != iProver_top
    | r2_hidden(sK2(sK6,X0),X1) != iProver_top
    | r2_hidden(sK3(sK6,X0),X1) != iProver_top
    | sP0(sK5,X1) != iProver_top
    | sP0(sK6,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6024,c_3461,c_3465])).

cnf(c_6119,plain,
    ( r2_hidden(sK4(sK5,X0,sK2(sK6,X1),sK3(sK6,X1)),X1) != iProver_top
    | r2_hidden(sK2(sK6,X1),X0) != iProver_top
    | r2_hidden(sK3(sK6,X1),X0) != iProver_top
    | sP0(sK5,X0) != iProver_top
    | sP0(sK6,X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_6118])).

cnf(c_6129,plain,
    ( m1_subset_1(sK2(sK6,X0),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK3(sK6,X0),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK2(sK6,X0),X0) != iProver_top
    | r2_hidden(sK3(sK6,X0),X0) != iProver_top
    | sP0(sK5,X0) != iProver_top
    | sP0(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2357,c_6119])).

cnf(c_6130,plain,
    ( m1_subset_1(sK2(sK6,X0),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK3(sK6,X0),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0),X0) != iProver_top
    | r2_hidden(sK3(sK6,X0),X0) != iProver_top
    | sP0(sK5,X0) != iProver_top
    | sP0(sK6,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6129,c_3109])).

cnf(c_3,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | sP0(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3458,plain,
    ( r2_hidden(sK3(sK6,X0),X0)
    | sP0(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3469,plain,
    ( r2_hidden(sK3(sK6,X0),X0) = iProver_top
    | sP0(sK6,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3458])).

cnf(c_4,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | sP0(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3457,plain,
    ( r2_hidden(sK2(sK6,X0),X0)
    | sP0(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3473,plain,
    ( r2_hidden(sK2(sK6,X0),X0) = iProver_top
    | sP0(sK6,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3457])).

cnf(c_6135,plain,
    ( sP0(sK5,X0) != iProver_top
    | sP0(sK6,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6130,c_3461,c_3465,c_3469,c_3473])).

cnf(c_6143,plain,
    ( sP0(sK6,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2373,c_6135])).

cnf(c_0,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | v2_waybel_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_17,negated_conjecture,
    ( ~ v2_waybel_0(sK8,sK6) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_253,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | sK6 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_254,plain,
    ( ~ sP1(sK8,sK6)
    | ~ sP0(sK6,sK8) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_286,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ sP0(sK6,sK8)
    | ~ l1_orders_2(X1)
    | sK6 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_254])).

cnf(c_287,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ sP0(sK6,sK8)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_288,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | sP0(sK6,sK8) != iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_28,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6143,c_288,c_28,c_26])).


%------------------------------------------------------------------------------
