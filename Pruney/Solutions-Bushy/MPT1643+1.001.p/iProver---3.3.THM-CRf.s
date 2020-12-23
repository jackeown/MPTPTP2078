%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1643+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:04 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 750 expanded)
%              Number of clauses        :   99 ( 218 expanded)
%              Number of leaves         :   16 ( 178 expanded)
%              Depth                    :   22
%              Number of atoms          :  743 (4291 expanded)
%              Number of equality atoms :  171 ( 306 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ( k3_waybel_0(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( ( r2_hidden(X3,X2)
          <=> ? [X4] :
                ( r2_hidden(X4,X1)
                & r1_orders_2(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f8,f18,f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ( ( k3_waybel_0(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k3_waybel_0(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( k3_waybel_0(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k3_waybel_0(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f20])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k3_waybel_0(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k3_waybel_0(X1,X2))
      | ~ sP1(k3_waybel_0(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> r1_tarski(k3_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v12_waybel_0(X1,X0)
            <=> r1_tarski(k3_waybel_0(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v12_waybel_0(X1,X0)
          <~> r1_tarski(k3_waybel_0(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(k3_waybel_0(X0,X1),X1)
            | ~ v12_waybel_0(X1,X0) )
          & ( r1_tarski(k3_waybel_0(X0,X1),X1)
            | v12_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(k3_waybel_0(X0,X1),X1)
            | ~ v12_waybel_0(X1,X0) )
          & ( r1_tarski(k3_waybel_0(X0,X1),X1)
            | v12_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(k3_waybel_0(X0,X1),X1)
            | ~ v12_waybel_0(X1,X0) )
          & ( r1_tarski(k3_waybel_0(X0,X1),X1)
            | v12_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r1_tarski(k3_waybel_0(X0,sK9),sK9)
          | ~ v12_waybel_0(sK9,X0) )
        & ( r1_tarski(k3_waybel_0(X0,sK9),sK9)
          | v12_waybel_0(sK9,X0) )
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(k3_waybel_0(X0,X1),X1)
              | ~ v12_waybel_0(X1,X0) )
            & ( r1_tarski(k3_waybel_0(X0,X1),X1)
              | v12_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(k3_waybel_0(sK8,X1),X1)
            | ~ v12_waybel_0(X1,sK8) )
          & ( r1_tarski(k3_waybel_0(sK8,X1),X1)
            | v12_waybel_0(X1,sK8) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) )
      & l1_orders_2(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ~ r1_tarski(k3_waybel_0(sK8,sK9),sK9)
      | ~ v12_waybel_0(sK9,sK8) )
    & ( r1_tarski(k3_waybel_0(sK8,sK9),sK9)
      | v12_waybel_0(sK9,sK8) )
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & l1_orders_2(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f39,f41,f40])).

fof(f66,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f42])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r1_orders_2(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r1_orders_2(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r1_orders_2(X0,X3,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
              & ( ? [X4] :
                    ( r2_hidden(X4,X1)
                    & r1_orders_2(X0,X3,X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r1_orders_2(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r1_orders_2(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r1_orders_2(X0,X3,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
              & ( ? [X4] :
                    ( r2_hidden(X4,X1)
                    & r1_orders_2(X0,X3,X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X0)
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r2_hidden(X5,X0)
                  & r1_orders_2(X1,X3,X5)
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ! [X7] :
                    ( ~ r2_hidden(X7,X0)
                    | ~ r1_orders_2(X1,X6,X7)
                    | ~ m1_subset_1(X7,u1_struct_0(X1)) ) )
              & ( ? [X8] :
                    ( r2_hidden(X8,X0)
                    & r1_orders_2(X1,X6,X8)
                    & m1_subset_1(X8,u1_struct_0(X1)) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X0)
          & r1_orders_2(X1,X6,X8)
          & m1_subset_1(X8,u1_struct_0(X1)) )
     => ( r2_hidden(sK4(X0,X1,X6),X0)
        & r1_orders_2(X1,X6,sK4(X0,X1,X6))
        & m1_subset_1(sK4(X0,X1,X6),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X0)
          & r1_orders_2(X1,X3,X5)
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r2_hidden(sK3(X0,X1,X2),X0)
        & r1_orders_2(X1,X3,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X0)
                & r1_orders_2(X1,X3,X5)
                & m1_subset_1(X5,u1_struct_0(X1)) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X0)
              | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X0)
              & r1_orders_2(X1,sK2(X0,X1,X2),X5)
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | r2_hidden(sK2(X0,X1,X2),X2) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X0)
              & r1_orders_2(X1,sK2(X0,X1,X2),sK3(X0,X1,X2))
              & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
            | r2_hidden(sK2(X0,X1,X2),X2) )
          & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ! [X7] :
                    ( ~ r2_hidden(X7,X0)
                    | ~ r1_orders_2(X1,X6,X7)
                    | ~ m1_subset_1(X7,u1_struct_0(X1)) ) )
              & ( ( r2_hidden(sK4(X0,X1,X6),X0)
                  & r1_orders_2(X1,X6,sK4(X0,X1,X6))
                  & m1_subset_1(sK4(X0,X1,X6),u1_struct_0(X1)) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f27,f26,f25])).

fof(f47,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X0)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X1,X6,sK4(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X3,X2)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f29])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X3,X2)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r1_orders_2(X0,sK6(X0,X1),X2)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X3,X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,X3,sK5(X0,X1))
            & r2_hidden(sK5(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK6(X0,X1),X1)
                & r1_orders_2(X0,sK6(X0,X1),sK5(X0,X1))
                & r2_hidden(sK5(X0,X1),X1)
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f30,f32,f31])).

fof(f55,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X5,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,
    ( r1_tarski(k3_waybel_0(sK8,sK9),sK9)
    | v12_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | r2_hidden(sK5(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | ~ r2_hidden(sK6(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | r1_orders_2(X0,sK6(X0,X1),sK5(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X0)
      | ~ r1_orders_2(X1,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,
    ( ~ r1_tarski(k3_waybel_0(sK8,sK9),sK9)
    | ~ v12_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK7(X0,X1),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4238,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK7(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1,plain,
    ( ~ sP1(k3_waybel_0(X0,X1),X0,X1)
    | sP0(X1,X0,k3_waybel_0(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_392,plain,
    ( sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_orders_2(X3)
    | X1 != X3
    | X0 != X4
    | k3_waybel_0(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_1])).

cnf(c_393,plain,
    ( sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k3_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ l1_orders_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_393,c_21])).

cnf(c_398,plain,
    ( sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_397])).

cnf(c_26,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_496,plain,
    ( sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_398,c_26])).

cnf(c_497,plain,
    ( sP0(X0,sK8,k3_waybel_0(sK8,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_4232,plain,
    ( sP0(X0,sK8,k3_waybel_0(sK8,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,X2)
    | r2_hidden(sK4(X0,X1,X3),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_4242,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(sK4(X0,X1,X3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5781,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,k3_waybel_0(sK8,X0)) != iProver_top
    | r2_hidden(sK4(X0,sK8,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4232,c_4242])).

cnf(c_1725,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(sK4(X4,X2,X1),X4)
    | X0 != X4
    | k3_waybel_0(sK8,X0) != X3
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_497])).

cnf(c_1726,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,k3_waybel_0(sK8,X0))
    | r2_hidden(sK4(X0,sK8,X1),X0) ),
    inference(unflattening,[status(thm)],[c_1725])).

cnf(c_1727,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,k3_waybel_0(sK8,X0)) != iProver_top
    | r2_hidden(sK4(X0,sK8,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1726])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(k3_waybel_0(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_4230,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(k3_waybel_0(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_22,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4236,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5223,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) = iProver_top
    | r2_hidden(X1,k3_waybel_0(sK8,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4230,c_4236])).

cnf(c_5969,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X1,k3_waybel_0(sK8,X0)) != iProver_top
    | r2_hidden(sK4(X0,sK8,X1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5781,c_1727,c_5223])).

cnf(c_9,plain,
    ( r1_orders_2(X0,X1,sK4(X2,X0,X1))
    | ~ sP0(X2,X0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4241,plain,
    ( r1_orders_2(X0,X1,sK4(X2,X0,X1)) = iProver_top
    | sP0(X2,X0,X3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5837,plain,
    ( r1_orders_2(sK8,X0,sK4(X1,sK8,X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,k3_waybel_0(sK8,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4232,c_4241])).

cnf(c_6135,plain,
    ( r1_orders_2(sK8,X0,sK4(X1,sK8,X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X0,k3_waybel_0(sK8,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5837,c_5223])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4233,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_17,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v12_waybel_0(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_598,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v12_waybel_0(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X3)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_599,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ v12_waybel_0(X2,sK8)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,X2) ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_615,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ v12_waybel_0(X2,sK8)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_599,c_22])).

cnf(c_4225,plain,
    ( r1_orders_2(sK8,X0,X1) != iProver_top
    | v12_waybel_0(X2,sK8) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_5192,plain,
    ( r1_orders_2(sK8,X0,X1) != iProver_top
    | v12_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,sK9) != iProver_top
    | r2_hidden(X0,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_4233,c_4225])).

cnf(c_6141,plain,
    ( v12_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,k3_waybel_0(sK8,X0)) != iProver_top
    | r2_hidden(X1,sK9) = iProver_top
    | r2_hidden(sK4(X0,sK8,X1),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6135,c_5192])).

cnf(c_6231,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v12_waybel_0(sK9,sK8) != iProver_top
    | r2_hidden(X1,k3_waybel_0(sK8,X0)) != iProver_top
    | r2_hidden(X1,sK9) = iProver_top
    | r2_hidden(sK4(X0,sK8,X1),sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6141,c_5223])).

cnf(c_6232,plain,
    ( v12_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X1,k3_waybel_0(sK8,X0)) != iProver_top
    | r2_hidden(X1,sK9) = iProver_top
    | r2_hidden(sK4(X0,sK8,X1),sK9) != iProver_top ),
    inference(renaming,[status(thm)],[c_6231])).

cnf(c_6242,plain,
    ( v12_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X0,k3_waybel_0(sK8,sK9)) != iProver_top
    | r2_hidden(X0,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_5969,c_6232])).

cnf(c_28,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k3_waybel_0(sK8,sK9),sK9)
    | v12_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4234,plain,
    ( r1_tarski(k3_waybel_0(sK8,sK9),sK9) = iProver_top
    | v12_waybel_0(sK9,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_4237,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4683,plain,
    ( v12_waybel_0(sK9,sK8) = iProver_top
    | r2_hidden(X0,k3_waybel_0(sK8,sK9)) != iProver_top
    | r2_hidden(X0,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_4234,c_4237])).

cnf(c_4879,plain,
    ( r1_tarski(k3_waybel_0(sK8,sK9),X0) = iProver_top
    | v12_waybel_0(sK9,sK8) = iProver_top
    | r2_hidden(sK7(k3_waybel_0(sK8,sK9),X0),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_4238,c_4683])).

cnf(c_29,plain,
    ( r1_tarski(k3_waybel_0(sK8,sK9),sK9) = iProver_top
    | v12_waybel_0(sK9,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_498,plain,
    ( sP0(X0,sK8,k3_waybel_0(sK8,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_500,plain,
    ( sP0(sK9,sK8,k3_waybel_0(sK8,sK9)) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_498])).

cnf(c_16,plain,
    ( v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_538,plain,
    ( v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_539,plain,
    ( v12_waybel_0(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_540,plain,
    ( v12_waybel_0(X0,sK8) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(sK5(sK8,X0),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_542,plain,
    ( v12_waybel_0(sK9,sK8) = iProver_top
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_15,plain,
    ( v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK6(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_553,plain,
    ( v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK6(X1,X0),u1_struct_0(X1))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_554,plain,
    ( v12_waybel_0(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_555,plain,
    ( v12_waybel_0(X0,sK8) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_557,plain,
    ( v12_waybel_0(sK9,sK8) = iProver_top
    | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_555])).

cnf(c_14,plain,
    ( v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK5(X1,X0),X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_568,plain,
    ( v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK5(X1,X0),X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_569,plain,
    ( v12_waybel_0(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(sK5(sK8,X0),X0) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_570,plain,
    ( v12_waybel_0(X0,sK8) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK5(sK8,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_569])).

cnf(c_572,plain,
    ( v12_waybel_0(sK9,sK8) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK5(sK8,sK9),sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_12,plain,
    ( v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK6(X1,X0),X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_583,plain,
    ( v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK6(X1,X0),X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_26])).

cnf(c_584,plain,
    ( v12_waybel_0(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(sK6(sK8,X0),X0) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_585,plain,
    ( v12_waybel_0(X0,sK8) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK6(sK8,X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_587,plain,
    ( v12_waybel_0(sK9,sK8) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK6(sK8,sK9),sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_585])).

cnf(c_13,plain,
    ( r1_orders_2(X0,sK6(X0,X1),sK5(X0,X1))
    | v12_waybel_0(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_623,plain,
    ( r1_orders_2(X0,sK6(X0,X1),sK5(X0,X1))
    | v12_waybel_0(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_624,plain,
    ( r1_orders_2(sK8,sK6(sK8,X0),sK5(sK8,X0))
    | v12_waybel_0(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_625,plain,
    ( r1_orders_2(sK8,sK6(sK8,X0),sK5(sK8,X0)) = iProver_top
    | v12_waybel_0(X0,sK8) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_627,plain,
    ( r1_orders_2(sK8,sK6(sK8,sK9),sK5(sK8,sK9)) = iProver_top
    | v12_waybel_0(sK9,sK8) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_7,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ sP0(X3,X0,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4621,plain,
    ( ~ r1_orders_2(X0,X1,sK5(sK8,X2))
    | ~ sP0(X2,X0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(sK5(sK8,X2),u1_struct_0(X0))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(sK5(sK8,X2),X2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4903,plain,
    ( ~ r1_orders_2(sK8,sK6(sK8,X0),sK5(sK8,X1))
    | ~ sP0(X1,sK8,X2)
    | ~ m1_subset_1(sK5(sK8,X1),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
    | ~ r2_hidden(sK5(sK8,X1),X1)
    | r2_hidden(sK6(sK8,X0),X2) ),
    inference(instantiation,[status(thm)],[c_4621])).

cnf(c_5119,plain,
    ( ~ r1_orders_2(sK8,sK6(sK8,X0),sK5(sK8,X1))
    | ~ sP0(X1,sK8,k3_waybel_0(sK8,X1))
    | ~ m1_subset_1(sK5(sK8,X1),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8))
    | ~ r2_hidden(sK5(sK8,X1),X1)
    | r2_hidden(sK6(sK8,X0),k3_waybel_0(sK8,X1)) ),
    inference(instantiation,[status(thm)],[c_4903])).

cnf(c_5120,plain,
    ( r1_orders_2(sK8,sK6(sK8,X0),sK5(sK8,X1)) != iProver_top
    | sP0(X1,sK8,k3_waybel_0(sK8,X1)) != iProver_top
    | m1_subset_1(sK5(sK8,X1),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK5(sK8,X1),X1) != iProver_top
    | r2_hidden(sK6(sK8,X0),k3_waybel_0(sK8,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5119])).

cnf(c_5122,plain,
    ( r1_orders_2(sK8,sK6(sK8,sK9),sK5(sK8,sK9)) != iProver_top
    | sP0(sK9,sK8,k3_waybel_0(sK8,sK9)) != iProver_top
    | m1_subset_1(sK5(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK5(sK8,sK9),sK9) != iProver_top
    | r2_hidden(sK6(sK8,sK9),k3_waybel_0(sK8,sK9)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5120])).

cnf(c_6329,plain,
    ( ~ r1_tarski(k3_waybel_0(sK8,X0),X1)
    | r2_hidden(sK6(sK8,X2),X1)
    | ~ r2_hidden(sK6(sK8,X2),k3_waybel_0(sK8,X0)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_6330,plain,
    ( r1_tarski(k3_waybel_0(sK8,X0),X1) != iProver_top
    | r2_hidden(sK6(sK8,X2),X1) = iProver_top
    | r2_hidden(sK6(sK8,X2),k3_waybel_0(sK8,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6329])).

cnf(c_6332,plain,
    ( r1_tarski(k3_waybel_0(sK8,sK9),sK9) != iProver_top
    | r2_hidden(sK6(sK8,sK9),k3_waybel_0(sK8,sK9)) != iProver_top
    | r2_hidden(sK6(sK8,sK9),sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6330])).

cnf(c_6412,plain,
    ( v12_waybel_0(sK9,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4879,c_28,c_29,c_500,c_542,c_557,c_572,c_587,c_627,c_5122,c_6332])).

cnf(c_7094,plain,
    ( r2_hidden(X0,k3_waybel_0(sK8,sK9)) != iProver_top
    | r2_hidden(X0,sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6242,c_28,c_29,c_500,c_542,c_557,c_572,c_587,c_627,c_5122,c_6332])).

cnf(c_7105,plain,
    ( r1_tarski(k3_waybel_0(sK8,sK9),X0) = iProver_top
    | r2_hidden(sK7(k3_waybel_0(sK8,sK9),X0),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_4238,c_7094])).

cnf(c_7184,plain,
    ( r1_tarski(k3_waybel_0(sK8,sK9),sK9) = iProver_top
    | r2_hidden(sK7(k3_waybel_0(sK8,sK9),sK9),sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7105])).

cnf(c_18,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK7(X0,X1),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tarski(k3_waybel_0(sK8,sK9),sK9)
    | ~ v12_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_208,plain,
    ( ~ v12_waybel_0(sK9,sK8)
    | ~ r1_tarski(k3_waybel_0(sK8,sK9),sK9) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_209,plain,
    ( ~ r1_tarski(k3_waybel_0(sK8,sK9),sK9)
    | ~ v12_waybel_0(sK9,sK8) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_458,plain,
    ( ~ v12_waybel_0(sK9,sK8)
    | ~ r2_hidden(sK7(X0,X1),X1)
    | k3_waybel_0(sK8,sK9) != X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_209])).

cnf(c_459,plain,
    ( ~ v12_waybel_0(sK9,sK8)
    | ~ r2_hidden(sK7(k3_waybel_0(sK8,sK9),sK9),sK9) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_460,plain,
    ( v12_waybel_0(sK9,sK8) != iProver_top
    | r2_hidden(sK7(k3_waybel_0(sK8,sK9),sK9),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_30,plain,
    ( r1_tarski(k3_waybel_0(sK8,sK9),sK9) != iProver_top
    | v12_waybel_0(sK9,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7184,c_6412,c_460,c_30])).


%------------------------------------------------------------------------------
