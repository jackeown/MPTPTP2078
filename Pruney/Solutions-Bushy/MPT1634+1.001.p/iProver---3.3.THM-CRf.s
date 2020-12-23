%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1634+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:02 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  174 (1738 expanded)
%              Number of clauses        :  112 ( 524 expanded)
%              Number of leaves         :   17 ( 439 expanded)
%              Depth                    :   28
%              Number of atoms          :  810 (8534 expanded)
%              Number of equality atoms :  213 (1554 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1),X1)
          | ~ r2_hidden(sK7(X0,X1),X0) )
        & ( r2_hidden(sK7(X0,X1),X1)
          | r2_hidden(sK7(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK7(X0,X1),X1)
          | ~ r2_hidden(sK7(X0,X1),X0) )
        & ( r2_hidden(sK7(X0,X1),X1)
          | r2_hidden(sK7(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK7(X0,X1),X1)
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

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ( k3_waybel_0(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f18,plain,(
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

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f8,f19,f18])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ( ( k3_waybel_0(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k3_waybel_0(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( k3_waybel_0(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k3_waybel_0(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f21])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k3_waybel_0(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k3_waybel_0(X1,X2))
      | ~ sP1(k3_waybel_0(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_waybel_0(X0,X1) = a_2_0_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k3_waybel_0(X0,X1) = a_2_0_waybel_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_waybel_0(X0,X1) != a_2_0_waybel_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_waybel_0(X0,X1) != a_2_0_waybel_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k3_waybel_0(X0,X1) != a_2_0_waybel_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k3_waybel_0(X0,sK9) != a_2_0_waybel_0(X0,sK9)
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k3_waybel_0(X0,X1) != a_2_0_waybel_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k3_waybel_0(sK8,X1) != a_2_0_waybel_0(sK8,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) )
      & l1_orders_2(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k3_waybel_0(sK8,sK9) != a_2_0_waybel_0(sK8,sK9)
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & l1_orders_2(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f17,f39,f38])).

fof(f64,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f40])).

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
    inference(nnf_transformation,[],[f18])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X0)
          & r1_orders_2(X1,X6,X8)
          & m1_subset_1(X8,u1_struct_0(X1)) )
     => ( r2_hidden(sK4(X0,X1,X6),X0)
        & r1_orders_2(X1,X6,sK4(X0,X1,X6))
        & m1_subset_1(sK4(X0,X1,X6),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X0)
          & r1_orders_2(X1,X3,X5)
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r2_hidden(sK3(X0,X1,X2),X0)
        & r1_orders_2(X1,X3,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f28,f27,f26])).

fof(f45,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X0)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X1,X6,sK4(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r1_orders_2(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X2)
                  & r1_orders_2(X1,X5,X6)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f30])).

fof(f33,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK6(X0,X1,X2),X2)
        & r1_orders_2(X1,X5,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X2)
              & r1_orders_2(X1,X5,X6)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X2)
            & r1_orders_2(X1,sK5(X0,X1,X2),X6)
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK5(X0,X1,X2) = X0
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X2)
            & r1_orders_2(X1,sK5(X0,X1,X2),sK6(X0,X1,X2))
            & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
            & sK5(X0,X1,X2) = X0
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f31,f33,f32])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r1_orders_2(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_waybel_0(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r1_orders_2(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f59])).

fof(f63,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sK5(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    k3_waybel_0(sK8,sK9) != a_2_0_waybel_0(sK8,sK9) ),
    inference(cnf_transformation,[],[f40])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_waybel_0(X1,X2) = X0
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X1,sK5(X0,X1,X2),sK6(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X0)
      | ~ r1_orders_2(X1,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK7(X0,X1),X1)
      | ~ r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_20,plain,
    ( r2_hidden(sK7(X0,X1),X1)
    | r2_hidden(sK7(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3162,plain,
    ( X0 = X1
    | r2_hidden(sK7(X0,X1),X1) = iProver_top
    | r2_hidden(sK7(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1,plain,
    ( ~ sP1(k3_waybel_0(X0,X1),X0,X1)
    | sP0(X1,X0,k3_waybel_0(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_304,plain,
    ( sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_orders_2(X3)
    | X1 != X3
    | X0 != X4
    | k3_waybel_0(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_1])).

cnf(c_305,plain,
    ( sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k3_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ l1_orders_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_305,c_12])).

cnf(c_310,plain,
    ( sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_309])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_496,plain,
    ( sP0(X0,X1,k3_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_310,c_24])).

cnf(c_497,plain,
    ( sP0(X0,sK8,k3_waybel_0(sK8,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_3153,plain,
    ( sP0(X0,sK8,k3_waybel_0(sK8,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,X2)
    | r2_hidden(sK4(X0,X1,X3),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3166,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(sK4(X0,X1,X3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4719,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,k3_waybel_0(sK8,X0)) != iProver_top
    | r2_hidden(sK4(X0,sK8,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3153,c_3166])).

cnf(c_1343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(sK4(X4,X2,X1),X4)
    | X0 != X4
    | k3_waybel_0(sK8,X0) != X3
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_497])).

cnf(c_1344,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,k3_waybel_0(sK8,X0))
    | r2_hidden(sK4(X0,sK8,X1),X0) ),
    inference(unflattening,[status(thm)],[c_1343])).

cnf(c_1345,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,k3_waybel_0(sK8,X0)) != iProver_top
    | r2_hidden(sK4(X0,sK8,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1344])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(k3_waybel_0(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_3151,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(k3_waybel_0(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_21,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3161,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3728,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) = iProver_top
    | r2_hidden(X1,k3_waybel_0(sK8,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3151,c_3161])).

cnf(c_4945,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X1,k3_waybel_0(sK8,X0)) != iProver_top
    | r2_hidden(sK4(X0,sK8,X1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4719,c_1345,c_3728])).

cnf(c_9,plain,
    ( r1_orders_2(X0,X1,sK4(X2,X0,X1))
    | ~ sP0(X2,X0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3165,plain,
    ( r1_orders_2(X0,X1,sK4(X2,X0,X1)) = iProver_top
    | sP0(X2,X0,X3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5117,plain,
    ( r1_orders_2(sK8,X0,sK4(X1,sK8,X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,k3_waybel_0(sK8,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3153,c_3165])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3160,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,a_2_0_waybel_0(X0,X3))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_356,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,a_2_0_waybel_0(X0,X3))
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_357,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,a_2_0_waybel_0(sK8,X2))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_361,plain,
    ( r2_hidden(X0,a_2_0_waybel_0(sK8,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r1_orders_2(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_24])).

cnf(c_362,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,a_2_0_waybel_0(sK8,X2)) ),
    inference(renaming,[status(thm)],[c_361])).

cnf(c_379,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,a_2_0_waybel_0(sK8,X2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_362,c_21])).

cnf(c_3158,plain,
    ( r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,a_2_0_waybel_0(sK8,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_4593,plain,
    ( r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,a_2_0_waybel_0(sK8,sK9)) = iProver_top
    | r2_hidden(X1,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3160,c_3158])).

cnf(c_5255,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,a_2_0_waybel_0(sK8,sK9)) = iProver_top
    | r2_hidden(X1,k3_waybel_0(sK8,X0)) != iProver_top
    | r2_hidden(sK4(X0,sK8,X1),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5117,c_4593])).

cnf(c_5409,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X1,a_2_0_waybel_0(sK8,sK9)) = iProver_top
    | r2_hidden(X1,k3_waybel_0(sK8,X0)) != iProver_top
    | r2_hidden(sK4(X0,sK8,X1),sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5255,c_3728])).

cnf(c_5415,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X0,a_2_0_waybel_0(sK8,sK9)) = iProver_top
    | r2_hidden(X0,k3_waybel_0(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4945,c_5409])).

cnf(c_28,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7541,plain,
    ( r2_hidden(X0,a_2_0_waybel_0(sK8,sK9)) = iProver_top
    | r2_hidden(X0,k3_waybel_0(sK8,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5415,c_28])).

cnf(c_7550,plain,
    ( k3_waybel_0(sK8,sK9) = X0
    | r2_hidden(sK7(X0,k3_waybel_0(sK8,sK9)),X0) = iProver_top
    | r2_hidden(sK7(X0,k3_waybel_0(sK8,sK9)),a_2_0_waybel_0(sK8,sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3162,c_7541])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_waybel_0(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | sK5(X2,X1,X0) = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_waybel_0(X1,X0))
    | ~ l1_orders_2(X1)
    | sK5(X2,X1,X0) = X2
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X1,a_2_0_waybel_0(sK8,X0))
    | ~ l1_orders_2(sK8)
    | sK5(X1,sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_412,plain,
    ( ~ r2_hidden(X1,a_2_0_waybel_0(sK8,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | sK5(X1,sK8,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_24])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X1,a_2_0_waybel_0(sK8,X0))
    | sK5(X1,sK8,X0) = X1 ),
    inference(renaming,[status(thm)],[c_412])).

cnf(c_3156,plain,
    ( sK5(X0,sK8,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X0,a_2_0_waybel_0(sK8,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_3527,plain,
    ( sK5(X0,sK8,sK9) = X0
    | r2_hidden(X0,a_2_0_waybel_0(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3160,c_3156])).

cnf(c_8621,plain,
    ( sK5(sK7(X0,k3_waybel_0(sK8,sK9)),sK8,sK9) = sK7(X0,k3_waybel_0(sK8,sK9))
    | k3_waybel_0(sK8,sK9) = X0
    | r2_hidden(sK7(X0,k3_waybel_0(sK8,sK9)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7550,c_3527])).

cnf(c_10205,plain,
    ( sK5(sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9)),sK8,sK9) = sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9))
    | a_2_0_waybel_0(sK8,sK9) = k3_waybel_0(sK8,sK9) ),
    inference(superposition,[status(thm)],[c_8621,c_3527])).

cnf(c_22,negated_conjecture,
    ( k3_waybel_0(sK8,sK9) != a_2_0_waybel_0(sK8,sK9) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3213,plain,
    ( m1_subset_1(k3_waybel_0(sK8,sK9),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_3226,plain,
    ( sP0(sK9,sK8,k3_waybel_0(sK8,sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_0,plain,
    ( ~ sP1(X0,X1,X2)
    | ~ sP0(X2,X1,X0)
    | k3_waybel_0(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_284,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | k3_waybel_0(X1,X0) = X2 ),
    inference(resolution,[status(thm)],[c_11,c_0])).

cnf(c_508,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_waybel_0(X1,X0) = X2
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_284,c_24])).

cnf(c_509,plain,
    ( ~ sP0(X0,sK8,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | k3_waybel_0(sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_3297,plain,
    ( ~ sP0(X0,sK8,k3_waybel_0(sK8,sK9))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(k3_waybel_0(sK8,sK9),k1_zfmisc_1(u1_struct_0(sK8)))
    | k3_waybel_0(sK8,X0) = k3_waybel_0(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_3585,plain,
    ( ~ sP0(sK9,sK8,k3_waybel_0(sK8,sK9))
    | ~ m1_subset_1(k3_waybel_0(sK8,sK9),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | k3_waybel_0(sK8,sK9) = k3_waybel_0(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_3297])).

cnf(c_2778,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3205,plain,
    ( a_2_0_waybel_0(sK8,sK9) != X0
    | k3_waybel_0(sK8,sK9) != X0
    | k3_waybel_0(sK8,sK9) = a_2_0_waybel_0(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_2778])).

cnf(c_3632,plain,
    ( a_2_0_waybel_0(sK8,sK9) != k3_waybel_0(sK8,sK9)
    | k3_waybel_0(sK8,sK9) = a_2_0_waybel_0(sK8,sK9)
    | k3_waybel_0(sK8,sK9) != k3_waybel_0(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_3205])).

cnf(c_3245,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X0,a_2_0_waybel_0(sK8,sK9))
    | sK5(X0,sK8,sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_4751,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9)),a_2_0_waybel_0(sK8,sK9))
    | sK5(sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9)),sK8,sK9) = sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_3245])).

cnf(c_4761,plain,
    ( sK5(sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9)),sK8,sK9) = sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9))
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9)),a_2_0_waybel_0(sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4751])).

cnf(c_8632,plain,
    ( a_2_0_waybel_0(sK8,sK9) = k3_waybel_0(sK8,sK9)
    | r2_hidden(sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9)),a_2_0_waybel_0(sK8,sK9)) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_7550])).

cnf(c_8634,plain,
    ( a_2_0_waybel_0(sK8,sK9) = k3_waybel_0(sK8,sK9)
    | r2_hidden(sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9)),a_2_0_waybel_0(sK8,sK9)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8632])).

cnf(c_10268,plain,
    ( sK5(sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9)),sK8,sK9) = sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10205,c_23,c_28,c_22,c_3213,c_3226,c_3585,c_3632,c_4761,c_8634])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_waybel_0(X1,X0))
    | r2_hidden(sK6(X2,X1,X0),X0)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_449,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_0_waybel_0(X1,X0))
    | r2_hidden(sK6(X2,X1,X0),X0)
    | ~ l1_orders_2(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X1,a_2_0_waybel_0(sK8,X0))
    | r2_hidden(sK6(X1,sK8,X0),X0)
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_454,plain,
    ( r2_hidden(sK6(X1,sK8,X0),X0)
    | ~ r2_hidden(X1,a_2_0_waybel_0(sK8,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_24])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X1,a_2_0_waybel_0(sK8,X0))
    | r2_hidden(sK6(X1,sK8,X0),X0) ),
    inference(renaming,[status(thm)],[c_454])).

cnf(c_3154,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X1,a_2_0_waybel_0(sK8,X0)) != iProver_top
    | r2_hidden(sK6(X1,sK8,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_15,plain,
    ( r1_orders_2(X0,sK5(X1,X0,X2),sK6(X1,X0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,a_2_0_waybel_0(X0,X2))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_335,plain,
    ( r1_orders_2(X0,sK5(X1,X0,X2),sK6(X1,X0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,a_2_0_waybel_0(X0,X2))
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_336,plain,
    ( r1_orders_2(sK8,sK5(X0,sK8,X1),sK6(X0,sK8,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X0,a_2_0_waybel_0(sK8,X1))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_340,plain,
    ( ~ r2_hidden(X0,a_2_0_waybel_0(sK8,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | r1_orders_2(sK8,sK5(X0,sK8,X1),sK6(X0,sK8,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_336,c_24])).

cnf(c_341,plain,
    ( r1_orders_2(sK8,sK5(X0,sK8,X1),sK6(X0,sK8,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X0,a_2_0_waybel_0(sK8,X1)) ),
    inference(renaming,[status(thm)],[c_340])).

cnf(c_3159,plain,
    ( r1_orders_2(sK8,sK5(X0,sK8,X1),sK6(X0,sK8,X1)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X0,a_2_0_waybel_0(sK8,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_341])).

cnf(c_7,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ sP0(X3,X0,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3167,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | sP0(X3,X0,X4) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(X1,X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5171,plain,
    ( sP0(X0,sK8,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(sK5(X3,sK8,X2),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK6(X3,sK8,X2),u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X3,a_2_0_waybel_0(sK8,X2)) != iProver_top
    | r2_hidden(sK5(X3,sK8,X2),X1) = iProver_top
    | r2_hidden(sK6(X3,sK8,X2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3159,c_3167])).

cnf(c_702,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r2_hidden(X4,X0)
    | r2_hidden(X5,X2)
    | ~ r2_hidden(X6,a_2_0_waybel_0(sK8,X3))
    | sK5(X6,sK8,X3) != X5
    | sK6(X6,sK8,X3) != X4
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_341])).

cnf(c_703,plain,
    ( ~ sP0(X0,sK8,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(sK5(X3,sK8,X2),u1_struct_0(sK8))
    | ~ m1_subset_1(sK6(X3,sK8,X2),u1_struct_0(sK8))
    | ~ r2_hidden(X3,a_2_0_waybel_0(sK8,X2))
    | r2_hidden(sK5(X3,sK8,X2),X1)
    | ~ r2_hidden(sK6(X3,sK8,X2),X0) ),
    inference(unflattening,[status(thm)],[c_702])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK6(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_waybel_0(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK6(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_waybel_0(X1,X0))
    | ~ l1_orders_2(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(sK6(X1,sK8,X0),u1_struct_0(sK8))
    | ~ r2_hidden(X1,a_2_0_waybel_0(sK8,X0))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_433,plain,
    ( ~ r2_hidden(X1,a_2_0_waybel_0(sK8,X0))
    | m1_subset_1(sK6(X1,sK8,X0),u1_struct_0(sK8))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_24])).

cnf(c_434,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(sK6(X1,sK8,X0),u1_struct_0(sK8))
    | ~ r2_hidden(X1,a_2_0_waybel_0(sK8,X0)) ),
    inference(renaming,[status(thm)],[c_433])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK5(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_waybel_0(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK5(X2,X1,X0),u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_0_waybel_0(X1,X0))
    | ~ l1_orders_2(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(sK5(X1,sK8,X0),u1_struct_0(sK8))
    | ~ r2_hidden(X1,a_2_0_waybel_0(sK8,X0))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_391,plain,
    ( ~ r2_hidden(X1,a_2_0_waybel_0(sK8,X0))
    | m1_subset_1(sK5(X1,sK8,X0),u1_struct_0(sK8))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_24])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(sK5(X1,sK8,X0),u1_struct_0(sK8))
    | ~ r2_hidden(X1,a_2_0_waybel_0(sK8,X0)) ),
    inference(renaming,[status(thm)],[c_391])).

cnf(c_721,plain,
    ( ~ sP0(X0,sK8,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X3,a_2_0_waybel_0(sK8,X2))
    | r2_hidden(sK5(X3,sK8,X2),X1)
    | ~ r2_hidden(sK6(X3,sK8,X2),X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_703,c_434,c_392])).

cnf(c_727,plain,
    ( sP0(X0,sK8,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X3,a_2_0_waybel_0(sK8,X2)) != iProver_top
    | r2_hidden(sK5(X3,sK8,X2),X1) = iProver_top
    | r2_hidden(sK6(X3,sK8,X2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_6065,plain,
    ( sP0(X0,sK8,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X3,a_2_0_waybel_0(sK8,X2)) != iProver_top
    | r2_hidden(sK5(X3,sK8,X2),X1) = iProver_top
    | r2_hidden(sK6(X3,sK8,X2),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5171,c_727])).

cnf(c_6069,plain,
    ( sP0(X0,sK8,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X2,a_2_0_waybel_0(sK8,X0)) != iProver_top
    | r2_hidden(sK5(X2,sK8,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3154,c_6065])).

cnf(c_10271,plain,
    ( sP0(sK9,sK8,X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9)),X0) = iProver_top
    | r2_hidden(sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9)),a_2_0_waybel_0(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10268,c_6069])).

cnf(c_12924,plain,
    ( r2_hidden(sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9)),X0) = iProver_top
    | sP0(sK9,sK8,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10271,c_23,c_28,c_22,c_3213,c_3226,c_3585,c_3632,c_8634])).

cnf(c_12925,plain,
    ( sP0(sK9,sK8,X0) != iProver_top
    | r2_hidden(sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9)),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_12924])).

cnf(c_19,plain,
    ( ~ r2_hidden(sK7(X0,X1),X1)
    | ~ r2_hidden(sK7(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3163,plain,
    ( X0 = X1
    | r2_hidden(sK7(X0,X1),X1) != iProver_top
    | r2_hidden(sK7(X0,X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_12930,plain,
    ( a_2_0_waybel_0(sK8,sK9) = k3_waybel_0(sK8,sK9)
    | sP0(sK9,sK8,k3_waybel_0(sK8,sK9)) != iProver_top
    | r2_hidden(sK7(a_2_0_waybel_0(sK8,sK9),k3_waybel_0(sK8,sK9)),a_2_0_waybel_0(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12925,c_3163])).

cnf(c_3227,plain,
    ( sP0(sK9,sK8,k3_waybel_0(sK8,sK9)) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3226])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12930,c_8634,c_3632,c_3585,c_3227,c_3226,c_3213,c_22,c_28,c_23])).


%------------------------------------------------------------------------------
