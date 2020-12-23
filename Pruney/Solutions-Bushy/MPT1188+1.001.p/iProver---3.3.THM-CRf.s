%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1188+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:06 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  208 (1735 expanded)
%              Number of clauses        :  120 ( 403 expanded)
%              Number of leaves         :   22 ( 419 expanded)
%              Depth                    :   25
%              Number of atoms          :  852 (14500 expanded)
%              Number of equality atoms :  195 (2125 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r8_orders_1(u1_orders_2(X0),X1)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( X1 != X2
                 => r2_orders_2(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( r8_orders_1(u1_orders_2(X0),X1)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( X1 != X2
                   => r2_orders_2(X0,X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r8_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( r2_orders_2(X0,X2,X1)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r8_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( r2_orders_2(X0,X2,X1)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(X0,X2,X1)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r8_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X2] :
                ( r2_orders_2(X0,X2,X1)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | r8_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(X0,X2,X1)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r8_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X2] :
                ( r2_orders_2(X0,X2,X1)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | r8_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(X0,X2,X1)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r8_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X3] :
                ( r2_orders_2(X0,X3,X1)
                | X1 = X3
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | r8_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f53])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_orders_2(X0,X2,X1)
          & X1 != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,sK3,X1)
        & sK3 != X1
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(X0,X2,X1)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r8_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X3] :
                ( r2_orders_2(X0,X3,X1)
                | X1 = X3
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | r8_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ? [X2] :
              ( ~ r2_orders_2(X0,X2,sK2)
              & sK2 != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ r8_orders_1(u1_orders_2(X0),sK2) )
        & ( ! [X3] :
              ( r2_orders_2(X0,X3,sK2)
              | sK2 = X3
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | r8_orders_1(u1_orders_2(X0),sK2) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ~ r2_orders_2(X0,X2,X1)
                  & X1 != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r8_orders_1(u1_orders_2(X0),X1) )
            & ( ! [X3] :
                  ( r2_orders_2(X0,X3,X1)
                  | X1 = X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | r8_orders_1(u1_orders_2(X0),X1) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(sK1,X2,X1)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(sK1)) )
            | ~ r8_orders_1(u1_orders_2(sK1),X1) )
          & ( ! [X3] :
                ( r2_orders_2(sK1,X3,X1)
                | X1 = X3
                | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
            | r8_orders_1(u1_orders_2(sK1),X1) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ( ( ~ r2_orders_2(sK1,sK3,sK2)
        & sK2 != sK3
        & m1_subset_1(sK3,u1_struct_0(sK1)) )
      | ~ r8_orders_1(u1_orders_2(sK1),sK2) )
    & ( ! [X3] :
          ( r2_orders_2(sK1,X3,sK2)
          | sK2 = X3
          | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
      | r8_orders_1(u1_orders_2(sK1),sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f54,f57,f56,f55])).

fof(f87,plain,(
    ! [X3] :
      ( r2_orders_2(sK1,X3,sK2)
      | sK2 = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | r8_orders_1(u1_orders_2(sK1),sK2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f44])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f85,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f58])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r8_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( r2_hidden(X2,k3_relat_1(X0))
               => ( r2_hidden(k4_tarski(X2,X1),X0)
                  | X1 = X2 ) )
            & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X1),X0)
                | X1 = X2
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X1),X0)
                | X1 = X2
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_orders_1(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X2] :
                  ( r2_hidden(k4_tarski(X2,X1),X0)
                  | X1 = X2
                  | ~ r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r8_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_orders_1(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X2] :
                  ( r2_hidden(k4_tarski(X2,X1),X0)
                  | X1 = X2
                  | ~ r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r8_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_orders_1(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X3] :
                  ( r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r8_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK0(X0,X1),X1),X0)
        & sK0(X0,X1) != X1
        & r2_hidden(sK0(X0,X1),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_orders_1(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK0(X0,X1),X1),X0)
              & sK0(X0,X1) != X1
              & r2_hidden(sK0(X0,X1),k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X3] :
                  ( r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r8_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X1),X0)
      | X1 = X3
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ r8_orders_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,
    ( ~ r2_orders_2(sK1,sK3,sK2)
    | ~ r8_orders_1(u1_orders_2(sK1),sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,X1,X2)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f88,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r8_orders_1(u1_orders_2(sK1),sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f89,plain,
    ( sK2 != sK3
    | ~ r8_orders_1(u1_orders_2(sK1),sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v4_relat_2(X1)
        & v1_relat_2(X1) )
     => k3_relat_1(X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(flattening,[],[f37])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
       => v2_orders_2(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f59,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_orders_2(X0) )
     => v1_partfun1(u1_orders_2(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f73,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f83,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f84,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v2_orders_2(X0) )
     => v8_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f77,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v2_orders_2(X0) )
     => v4_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f76,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => v1_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f75,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r8_orders_1(X0,X1)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1),X1),X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r8_orders_1(X0,X1)
      | r2_hidden(sK0(X0,X1),k3_relat_1(X0))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r8_orders_1(X0,X1)
      | sK0(X0,X1) != X1
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_25,negated_conjecture,
    ( r2_orders_2(sK1,X0,sK2)
    | r8_orders_1(u1_orders_2(sK1),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | sK2 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_513,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_27])).

cnf(c_514,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_11,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_477,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_478,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_701,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_514,c_478])).

cnf(c_767,plain,
    ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK1))
    | r8_orders_1(u1_orders_2(sK1),sK2)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | X0 != X2
    | sK2 != X1
    | sK2 = X2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_701])).

cnf(c_768,plain,
    ( r2_hidden(k4_tarski(X0,sK2),u1_orders_2(sK1))
    | r8_orders_1(u1_orders_2(sK1),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK2 = X0 ),
    inference(unflattening,[status(thm)],[c_767])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_772,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r8_orders_1(u1_orders_2(sK1),sK2)
    | r2_hidden(k4_tarski(X0,sK2),u1_orders_2(sK1))
    | sK2 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_768,c_26])).

cnf(c_773,plain,
    ( r2_hidden(k4_tarski(X0,sK2),u1_orders_2(sK1))
    | r8_orders_1(u1_orders_2(sK1),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | sK2 = X0 ),
    inference(renaming,[status(thm)],[c_772])).

cnf(c_854,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X2,sK2),u1_orders_2(sK1))
    | r8_orders_1(u1_orders_2(sK1),sK2)
    | X2 != X0
    | u1_struct_0(sK1) != X1
    | sK2 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_773])).

cnf(c_855,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK1))
    | r2_hidden(k4_tarski(X0,sK2),u1_orders_2(sK1))
    | r8_orders_1(u1_orders_2(sK1),sK2)
    | sK2 = X0 ),
    inference(unflattening,[status(thm)],[c_854])).

cnf(c_3201,plain,
    ( ~ r2_hidden(X0_56,u1_struct_0(sK1))
    | r2_hidden(k4_tarski(X0_56,sK2),u1_orders_2(sK1))
    | r8_orders_1(u1_orders_2(sK1),sK2)
    | sK2 = X0_56 ),
    inference(subtyping,[status(esa)],[c_855])).

cnf(c_3558,plain,
    ( sK2 = X0_56
    | r2_hidden(X0_56,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(k4_tarski(X0_56,sK2),u1_orders_2(sK1)) = iProver_top
    | r8_orders_1(u1_orders_2(sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3201])).

cnf(c_3265,plain,
    ( sK2 = X0_56
    | r2_hidden(X0_56,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(k4_tarski(X0_56,sK2),u1_orders_2(sK1)) = iProver_top
    | r8_orders_1(u1_orders_2(sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3201])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ r8_orders_1(X1,X2)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3210,plain,
    ( ~ r2_hidden(X0_56,k3_relat_1(X1_56))
    | r2_hidden(k4_tarski(X0_56,X2_56),X1_56)
    | ~ r8_orders_1(X1_56,X2_56)
    | ~ v1_relat_1(X1_56)
    | X0_56 = X2_56 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3549,plain,
    ( X0_56 = X1_56
    | r2_hidden(X0_56,k3_relat_1(X2_56)) != iProver_top
    | r2_hidden(k4_tarski(X0_56,X1_56),X2_56) = iProver_top
    | r8_orders_1(X2_56,X1_56) != iProver_top
    | v1_relat_1(X2_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3210])).

cnf(c_22,negated_conjecture,
    ( ~ r2_orders_2(sK1,sK3,sK2)
    | ~ r8_orders_1(u1_orders_2(sK1),sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_495,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_496,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_2,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X1 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_543,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | X2 = X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_27])).

cnf(c_544,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r2_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_718,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_496,c_544])).

cnf(c_753,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK1))
    | ~ r8_orders_1(u1_orders_2(sK1),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | X1 = X0
    | sK2 != X1
    | sK3 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_718])).

cnf(c_754,plain,
    ( ~ r2_hidden(k4_tarski(sK3,sK2),u1_orders_2(sK1))
    | ~ r8_orders_1(u1_orders_2(sK1),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | sK2 = sK3 ),
    inference(unflattening,[status(thm)],[c_753])).

cnf(c_24,negated_conjecture,
    ( ~ r8_orders_1(u1_orders_2(sK1),sK2)
    | m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_23,negated_conjecture,
    ( ~ r8_orders_1(u1_orders_2(sK1),sK2)
    | sK2 != sK3 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_756,plain,
    ( ~ r8_orders_1(u1_orders_2(sK1),sK2)
    | ~ r2_hidden(k4_tarski(sK3,sK2),u1_orders_2(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_754,c_26,c_24,c_23])).

cnf(c_757,plain,
    ( ~ r2_hidden(k4_tarski(sK3,sK2),u1_orders_2(sK1))
    | ~ r8_orders_1(u1_orders_2(sK1),sK2) ),
    inference(renaming,[status(thm)],[c_756])).

cnf(c_3206,plain,
    ( ~ r2_hidden(k4_tarski(sK3,sK2),u1_orders_2(sK1))
    | ~ r8_orders_1(u1_orders_2(sK1),sK2) ),
    inference(subtyping,[status(esa)],[c_757])).

cnf(c_3552,plain,
    ( r2_hidden(k4_tarski(sK3,sK2),u1_orders_2(sK1)) != iProver_top
    | r8_orders_1(u1_orders_2(sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3206])).

cnf(c_4083,plain,
    ( sK2 = sK3
    | r2_hidden(sK3,k3_relat_1(u1_orders_2(sK1))) != iProver_top
    | r8_orders_1(u1_orders_2(sK1),sK2) != iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3549,c_3552])).

cnf(c_19,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v8_relat_2(X0)
    | ~ v4_relat_2(X0)
    | ~ v1_relat_2(X0)
    | k3_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_14,plain,
    ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_417,plain,
    ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_0,c_14])).

cnf(c_30,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_435,plain,
    ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_417,c_30])).

cnf(c_436,plain,
    ( v1_partfun1(u1_orders_2(sK1),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_66,plain,
    ( v1_partfun1(u1_orders_2(sK1),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_108,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | v2_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_438,plain,
    ( v1_partfun1(u1_orders_2(sK1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_30,c_27,c_66,c_108])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v8_relat_2(X0)
    | ~ v4_relat_2(X0)
    | ~ v1_relat_2(X0)
    | u1_orders_2(sK1) != X0
    | k3_relat_1(X0) = X1
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_438])).

cnf(c_462,plain,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v8_relat_2(u1_orders_2(sK1))
    | ~ v4_relat_2(u1_orders_2(sK1))
    | ~ v1_relat_2(u1_orders_2(sK1))
    | k3_relat_1(u1_orders_2(sK1)) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_29,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_28,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_18,plain,
    ( ~ v4_orders_2(X0)
    | v8_relat_2(u1_orders_2(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_orders_2(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_54,plain,
    ( ~ v4_orders_2(sK1)
    | v8_relat_2(u1_orders_2(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( ~ v5_orders_2(X0)
    | v4_relat_2(u1_orders_2(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_orders_2(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_57,plain,
    ( ~ v5_orders_2(sK1)
    | v4_relat_2(u1_orders_2(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( v1_relat_2(u1_orders_2(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_60,plain,
    ( v1_relat_2(u1_orders_2(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v3_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_13,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_69,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_464,plain,
    ( k3_relat_1(u1_orders_2(sK1)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_30,c_29,c_28,c_27,c_54,c_57,c_60,c_69,c_108])).

cnf(c_3207,plain,
    ( k3_relat_1(u1_orders_2(sK1)) = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_464])).

cnf(c_4089,plain,
    ( sK2 = sK3
    | r2_hidden(sK3,u1_struct_0(sK1)) != iProver_top
    | r8_orders_1(u1_orders_2(sK1),sK2) != iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4083,c_3207])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_15,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_363,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_364,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_63,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_12,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_72,plain,
    ( l1_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_366,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_364,c_31,c_27,c_63,c_72])).

cnf(c_376,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_366])).

cnf(c_377,plain,
    ( r2_hidden(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_876,plain,
    ( r2_hidden(X0,u1_struct_0(sK1))
    | ~ r8_orders_1(u1_orders_2(sK1),sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_377])).

cnf(c_877,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ r8_orders_1(u1_orders_2(sK1),sK2) ),
    inference(unflattening,[status(thm)],[c_876])).

cnf(c_878,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1)) = iProver_top
    | r8_orders_1(u1_orders_2(sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_877])).

cnf(c_3208,negated_conjecture,
    ( ~ r8_orders_1(u1_orders_2(sK1),sK2)
    | sK2 != sK3 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_3250,plain,
    ( sK2 != sK3
    | r8_orders_1(u1_orders_2(sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3208])).

cnf(c_3217,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_3702,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_3217])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_470,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_27])).

cnf(c_471,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_842,plain,
    ( v1_relat_1(X0)
    | u1_orders_2(sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(resolution_lifted,[status(thm)],[c_1,c_471])).

cnf(c_843,plain,
    ( v1_relat_1(u1_orders_2(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_842])).

cnf(c_3202,plain,
    ( v1_relat_1(u1_orders_2(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)) ),
    inference(subtyping,[status(esa)],[c_843])).

cnf(c_3703,plain,
    ( v1_relat_1(u1_orders_2(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_3202])).

cnf(c_3704,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | v1_relat_1(u1_orders_2(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3703])).

cnf(c_4185,plain,
    ( r8_orders_1(u1_orders_2(sK1),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4089,c_878,c_3250,c_3702,c_3704])).

cnf(c_4191,plain,
    ( r2_hidden(k4_tarski(X0_56,sK2),u1_orders_2(sK1)) = iProver_top
    | r2_hidden(X0_56,u1_struct_0(sK1)) != iProver_top
    | sK2 = X0_56 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3558,c_878,c_3250,c_3265,c_3702,c_3704,c_4089])).

cnf(c_4192,plain,
    ( sK2 = X0_56
    | r2_hidden(X0_56,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(k4_tarski(X0_56,sK2),u1_orders_2(sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4191])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(sK0(X1,X0),X0),X1)
    | r8_orders_1(X1,X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3213,plain,
    ( ~ r2_hidden(X0_56,k3_relat_1(X1_56))
    | ~ r2_hidden(k4_tarski(sK0(X1_56,X0_56),X0_56),X1_56)
    | r8_orders_1(X1_56,X0_56)
    | ~ v1_relat_1(X1_56) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3546,plain,
    ( r2_hidden(X0_56,k3_relat_1(X1_56)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X1_56,X0_56),X0_56),X1_56) != iProver_top
    | r8_orders_1(X1_56,X0_56) = iProver_top
    | v1_relat_1(X1_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3213])).

cnf(c_4199,plain,
    ( sK0(u1_orders_2(sK1),sK2) = sK2
    | r2_hidden(sK0(u1_orders_2(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,k3_relat_1(u1_orders_2(sK1))) != iProver_top
    | r8_orders_1(u1_orders_2(sK1),sK2) = iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4192,c_3546])).

cnf(c_4205,plain,
    ( sK0(u1_orders_2(sK1),sK2) = sK2
    | r2_hidden(sK0(u1_orders_2(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,u1_struct_0(sK1)) != iProver_top
    | r8_orders_1(u1_orders_2(sK1),sK2) = iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4199,c_3207])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(sK0(X1,X0),k3_relat_1(X1))
    | r8_orders_1(X1,X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3211,plain,
    ( ~ r2_hidden(X0_56,k3_relat_1(X1_56))
    | r2_hidden(sK0(X1_56,X0_56),k3_relat_1(X1_56))
    | r8_orders_1(X1_56,X0_56)
    | ~ v1_relat_1(X1_56) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3548,plain,
    ( r2_hidden(X0_56,k3_relat_1(X1_56)) != iProver_top
    | r2_hidden(sK0(X1_56,X0_56),k3_relat_1(X1_56)) = iProver_top
    | r8_orders_1(X1_56,X0_56) = iProver_top
    | v1_relat_1(X1_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3211])).

cnf(c_4027,plain,
    ( r2_hidden(X0_56,k3_relat_1(u1_orders_2(sK1))) != iProver_top
    | r2_hidden(sK0(u1_orders_2(sK1),X0_56),u1_struct_0(sK1)) = iProver_top
    | r8_orders_1(u1_orders_2(sK1),X0_56) = iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3207,c_3548])).

cnf(c_4028,plain,
    ( r2_hidden(X0_56,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(u1_orders_2(sK1),X0_56),u1_struct_0(sK1)) = iProver_top
    | r8_orders_1(u1_orders_2(sK1),X0_56) = iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4027,c_3207])).

cnf(c_4030,plain,
    ( r2_hidden(sK0(u1_orders_2(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | r2_hidden(sK2,u1_struct_0(sK1)) != iProver_top
    | r8_orders_1(u1_orders_2(sK1),sK2) = iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4028])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r8_orders_1(X1,X0)
    | ~ v1_relat_1(X1)
    | sK0(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3212,plain,
    ( ~ r2_hidden(X0_56,k3_relat_1(X1_56))
    | r8_orders_1(X1_56,X0_56)
    | ~ v1_relat_1(X1_56)
    | sK0(X1_56,X0_56) != X0_56 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3776,plain,
    ( ~ r2_hidden(X0_56,k3_relat_1(u1_orders_2(sK1)))
    | r8_orders_1(u1_orders_2(sK1),X0_56)
    | ~ v1_relat_1(u1_orders_2(sK1))
    | sK0(u1_orders_2(sK1),X0_56) != X0_56 ),
    inference(instantiation,[status(thm)],[c_3212])).

cnf(c_3787,plain,
    ( sK0(u1_orders_2(sK1),X0_56) != X0_56
    | r2_hidden(X0_56,k3_relat_1(u1_orders_2(sK1))) != iProver_top
    | r8_orders_1(u1_orders_2(sK1),X0_56) = iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3776])).

cnf(c_3789,plain,
    ( sK0(u1_orders_2(sK1),sK2) != sK2
    | r2_hidden(sK2,k3_relat_1(u1_orders_2(sK1))) != iProver_top
    | r8_orders_1(u1_orders_2(sK1),sK2) = iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3787])).

cnf(c_3225,plain,
    ( ~ r2_hidden(X0_56,X1_56)
    | r2_hidden(X2_56,X3_56)
    | X2_56 != X0_56
    | X3_56 != X1_56 ),
    theory(equality)).

cnf(c_3719,plain,
    ( r2_hidden(X0_56,X1_56)
    | ~ r2_hidden(sK2,u1_struct_0(sK1))
    | X1_56 != u1_struct_0(sK1)
    | X0_56 != sK2 ),
    inference(instantiation,[status(thm)],[c_3225])).

cnf(c_3745,plain,
    ( r2_hidden(X0_56,k3_relat_1(u1_orders_2(sK1)))
    | ~ r2_hidden(sK2,u1_struct_0(sK1))
    | X0_56 != sK2
    | k3_relat_1(u1_orders_2(sK1)) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3719])).

cnf(c_3746,plain,
    ( X0_56 != sK2
    | k3_relat_1(u1_orders_2(sK1)) != u1_struct_0(sK1)
    | r2_hidden(X0_56,k3_relat_1(u1_orders_2(sK1))) = iProver_top
    | r2_hidden(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3745])).

cnf(c_3748,plain,
    ( k3_relat_1(u1_orders_2(sK1)) != u1_struct_0(sK1)
    | sK2 != sK2
    | r2_hidden(sK2,k3_relat_1(u1_orders_2(sK1))) = iProver_top
    | r2_hidden(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3746])).

cnf(c_3235,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3217])).

cnf(c_888,plain,
    ( r2_hidden(X0,u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_377,c_26])).

cnf(c_889,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_888])).

cnf(c_890,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_889])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4205,c_4185,c_4030,c_3789,c_3748,c_3704,c_3702,c_3207,c_3235,c_890])).


%------------------------------------------------------------------------------
