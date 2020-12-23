%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1187+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  215 (1788 expanded)
%              Number of clauses        :  127 ( 425 expanded)
%              Number of leaves         :   23 ( 433 expanded)
%              Depth                    :   25
%              Number of atoms          :  850 (13112 expanded)
%              Number of equality atoms :  182 ( 414 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r6_orders_1(X0,X1)
        <=> ( ! [X2] :
                ~ ( r2_hidden(k4_tarski(X1,X2),X0)
                  & X1 != X2
                  & r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r6_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                | X1 = X2
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_orders_1(X0,X1)
            | ? [X2] :
                ( r2_hidden(k4_tarski(X1,X2),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X2] :
                  ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                  | X1 = X2
                  | ~ r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r6_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_orders_1(X0,X1)
            | ? [X2] :
                ( r2_hidden(k4_tarski(X1,X2),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X2] :
                  ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                  | X1 = X2
                  | ~ r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r6_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_orders_1(X0,X1)
            | ? [X2] :
                ( r2_hidden(k4_tarski(X1,X2),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X3] :
                  ( ~ r2_hidden(k4_tarski(X1,X3),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r6_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0)) )
     => ( r2_hidden(k4_tarski(X1,sK0(X0,X1)),X0)
        & sK0(X0,X1) != X1
        & r2_hidden(sK0(X0,X1),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_orders_1(X0,X1)
            | ( r2_hidden(k4_tarski(X1,sK0(X0,X1)),X0)
              & sK0(X0,X1) != X1
              & r2_hidden(sK0(X0,X1),k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X3] :
                  ( ~ r2_hidden(k4_tarski(X1,X3),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r6_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r6_orders_1(X0,X1)
      | r2_hidden(k4_tarski(X1,sK0(X0,X1)),X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r6_orders_1(u1_orders_2(X0),X1)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ r2_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( r6_orders_1(u1_orders_2(X0),X1)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ r2_orders_2(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r6_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r6_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r2_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r6_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | r6_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r2_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r6_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | r6_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r2_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r6_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X3] :
                ( ~ r2_orders_2(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | r6_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f52])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_orders_2(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r2_orders_2(X0,X1,sK3)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r2_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r6_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X3] :
                ( ~ r2_orders_2(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | r6_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ? [X2] :
              ( r2_orders_2(X0,sK2,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ r6_orders_1(u1_orders_2(X0),sK2) )
        & ( ! [X3] :
              ( ~ r2_orders_2(X0,sK2,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | r6_orders_1(u1_orders_2(X0),sK2) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r6_orders_1(u1_orders_2(X0),X1) )
            & ( ! [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | r6_orders_1(u1_orders_2(X0),X1) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( r2_orders_2(sK1,X1,X2)
                & m1_subset_1(X2,u1_struct_0(sK1)) )
            | ~ r6_orders_1(u1_orders_2(sK1),X1) )
          & ( ! [X3] :
                ( ~ r2_orders_2(sK1,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
            | r6_orders_1(u1_orders_2(sK1),X1) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ( r2_orders_2(sK1,sK2,sK3)
        & m1_subset_1(sK3,u1_struct_0(sK1)) )
      | ~ r6_orders_1(u1_orders_2(sK1),sK2) )
    & ( ! [X3] :
          ( ~ r2_orders_2(sK1,sK2,X3)
          | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
      | r6_orders_1(u1_orders_2(sK1),sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f53,f56,f55,f54])).

fof(f86,plain,(
    ! [X3] :
      ( ~ r2_orders_2(sK1,sK2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | r6_orders_1(u1_orders_2(sK1),sK2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f57])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f43,plain,(
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
    inference(flattening,[],[f43])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,X1,X2)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,
    ( r2_orders_2(sK1,sK2,sK3)
    | ~ r6_orders_1(u1_orders_2(sK1),sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r6_orders_1(u1_orders_2(sK1),sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X3),X0)
      | X1 = X3
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ r6_orders_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v4_relat_2(X1)
        & v1_relat_2(X1) )
     => k3_relat_1(X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(flattening,[],[f36])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
       => v2_orders_2(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f72,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f82,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f83,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v2_orders_2(X0) )
     => v8_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f76,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v2_orders_2(X0) )
     => v4_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f75,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => v1_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f74,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r6_orders_1(X0,X1)
      | r2_hidden(sK0(X0,X1),k3_relat_1(X0))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r6_orders_1(X0,X1)
      | sK0(X0,X1) != X1
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK0(X1,X0)),X1)
    | r6_orders_1(X1,X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3218,plain,
    ( ~ r2_hidden(X0_56,k3_relat_1(X1_56))
    | r2_hidden(k4_tarski(X0_56,sK0(X1_56,X0_56)),X1_56)
    | r6_orders_1(X1_56,X0_56)
    | ~ v1_relat_1(X1_56) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3551,plain,
    ( r2_hidden(X0_56,k3_relat_1(X1_56)) != iProver_top
    | r2_hidden(k4_tarski(X0_56,sK0(X1_56,X0_56)),X1_56) = iProver_top
    | r6_orders_1(X1_56,X0_56) = iProver_top
    | v1_relat_1(X1_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3218])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_24,negated_conjecture,
    ( ~ r2_orders_2(sK1,sK2,X0)
    | r6_orders_1(u1_orders_2(sK1),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_26,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_485,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_486,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_2,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X1 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_533,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | X2 = X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_26])).

cnf(c_534,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r2_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_708,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_486,c_534])).

cnf(c_771,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK1))
    | r6_orders_1(u1_orders_2(sK1),sK2)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | X1 != X2
    | X1 = X0
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_708])).

cnf(c_772,plain,
    ( ~ r2_hidden(k4_tarski(sK2,X0),u1_orders_2(sK1))
    | r6_orders_1(u1_orders_2(sK1),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | X0 = sK2 ),
    inference(unflattening,[status(thm)],[c_771])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_776,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r6_orders_1(u1_orders_2(sK1),sK2)
    | ~ r2_hidden(k4_tarski(sK2,X0),u1_orders_2(sK1))
    | X0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_772,c_25])).

cnf(c_777,plain,
    ( ~ r2_hidden(k4_tarski(sK2,X0),u1_orders_2(sK1))
    | r6_orders_1(u1_orders_2(sK1),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | X0 = sK2 ),
    inference(renaming,[status(thm)],[c_776])).

cnf(c_859,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(sK2,X2),u1_orders_2(sK1))
    | r6_orders_1(u1_orders_2(sK1),sK2)
    | X2 != X0
    | u1_struct_0(sK1) != X1
    | sK2 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_777])).

cnf(c_860,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK1))
    | ~ r2_hidden(k4_tarski(sK2,X0),u1_orders_2(sK1))
    | r6_orders_1(u1_orders_2(sK1),sK2)
    | sK2 = X0 ),
    inference(unflattening,[status(thm)],[c_859])).

cnf(c_3206,plain,
    ( ~ r2_hidden(X0_56,u1_struct_0(sK1))
    | ~ r2_hidden(k4_tarski(sK2,X0_56),u1_orders_2(sK1))
    | r6_orders_1(u1_orders_2(sK1),sK2)
    | sK2 = X0_56 ),
    inference(subtyping,[status(esa)],[c_860])).

cnf(c_3563,plain,
    ( sK2 = X0_56
    | r2_hidden(X0_56,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(k4_tarski(sK2,X0_56),u1_orders_2(sK1)) != iProver_top
    | r6_orders_1(u1_orders_2(sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3206])).

cnf(c_3270,plain,
    ( sK2 = X0_56
    | r2_hidden(X0_56,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(k4_tarski(sK2,X0_56),u1_orders_2(sK1)) != iProver_top
    | r6_orders_1(u1_orders_2(sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3206])).

cnf(c_22,negated_conjecture,
    ( r2_orders_2(sK1,sK2,sK3)
    | ~ r6_orders_1(u1_orders_2(sK1),sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_503,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_26])).

cnf(c_504,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_11,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_467,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_468,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_691,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_504,c_468])).

cnf(c_743,plain,
    ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK1))
    | ~ r6_orders_1(u1_orders_2(sK1),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | sK3 != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_691])).

cnf(c_744,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1))
    | ~ r6_orders_1(u1_orders_2(sK1),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_743])).

cnf(c_23,negated_conjecture,
    ( ~ r6_orders_1(u1_orders_2(sK1),sK2)
    | m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_746,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1))
    | ~ r6_orders_1(u1_orders_2(sK1),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_744,c_25,c_23])).

cnf(c_3212,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1))
    | ~ r6_orders_1(u1_orders_2(sK1),sK2) ),
    inference(subtyping,[status(esa)],[c_746])).

cnf(c_3556,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1)) = iProver_top
    | r6_orders_1(u1_orders_2(sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3212])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ r6_orders_1(X1,X2)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3215,plain,
    ( ~ r2_hidden(X0_56,k3_relat_1(X1_56))
    | ~ r2_hidden(k4_tarski(X2_56,X0_56),X1_56)
    | ~ r6_orders_1(X1_56,X2_56)
    | ~ v1_relat_1(X1_56)
    | X0_56 = X2_56 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3554,plain,
    ( X0_56 = X1_56
    | r2_hidden(X0_56,k3_relat_1(X2_56)) != iProver_top
    | r2_hidden(k4_tarski(X1_56,X0_56),X2_56) != iProver_top
    | r6_orders_1(X2_56,X1_56) != iProver_top
    | v1_relat_1(X2_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3215])).

cnf(c_4071,plain,
    ( sK3 = sK2
    | r2_hidden(sK3,k3_relat_1(u1_orders_2(sK1))) != iProver_top
    | r6_orders_1(u1_orders_2(sK1),sK2) != iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3556,c_3554])).

cnf(c_19,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v8_relat_2(X0)
    | ~ v4_relat_2(X0)
    | ~ v1_relat_2(X0)
    | k3_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_14,plain,
    ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_407,plain,
    ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_0,c_14])).

cnf(c_29,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_425,plain,
    ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_407,c_29])).

cnf(c_426,plain,
    ( v1_partfun1(u1_orders_2(sK1),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_64,plain,
    ( v1_partfun1(u1_orders_2(sK1),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_106,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | v2_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_428,plain,
    ( v1_partfun1(u1_orders_2(sK1),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_426,c_29,c_26,c_64,c_106])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v8_relat_2(X0)
    | ~ v4_relat_2(X0)
    | ~ v1_relat_2(X0)
    | u1_orders_2(sK1) != X0
    | k3_relat_1(X0) = X1
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_428])).

cnf(c_452,plain,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v8_relat_2(u1_orders_2(sK1))
    | ~ v4_relat_2(u1_orders_2(sK1))
    | ~ v1_relat_2(u1_orders_2(sK1))
    | k3_relat_1(u1_orders_2(sK1)) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_28,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_27,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_18,plain,
    ( ~ v4_orders_2(X0)
    | v8_relat_2(u1_orders_2(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_orders_2(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_52,plain,
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
    inference(cnf_transformation,[],[f75])).

cnf(c_55,plain,
    ( ~ v5_orders_2(sK1)
    | v4_relat_2(u1_orders_2(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( v1_relat_2(u1_orders_2(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_58,plain,
    ( v1_relat_2(u1_orders_2(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v3_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_13,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_67,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_454,plain,
    ( k3_relat_1(u1_orders_2(sK1)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_29,c_28,c_27,c_26,c_52,c_55,c_58,c_67,c_106])).

cnf(c_3213,plain,
    ( k3_relat_1(u1_orders_2(sK1)) = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_454])).

cnf(c_4090,plain,
    ( sK3 = sK2
    | r2_hidden(sK3,u1_struct_0(sK1)) != iProver_top
    | r6_orders_1(u1_orders_2(sK1),sK2) != iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4071,c_3213])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_15,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_353,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_30])).

cnf(c_354,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_61,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_12,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_70,plain,
    ( l1_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_356,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_30,c_26,c_61,c_70])).

cnf(c_366,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_356])).

cnf(c_367,plain,
    ( r2_hidden(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_881,plain,
    ( r2_hidden(X0,u1_struct_0(sK1))
    | ~ r6_orders_1(u1_orders_2(sK1),sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_367])).

cnf(c_882,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ r6_orders_1(u1_orders_2(sK1),sK2) ),
    inference(unflattening,[status(thm)],[c_881])).

cnf(c_883,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1)) = iProver_top
    | r6_orders_1(u1_orders_2(sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_882])).

cnf(c_3222,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_3240,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3222])).

cnf(c_3,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_521,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_26])).

cnf(c_522,plain,
    ( ~ r2_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_757,plain,
    ( ~ r6_orders_1(u1_orders_2(sK1),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | sK3 != X0
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_522])).

cnf(c_758,plain,
    ( ~ r6_orders_1(u1_orders_2(sK1),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | sK2 != sK3 ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_760,plain,
    ( ~ r6_orders_1(u1_orders_2(sK1),sK2)
    | sK2 != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_758,c_23])).

cnf(c_3211,plain,
    ( ~ r6_orders_1(u1_orders_2(sK1),sK2)
    | sK2 != sK3 ),
    inference(subtyping,[status(esa)],[c_760])).

cnf(c_3256,plain,
    ( sK2 != sK3
    | r6_orders_1(u1_orders_2(sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3211])).

cnf(c_3706,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_3222])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_460,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_461,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_847,plain,
    ( v1_relat_1(X0)
    | u1_orders_2(sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(resolution_lifted,[status(thm)],[c_1,c_461])).

cnf(c_848,plain,
    ( v1_relat_1(u1_orders_2(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_847])).

cnf(c_3207,plain,
    ( v1_relat_1(u1_orders_2(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)) ),
    inference(subtyping,[status(esa)],[c_848])).

cnf(c_3707,plain,
    ( v1_relat_1(u1_orders_2(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_3207])).

cnf(c_3708,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | v1_relat_1(u1_orders_2(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3707])).

cnf(c_3224,plain,
    ( X0_56 != X1_56
    | X2_56 != X1_56
    | X2_56 = X0_56 ),
    theory(equality)).

cnf(c_3855,plain,
    ( sK3 != X0_56
    | sK2 != X0_56
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_3224])).

cnf(c_3856,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3855])).

cnf(c_4200,plain,
    ( r6_orders_1(u1_orders_2(sK1),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4090,c_883,c_3240,c_3256,c_3706,c_3708,c_3856])).

cnf(c_4206,plain,
    ( r2_hidden(k4_tarski(sK2,X0_56),u1_orders_2(sK1)) != iProver_top
    | r2_hidden(X0_56,u1_struct_0(sK1)) != iProver_top
    | sK2 = X0_56 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3563,c_883,c_3240,c_3256,c_3270,c_3706,c_3708,c_3856,c_4090])).

cnf(c_4207,plain,
    ( sK2 = X0_56
    | r2_hidden(X0_56,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(k4_tarski(sK2,X0_56),u1_orders_2(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4206])).

cnf(c_4214,plain,
    ( sK0(u1_orders_2(sK1),sK2) = sK2
    | r2_hidden(sK0(u1_orders_2(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,k3_relat_1(u1_orders_2(sK1))) != iProver_top
    | r6_orders_1(u1_orders_2(sK1),sK2) = iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3551,c_4207])).

cnf(c_4220,plain,
    ( sK0(u1_orders_2(sK1),sK2) = sK2
    | r2_hidden(sK0(u1_orders_2(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,u1_struct_0(sK1)) != iProver_top
    | r6_orders_1(u1_orders_2(sK1),sK2) = iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4214,c_3213])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(sK0(X1,X0),k3_relat_1(X1))
    | r6_orders_1(X1,X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3216,plain,
    ( ~ r2_hidden(X0_56,k3_relat_1(X1_56))
    | r2_hidden(sK0(X1_56,X0_56),k3_relat_1(X1_56))
    | r6_orders_1(X1_56,X0_56)
    | ~ v1_relat_1(X1_56) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3553,plain,
    ( r2_hidden(X0_56,k3_relat_1(X1_56)) != iProver_top
    | r2_hidden(sK0(X1_56,X0_56),k3_relat_1(X1_56)) = iProver_top
    | r6_orders_1(X1_56,X0_56) = iProver_top
    | v1_relat_1(X1_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3216])).

cnf(c_4017,plain,
    ( r2_hidden(X0_56,k3_relat_1(u1_orders_2(sK1))) != iProver_top
    | r2_hidden(sK0(u1_orders_2(sK1),X0_56),u1_struct_0(sK1)) = iProver_top
    | r6_orders_1(u1_orders_2(sK1),X0_56) = iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3213,c_3553])).

cnf(c_4018,plain,
    ( r2_hidden(X0_56,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(u1_orders_2(sK1),X0_56),u1_struct_0(sK1)) = iProver_top
    | r6_orders_1(u1_orders_2(sK1),X0_56) = iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4017,c_3213])).

cnf(c_4020,plain,
    ( r2_hidden(sK0(u1_orders_2(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | r2_hidden(sK2,u1_struct_0(sK1)) != iProver_top
    | r6_orders_1(u1_orders_2(sK1),sK2) = iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4018])).

cnf(c_3230,plain,
    ( ~ r2_hidden(X0_56,X1_56)
    | r2_hidden(X2_56,X3_56)
    | X2_56 != X0_56
    | X3_56 != X1_56 ),
    theory(equality)).

cnf(c_3724,plain,
    ( r2_hidden(X0_56,X1_56)
    | ~ r2_hidden(sK2,u1_struct_0(sK1))
    | X1_56 != u1_struct_0(sK1)
    | X0_56 != sK2 ),
    inference(instantiation,[status(thm)],[c_3230])).

cnf(c_3792,plain,
    ( r2_hidden(X0_56,k3_relat_1(u1_orders_2(sK1)))
    | ~ r2_hidden(sK2,u1_struct_0(sK1))
    | X0_56 != sK2
    | k3_relat_1(u1_orders_2(sK1)) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3724])).

cnf(c_3793,plain,
    ( X0_56 != sK2
    | k3_relat_1(u1_orders_2(sK1)) != u1_struct_0(sK1)
    | r2_hidden(X0_56,k3_relat_1(u1_orders_2(sK1))) = iProver_top
    | r2_hidden(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3792])).

cnf(c_3795,plain,
    ( k3_relat_1(u1_orders_2(sK1)) != u1_struct_0(sK1)
    | sK2 != sK2
    | r2_hidden(sK2,k3_relat_1(u1_orders_2(sK1))) = iProver_top
    | r2_hidden(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3793])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r6_orders_1(X1,X0)
    | ~ v1_relat_1(X1)
    | sK0(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3217,plain,
    ( ~ r2_hidden(X0_56,k3_relat_1(X1_56))
    | r6_orders_1(X1_56,X0_56)
    | ~ v1_relat_1(X1_56)
    | sK0(X1_56,X0_56) != X0_56 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3752,plain,
    ( ~ r2_hidden(X0_56,k3_relat_1(u1_orders_2(sK1)))
    | r6_orders_1(u1_orders_2(sK1),X0_56)
    | ~ v1_relat_1(u1_orders_2(sK1))
    | sK0(u1_orders_2(sK1),X0_56) != X0_56 ),
    inference(instantiation,[status(thm)],[c_3217])).

cnf(c_3763,plain,
    ( sK0(u1_orders_2(sK1),X0_56) != X0_56
    | r2_hidden(X0_56,k3_relat_1(u1_orders_2(sK1))) != iProver_top
    | r6_orders_1(u1_orders_2(sK1),X0_56) = iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3752])).

cnf(c_3765,plain,
    ( sK0(u1_orders_2(sK1),sK2) != sK2
    | r2_hidden(sK2,k3_relat_1(u1_orders_2(sK1))) != iProver_top
    | r6_orders_1(u1_orders_2(sK1),sK2) = iProver_top
    | v1_relat_1(u1_orders_2(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3763])).

cnf(c_893,plain,
    ( r2_hidden(X0,u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_367,c_25])).

cnf(c_894,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_893])).

cnf(c_895,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_894])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4220,c_4200,c_4020,c_3795,c_3765,c_3708,c_3706,c_3213,c_3240,c_895])).


%------------------------------------------------------------------------------
