%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1935+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:53 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  166 (1799 expanded)
%              Number of clauses        :  104 ( 359 expanded)
%              Number of leaves         :   15 ( 471 expanded)
%              Depth                    :   25
%              Number of atoms          :  934 (20952 expanded)
%              Number of equality atoms :  161 ( 468 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   34 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( m3_yellow_6(X2,X0,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,X0)
               => ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( ( v1_partfun1(X2,X0)
              & v1_funct_1(X2)
              & v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( m3_yellow_6(X2,X0,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                    & v7_waybel_0(k1_funct_1(X2,X3))
                    & v4_orders_2(k1_funct_1(X2,X3))
                    & ~ v2_struct_0(k1_funct_1(X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( m3_yellow_6(X2,X0,X1)
          <~> ! [X3] :
                ( ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) )
                | ~ r2_hidden(X3,X0) ) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( m3_yellow_6(X2,X0,X1)
          <~> ! [X3] :
                ( ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) )
                | ~ r2_hidden(X3,X0) ) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),X1)
                  | ~ v7_waybel_0(k1_funct_1(X2,X3))
                  | ~ v4_orders_2(k1_funct_1(X2,X3))
                  | v2_struct_0(k1_funct_1(X2,X3)) )
                & r2_hidden(X3,X0) )
            | ~ m3_yellow_6(X2,X0,X1) )
          & ( ! [X3] :
                ( ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) )
                | ~ r2_hidden(X3,X0) )
            | m3_yellow_6(X2,X0,X1) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),X1)
                  | ~ v7_waybel_0(k1_funct_1(X2,X3))
                  | ~ v4_orders_2(k1_funct_1(X2,X3))
                  | v2_struct_0(k1_funct_1(X2,X3)) )
                & r2_hidden(X3,X0) )
            | ~ m3_yellow_6(X2,X0,X1) )
          & ( ! [X3] :
                ( ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) )
                | ~ r2_hidden(X3,X0) )
            | m3_yellow_6(X2,X0,X1) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),X1)
                  | ~ v7_waybel_0(k1_funct_1(X2,X3))
                  | ~ v4_orders_2(k1_funct_1(X2,X3))
                  | v2_struct_0(k1_funct_1(X2,X3)) )
                & r2_hidden(X3,X0) )
            | ~ m3_yellow_6(X2,X0,X1) )
          & ( ! [X4] :
                ( ( l1_waybel_0(k1_funct_1(X2,X4),X1)
                  & v7_waybel_0(k1_funct_1(X2,X4))
                  & v4_orders_2(k1_funct_1(X2,X4))
                  & ~ v2_struct_0(k1_funct_1(X2,X4)) )
                | ~ r2_hidden(X4,X0) )
            | m3_yellow_6(X2,X0,X1) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),X1)
            | ~ v7_waybel_0(k1_funct_1(X2,X3))
            | ~ v4_orders_2(k1_funct_1(X2,X3))
            | v2_struct_0(k1_funct_1(X2,X3)) )
          & r2_hidden(X3,X0) )
     => ( ( ~ l1_waybel_0(k1_funct_1(X2,sK7),X1)
          | ~ v7_waybel_0(k1_funct_1(X2,sK7))
          | ~ v4_orders_2(k1_funct_1(X2,sK7))
          | v2_struct_0(k1_funct_1(X2,sK7)) )
        & r2_hidden(sK7,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),X1)
                  | ~ v7_waybel_0(k1_funct_1(X2,X3))
                  | ~ v4_orders_2(k1_funct_1(X2,X3))
                  | v2_struct_0(k1_funct_1(X2,X3)) )
                & r2_hidden(X3,X0) )
            | ~ m3_yellow_6(X2,X0,X1) )
          & ( ! [X4] :
                ( ( l1_waybel_0(k1_funct_1(X2,X4),X1)
                  & v7_waybel_0(k1_funct_1(X2,X4))
                  & v4_orders_2(k1_funct_1(X2,X4))
                  & ~ v2_struct_0(k1_funct_1(X2,X4)) )
                | ~ r2_hidden(X4,X0) )
            | m3_yellow_6(X2,X0,X1) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
     => ( ( ? [X3] :
              ( ( ~ l1_waybel_0(k1_funct_1(sK6,X3),X1)
                | ~ v7_waybel_0(k1_funct_1(sK6,X3))
                | ~ v4_orders_2(k1_funct_1(sK6,X3))
                | v2_struct_0(k1_funct_1(sK6,X3)) )
              & r2_hidden(X3,X0) )
          | ~ m3_yellow_6(sK6,X0,X1) )
        & ( ! [X4] :
              ( ( l1_waybel_0(k1_funct_1(sK6,X4),X1)
                & v7_waybel_0(k1_funct_1(sK6,X4))
                & v4_orders_2(k1_funct_1(sK6,X4))
                & ~ v2_struct_0(k1_funct_1(sK6,X4)) )
              | ~ r2_hidden(X4,X0) )
          | m3_yellow_6(sK6,X0,X1) )
        & v1_partfun1(sK6,X0)
        & v1_funct_1(sK6)
        & v4_relat_1(sK6,X0)
        & v1_relat_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),X1)
                    | ~ v7_waybel_0(k1_funct_1(X2,X3))
                    | ~ v4_orders_2(k1_funct_1(X2,X3))
                    | v2_struct_0(k1_funct_1(X2,X3)) )
                  & r2_hidden(X3,X0) )
              | ~ m3_yellow_6(X2,X0,X1) )
            & ( ! [X4] :
                  ( ( l1_waybel_0(k1_funct_1(X2,X4),X1)
                    & v7_waybel_0(k1_funct_1(X2,X4))
                    & v4_orders_2(k1_funct_1(X2,X4))
                    & ~ v2_struct_0(k1_funct_1(X2,X4)) )
                  | ~ r2_hidden(X4,X0) )
              | m3_yellow_6(X2,X0,X1) )
            & v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),sK5)
                  | ~ v7_waybel_0(k1_funct_1(X2,X3))
                  | ~ v4_orders_2(k1_funct_1(X2,X3))
                  | v2_struct_0(k1_funct_1(X2,X3)) )
                & r2_hidden(X3,sK4) )
            | ~ m3_yellow_6(X2,sK4,sK5) )
          & ( ! [X4] :
                ( ( l1_waybel_0(k1_funct_1(X2,X4),sK5)
                  & v7_waybel_0(k1_funct_1(X2,X4))
                  & v4_orders_2(k1_funct_1(X2,X4))
                  & ~ v2_struct_0(k1_funct_1(X2,X4)) )
                | ~ r2_hidden(X4,sK4) )
            | m3_yellow_6(X2,sK4,sK5) )
          & v1_partfun1(X2,sK4)
          & v1_funct_1(X2)
          & v4_relat_1(X2,sK4)
          & v1_relat_1(X2) )
      & l1_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ( ( ~ l1_waybel_0(k1_funct_1(sK6,sK7),sK5)
          | ~ v7_waybel_0(k1_funct_1(sK6,sK7))
          | ~ v4_orders_2(k1_funct_1(sK6,sK7))
          | v2_struct_0(k1_funct_1(sK6,sK7)) )
        & r2_hidden(sK7,sK4) )
      | ~ m3_yellow_6(sK6,sK4,sK5) )
    & ( ! [X4] :
          ( ( l1_waybel_0(k1_funct_1(sK6,X4),sK5)
            & v7_waybel_0(k1_funct_1(sK6,X4))
            & v4_orders_2(k1_funct_1(sK6,X4))
            & ~ v2_struct_0(k1_funct_1(sK6,X4)) )
          | ~ r2_hidden(X4,sK4) )
      | m3_yellow_6(sK6,sK4,sK5) )
    & v1_partfun1(sK6,sK4)
    & v1_funct_1(sK6)
    & v4_relat_1(sK6,sK4)
    & v1_relat_1(sK6)
    & l1_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f29,f32,f31,f30])).

fof(f57,plain,(
    ! [X4] :
      ( ~ v2_struct_0(k1_funct_1(sK6,X4))
      | ~ r2_hidden(X4,sK4)
      | m3_yellow_6(sK6,sK4,sK5) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X4] :
      ( v4_orders_2(k1_funct_1(sK6,X4))
      | ~ r2_hidden(X4,sK4)
      | m3_yellow_6(sK6,sK4,sK5) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    ! [X4] :
      ( v7_waybel_0(k1_funct_1(sK6,X4))
      | ~ r2_hidden(X4,sK4)
      | m3_yellow_6(sK6,sK4,sK5) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X4] :
      ( l1_waybel_0(k1_funct_1(sK6,X4),sK5)
      | ~ r2_hidden(X4,sK4)
      | m3_yellow_6(sK6,sK4,sK5) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( m3_yellow_6(X2,X0,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,k2_relat_1(X2))
               => ( l1_waybel_0(X3,X1)
                  & v7_waybel_0(X3)
                  & v4_orders_2(X3)
                  & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m3_yellow_6(X2,X0,X1)
          <=> ! [X3] :
                ( ( l1_waybel_0(X3,X1)
                  & v7_waybel_0(X3)
                  & v4_orders_2(X3)
                  & ~ v2_struct_0(X3) )
                | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m3_yellow_6(X2,X0,X1)
          <=> ! [X3] :
                ( ( l1_waybel_0(X3,X1)
                  & v7_waybel_0(X3)
                  & v4_orders_2(X3)
                  & ~ v2_struct_0(X3) )
                | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(flattening,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( m3_yellow_6(X2,X0,X1)
              | ? [X3] :
                  ( ( ~ l1_waybel_0(X3,X1)
                    | ~ v7_waybel_0(X3)
                    | ~ v4_orders_2(X3)
                    | v2_struct_0(X3) )
                  & r2_hidden(X3,k2_relat_1(X2)) ) )
            & ( ! [X3] :
                  ( ( l1_waybel_0(X3,X1)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) )
                  | ~ r2_hidden(X3,k2_relat_1(X2)) )
              | ~ m3_yellow_6(X2,X0,X1) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( m3_yellow_6(X2,X0,X1)
              | ? [X3] :
                  ( ( ~ l1_waybel_0(X3,X1)
                    | ~ v7_waybel_0(X3)
                    | ~ v4_orders_2(X3)
                    | v2_struct_0(X3) )
                  & r2_hidden(X3,k2_relat_1(X2)) ) )
            & ( ! [X4] :
                  ( ( l1_waybel_0(X4,X1)
                    & v7_waybel_0(X4)
                    & v4_orders_2(X4)
                    & ~ v2_struct_0(X4) )
                  | ~ r2_hidden(X4,k2_relat_1(X2)) )
              | ~ m3_yellow_6(X2,X0,X1) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ( ~ l1_waybel_0(X3,X1)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
          & r2_hidden(X3,k2_relat_1(X2)) )
     => ( ( ~ l1_waybel_0(sK0(X1,X2),X1)
          | ~ v7_waybel_0(sK0(X1,X2))
          | ~ v4_orders_2(sK0(X1,X2))
          | v2_struct_0(sK0(X1,X2)) )
        & r2_hidden(sK0(X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( m3_yellow_6(X2,X0,X1)
              | ( ( ~ l1_waybel_0(sK0(X1,X2),X1)
                  | ~ v7_waybel_0(sK0(X1,X2))
                  | ~ v4_orders_2(sK0(X1,X2))
                  | v2_struct_0(sK0(X1,X2)) )
                & r2_hidden(sK0(X1,X2),k2_relat_1(X2)) ) )
            & ( ! [X4] :
                  ( ( l1_waybel_0(X4,X1)
                    & v7_waybel_0(X4)
                    & v4_orders_2(X4)
                    & ~ v2_struct_0(X4) )
                  | ~ r2_hidden(X4,k2_relat_1(X2)) )
              | ~ m3_yellow_6(X2,X0,X1) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m3_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(sK0(X1,X2),X1)
      | ~ v7_waybel_0(sK0(X1,X2))
      | ~ v4_orders_2(sK0(X1,X2))
      | v2_struct_0(sK0(X1,X2))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    v4_relat_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    v1_partfun1(sK6,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,
    ( ~ l1_waybel_0(k1_funct_1(sK6,sK7),sK5)
    | ~ v7_waybel_0(k1_funct_1(sK6,sK7))
    | ~ v4_orders_2(k1_funct_1(sK6,sK7))
    | v2_struct_0(k1_funct_1(sK6,sK7))
    | ~ m3_yellow_6(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( l1_waybel_0(X4,X1)
      | ~ r2_hidden(X4,k2_relat_1(X2))
      | ~ m3_yellow_6(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m3_yellow_6(X2,X0,X1)
         => ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
          | ~ m3_yellow_6(X2,X0,X1) )
      | ~ l1_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m3_yellow_6(X2,X0,X1)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m3_yellow_6(X2,X0,X1)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ m3_yellow_6(X2,X0,X1)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m3_yellow_6(X2,X0,X1)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( v7_waybel_0(X4)
      | ~ r2_hidden(X4,k2_relat_1(X2))
      | ~ m3_yellow_6(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_orders_2(X4)
      | ~ r2_hidden(X4,k2_relat_1(X2))
      | ~ m3_yellow_6(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v2_struct_0(X4)
      | ~ r2_hidden(X4,k2_relat_1(X2))
      | ~ m3_yellow_6(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m3_yellow_6(X2,X0,X1)
      | r2_hidden(sK0(X1,X2),k2_relat_1(X2))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f25,f24,f23])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f65,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,
    ( r2_hidden(sK7,sK4)
    | ~ m3_yellow_6(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f42,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

cnf(c_23,negated_conjecture,
    ( m3_yellow_6(sK6,sK4,sK5)
    | ~ r2_hidden(X0,sK4)
    | ~ v2_struct_0(k1_funct_1(sK6,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,negated_conjecture,
    ( m3_yellow_6(sK6,sK4,sK5)
    | ~ r2_hidden(X0,sK4)
    | v4_orders_2(k1_funct_1(sK6,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,negated_conjecture,
    ( m3_yellow_6(sK6,sK4,sK5)
    | ~ r2_hidden(X0,sK4)
    | v7_waybel_0(k1_funct_1(sK6,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,negated_conjecture,
    ( m3_yellow_6(sK6,sK4,sK5)
    | ~ r2_hidden(X0,sK4)
    | l1_waybel_0(k1_funct_1(sK6,X0),sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_0,plain,
    ( m3_yellow_6(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ l1_waybel_0(sK0(X2,X0),X2)
    | ~ l1_struct_0(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK0(X2,X0))
    | ~ v4_orders_2(sK0(X2,X0))
    | ~ v7_waybel_0(sK0(X2,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_28,negated_conjecture,
    ( l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_469,plain,
    ( m3_yellow_6(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ l1_waybel_0(sK0(X2,X0),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK0(X2,X0))
    | ~ v4_orders_2(sK0(X2,X0))
    | ~ v7_waybel_0(sK0(X2,X0))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_28])).

cnf(c_470,plain,
    ( m3_yellow_6(X0,X1,sK5)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ l1_waybel_0(sK0(sK5,X0),sK5)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK0(sK5,X0))
    | ~ v4_orders_2(sK0(sK5,X0))
    | ~ v7_waybel_0(sK0(sK5,X0)) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_26,negated_conjecture,
    ( v4_relat_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_969,plain,
    ( m3_yellow_6(X0,X1,sK5)
    | ~ v1_partfun1(X0,X1)
    | ~ l1_waybel_0(sK0(sK5,X0),sK5)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK0(sK5,X0))
    | ~ v4_orders_2(sK0(sK5,X0))
    | ~ v7_waybel_0(sK0(sK5,X0))
    | sK4 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_470,c_26])).

cnf(c_970,plain,
    ( m3_yellow_6(sK6,sK4,sK5)
    | ~ v1_partfun1(sK6,sK4)
    | ~ l1_waybel_0(sK0(sK5,sK6),sK5)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK6)
    | v2_struct_0(sK0(sK5,sK6))
    | ~ v4_orders_2(sK0(sK5,sK6))
    | ~ v7_waybel_0(sK0(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_969])).

cnf(c_27,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,negated_conjecture,
    ( v1_partfun1(sK6,sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_972,plain,
    ( m3_yellow_6(sK6,sK4,sK5)
    | ~ l1_waybel_0(sK0(sK5,sK6),sK5)
    | v2_struct_0(sK0(sK5,sK6))
    | ~ v4_orders_2(sK0(sK5,sK6))
    | ~ v7_waybel_0(sK0(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_970,c_27,c_25,c_24])).

cnf(c_1058,plain,
    ( m3_yellow_6(sK6,sK4,sK5)
    | ~ r2_hidden(X0,sK4)
    | v2_struct_0(sK0(sK5,sK6))
    | ~ v4_orders_2(sK0(sK5,sK6))
    | ~ v7_waybel_0(sK0(sK5,sK6))
    | k1_funct_1(sK6,X0) != sK0(sK5,sK6)
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_972])).

cnf(c_1124,plain,
    ( m3_yellow_6(sK6,sK4,sK5)
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X1,sK4)
    | v2_struct_0(sK0(sK5,sK6))
    | ~ v4_orders_2(sK0(sK5,sK6))
    | k1_funct_1(sK6,X0) != sK0(sK5,sK6)
    | k1_funct_1(sK6,X1) != sK0(sK5,sK6)
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1058])).

cnf(c_1171,plain,
    ( m3_yellow_6(sK6,sK4,sK5)
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X1,sK4)
    | ~ r2_hidden(X2,sK4)
    | v2_struct_0(sK0(sK5,sK6))
    | k1_funct_1(sK6,X0) != sK0(sK5,sK6)
    | k1_funct_1(sK6,X2) != sK0(sK5,sK6)
    | k1_funct_1(sK6,X1) != sK0(sK5,sK6)
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_1124])).

cnf(c_1222,plain,
    ( m3_yellow_6(sK6,sK4,sK5)
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X1,sK4)
    | ~ r2_hidden(X2,sK4)
    | ~ r2_hidden(X3,sK4)
    | k1_funct_1(sK6,X1) != sK0(sK5,sK6)
    | k1_funct_1(sK6,X3) != sK0(sK5,sK6)
    | k1_funct_1(sK6,X0) != sK0(sK5,sK6)
    | k1_funct_1(sK6,X2) != sK0(sK5,sK6)
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_1171])).

cnf(c_1833,plain,
    ( m3_yellow_6(sK6,sK4,sK5)
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X1,sK4)
    | ~ r2_hidden(X2,sK4)
    | ~ r2_hidden(X3,sK4)
    | k1_funct_1(sK6,X1) != sK0(sK5,sK6)
    | k1_funct_1(sK6,X3) != sK0(sK5,sK6)
    | k1_funct_1(sK6,X0) != sK0(sK5,sK6)
    | k1_funct_1(sK6,X2) != sK0(sK5,sK6) ),
    inference(equality_resolution_simp,[status(thm)],[c_1222])).

cnf(c_2424,plain,
    ( ~ r2_hidden(X0,sK4)
    | k1_funct_1(sK6,X0) != sK0(sK5,sK6)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1833])).

cnf(c_6096,plain,
    ( ~ r2_hidden(sK3(sK6,sK0(sK5,sK6)),sK4)
    | ~ sP0_iProver_split
    | k1_funct_1(sK6,sK3(sK6,sK0(sK5,sK6))) != sK0(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_2424])).

cnf(c_18,negated_conjecture,
    ( ~ m3_yellow_6(sK6,sK4,sK5)
    | ~ l1_waybel_0(k1_funct_1(sK6,sK7),sK5)
    | v2_struct_0(k1_funct_1(sK6,sK7))
    | ~ v4_orders_2(k1_funct_1(sK6,sK7))
    | ~ v7_waybel_0(k1_funct_1(sK6,sK7)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2,plain,
    ( ~ m3_yellow_6(X0,X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0))
    | ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | l1_waybel_0(X3,X2)
    | ~ l1_struct_0(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,plain,
    ( ~ m3_yellow_6(X0,X1,X2)
    | ~ l1_struct_0(X2)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_16,plain,
    ( ~ m3_yellow_6(X0,X1,X2)
    | v4_relat_1(X0,X1)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_15,plain,
    ( ~ m3_yellow_6(X0,X1,X2)
    | ~ l1_struct_0(X2)
    | v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_14,plain,
    ( ~ m3_yellow_6(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_201,plain,
    ( ~ m3_yellow_6(X0,X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0))
    | l1_waybel_0(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_17,c_16,c_15,c_14])).

cnf(c_341,plain,
    ( ~ m3_yellow_6(X0,X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0))
    | l1_waybel_0(X3,X2)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_201,c_28])).

cnf(c_342,plain,
    ( ~ m3_yellow_6(X0,X1,sK5)
    | ~ r2_hidden(X2,k2_relat_1(X0))
    | l1_waybel_0(X2,sK5) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_1041,plain,
    ( ~ m3_yellow_6(X0,X1,sK5)
    | ~ m3_yellow_6(sK6,sK4,sK5)
    | ~ r2_hidden(X2,k2_relat_1(X0))
    | v2_struct_0(k1_funct_1(sK6,sK7))
    | ~ v4_orders_2(k1_funct_1(sK6,sK7))
    | ~ v7_waybel_0(k1_funct_1(sK6,sK7))
    | k1_funct_1(sK6,sK7) != X2
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_342])).

cnf(c_1042,plain,
    ( ~ m3_yellow_6(X0,X1,sK5)
    | ~ m3_yellow_6(sK6,sK4,sK5)
    | ~ r2_hidden(k1_funct_1(sK6,sK7),k2_relat_1(X0))
    | v2_struct_0(k1_funct_1(sK6,sK7))
    | ~ v4_orders_2(k1_funct_1(sK6,sK7))
    | ~ v7_waybel_0(k1_funct_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_1041])).

cnf(c_548,plain,
    ( ~ m3_yellow_6(X0,X1,sK5)
    | ~ m3_yellow_6(sK6,sK4,sK5)
    | ~ r2_hidden(X2,k2_relat_1(X0))
    | v2_struct_0(k1_funct_1(sK6,sK7))
    | ~ v4_orders_2(k1_funct_1(sK6,sK7))
    | ~ v7_waybel_0(k1_funct_1(sK6,sK7))
    | k1_funct_1(sK6,sK7) != X2
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_342])).

cnf(c_549,plain,
    ( ~ m3_yellow_6(X0,X1,sK5)
    | ~ m3_yellow_6(sK6,sK4,sK5)
    | ~ r2_hidden(k1_funct_1(sK6,sK7),k2_relat_1(X0))
    | v2_struct_0(k1_funct_1(sK6,sK7))
    | ~ v4_orders_2(k1_funct_1(sK6,sK7))
    | ~ v7_waybel_0(k1_funct_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_3,plain,
    ( ~ m3_yellow_6(X0,X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0))
    | ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ l1_struct_0(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v7_waybel_0(X3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_194,plain,
    ( ~ m3_yellow_6(X0,X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0))
    | ~ l1_struct_0(X2)
    | v7_waybel_0(X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_17,c_16,c_15,c_14])).

cnf(c_356,plain,
    ( ~ m3_yellow_6(X0,X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0))
    | v7_waybel_0(X3)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_194,c_28])).

cnf(c_357,plain,
    ( ~ m3_yellow_6(X0,X1,sK5)
    | ~ r2_hidden(X2,k2_relat_1(X0))
    | v7_waybel_0(X2) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_4,plain,
    ( ~ m3_yellow_6(X0,X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0))
    | ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ l1_struct_0(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v4_orders_2(X3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_187,plain,
    ( ~ m3_yellow_6(X0,X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0))
    | ~ l1_struct_0(X2)
    | v4_orders_2(X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_17,c_16,c_15,c_14])).

cnf(c_371,plain,
    ( ~ m3_yellow_6(X0,X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0))
    | v4_orders_2(X3)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_187,c_28])).

cnf(c_372,plain,
    ( ~ m3_yellow_6(X0,X1,sK5)
    | ~ r2_hidden(X2,k2_relat_1(X0))
    | v4_orders_2(X2) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_5,plain,
    ( ~ m3_yellow_6(X0,X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0))
    | ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ l1_struct_0(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_struct_0(X3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_180,plain,
    ( ~ m3_yellow_6(X0,X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0))
    | ~ l1_struct_0(X2)
    | ~ v2_struct_0(X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_17,c_16,c_15,c_14])).

cnf(c_386,plain,
    ( ~ m3_yellow_6(X0,X1,X2)
    | ~ r2_hidden(X3,k2_relat_1(X0))
    | ~ v2_struct_0(X3)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_180,c_28])).

cnf(c_387,plain,
    ( ~ m3_yellow_6(X0,X1,sK5)
    | ~ r2_hidden(X2,k2_relat_1(X0))
    | ~ v2_struct_0(X2) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_565,plain,
    ( ~ m3_yellow_6(X0,X1,sK5)
    | ~ m3_yellow_6(sK6,sK4,sK5)
    | ~ r2_hidden(k1_funct_1(sK6,sK7),k2_relat_1(X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_549,c_357,c_372,c_387])).

cnf(c_1044,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK7),k2_relat_1(X0))
    | ~ m3_yellow_6(sK6,sK4,sK5)
    | ~ m3_yellow_6(X0,X1,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1042,c_565])).

cnf(c_1045,plain,
    ( ~ m3_yellow_6(X0,X1,sK5)
    | ~ m3_yellow_6(sK6,sK4,sK5)
    | ~ r2_hidden(k1_funct_1(sK6,sK7),k2_relat_1(X0)) ),
    inference(renaming,[status(thm)],[c_1044])).

cnf(c_4399,plain,
    ( ~ m3_yellow_6(sK6,sK4,sK5)
    | ~ r2_hidden(k1_funct_1(sK6,sK7),k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_1,plain,
    ( m3_yellow_6(X0,X1,X2)
    | r2_hidden(sK0(X2,X0),k2_relat_1(X0))
    | ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ l1_struct_0(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_445,plain,
    ( m3_yellow_6(X0,X1,X2)
    | r2_hidden(sK0(X2,X0),k2_relat_1(X0))
    | ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_28])).

cnf(c_446,plain,
    ( m3_yellow_6(X0,X1,sK5)
    | r2_hidden(sK0(sK5,X0),k2_relat_1(X0))
    | ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_992,plain,
    ( m3_yellow_6(X0,X1,sK5)
    | r2_hidden(sK0(sK5,X0),k2_relat_1(X0))
    | ~ v1_partfun1(X0,X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | sK4 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_446,c_26])).

cnf(c_993,plain,
    ( m3_yellow_6(sK6,sK4,sK5)
    | r2_hidden(sK0(sK5,sK6),k2_relat_1(sK6))
    | ~ v1_partfun1(sK6,sK4)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK6) ),
    inference(unflattening,[status(thm)],[c_992])).

cnf(c_995,plain,
    ( r2_hidden(sK0(sK5,sK6),k2_relat_1(sK6))
    | m3_yellow_6(sK6,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_993,c_27,c_25,c_24])).

cnf(c_996,plain,
    ( m3_yellow_6(sK6,sK4,sK5)
    | r2_hidden(sK0(sK5,sK6),k2_relat_1(sK6)) ),
    inference(renaming,[status(thm)],[c_995])).

cnf(c_2766,plain,
    ( m3_yellow_6(sK6,sK4,sK5) = iProver_top
    | r2_hidden(sK0(sK5,sK6),k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2775,plain,
    ( k1_funct_1(X0,sK3(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3097,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK0(sK5,sK6))) = sK0(sK5,sK6)
    | m3_yellow_6(sK6,sK4,sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2766,c_2775])).

cnf(c_30,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_32,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3668,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK0(sK5,sK6))) = sK0(sK5,sK6)
    | m3_yellow_6(sK6,sK4,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3097,c_30,c_32])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2776,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2768,plain,
    ( m3_yellow_6(X0,X1,sK5) != iProver_top
    | m3_yellow_6(sK6,sK4,sK5) != iProver_top
    | r2_hidden(k1_funct_1(sK6,sK7),k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1045])).

cnf(c_3171,plain,
    ( m3_yellow_6(sK6,X0,sK5) != iProver_top
    | m3_yellow_6(sK6,sK4,sK5) != iProver_top
    | r2_hidden(sK7,k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2776,c_2768])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1006,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | sK4 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_26])).

cnf(c_1007,plain,
    ( ~ v1_partfun1(sK6,sK4)
    | ~ v1_relat_1(sK6)
    | k1_relat_1(sK6) = sK4 ),
    inference(unflattening,[status(thm)],[c_1006])).

cnf(c_1009,plain,
    ( k1_relat_1(sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1007,c_27,c_24])).

cnf(c_3177,plain,
    ( m3_yellow_6(sK6,X0,sK5) != iProver_top
    | m3_yellow_6(sK6,sK4,sK5) != iProver_top
    | r2_hidden(sK7,sK4) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3171,c_1009])).

cnf(c_19,negated_conjecture,
    ( ~ m3_yellow_6(sK6,sK4,sK5)
    | r2_hidden(sK7,sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_46,plain,
    ( m3_yellow_6(sK6,sK4,sK5) != iProver_top
    | r2_hidden(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3344,plain,
    ( m3_yellow_6(sK6,sK4,sK5) != iProver_top
    | m3_yellow_6(sK6,X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3177,c_30,c_32,c_46])).

cnf(c_3345,plain,
    ( m3_yellow_6(sK6,X0,sK5) != iProver_top
    | m3_yellow_6(sK6,sK4,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_3344])).

cnf(c_3674,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK0(sK5,sK6))) = sK0(sK5,sK6)
    | m3_yellow_6(sK6,X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3668,c_3345])).

cnf(c_3688,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK0(sK5,sK6))) = sK0(sK5,sK6) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3674,c_3668])).

cnf(c_2427,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3644,plain,
    ( sK3(sK6,sK0(sK5,sK6)) = sK3(sK6,sK0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2427])).

cnf(c_2434,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3076,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3(sK6,sK0(sK5,sK6)),k1_relat_1(sK6))
    | X0 != sK3(sK6,sK0(sK5,sK6))
    | X1 != k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2434])).

cnf(c_3545,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(sK3(sK6,sK0(sK5,sK6)),k1_relat_1(sK6))
    | X0 != sK3(sK6,sK0(sK5,sK6))
    | sK4 != k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3076])).

cnf(c_3643,plain,
    ( ~ r2_hidden(sK3(sK6,sK0(sK5,sK6)),k1_relat_1(sK6))
    | r2_hidden(sK3(sK6,sK0(sK5,sK6)),sK4)
    | sK3(sK6,sK0(sK5,sK6)) != sK3(sK6,sK0(sK5,sK6))
    | sK4 != k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3545])).

cnf(c_2425,plain,
    ( m3_yellow_6(sK6,sK4,sK5)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1833])).

cnf(c_2760,plain,
    ( m3_yellow_6(sK6,sK4,sK5) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2425])).

cnf(c_3352,plain,
    ( m3_yellow_6(sK6,X0,sK5) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2760,c_3345])).

cnf(c_3454,plain,
    ( sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2760,c_3352])).

cnf(c_3455,plain,
    ( sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3454])).

cnf(c_2428,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3047,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_2428])).

cnf(c_3138,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3047])).

cnf(c_3334,plain,
    ( k1_relat_1(sK6) != sK4
    | sK4 = k1_relat_1(sK6)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3138])).

cnf(c_3140,plain,
    ( r2_hidden(k1_funct_1(sK6,sK7),k2_relat_1(sK6))
    | ~ r2_hidden(sK7,k1_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3050,plain,
    ( r2_hidden(sK3(sK6,sK0(sK5,sK6)),k1_relat_1(sK6))
    | ~ r2_hidden(sK0(sK5,sK6),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3034,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_2427])).

cnf(c_2926,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7,sK4)
    | X1 != sK4
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_2434])).

cnf(c_2960,plain,
    ( r2_hidden(X0,k1_relat_1(sK6))
    | ~ r2_hidden(sK7,sK4)
    | X0 != sK7
    | k1_relat_1(sK6) != sK4 ),
    inference(instantiation,[status(thm)],[c_2926])).

cnf(c_3033,plain,
    ( r2_hidden(sK7,k1_relat_1(sK6))
    | ~ r2_hidden(sK7,sK4)
    | k1_relat_1(sK6) != sK4
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2960])).

cnf(c_2953,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2427])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6096,c_4399,c_3688,c_3644,c_3643,c_3455,c_3334,c_3140,c_3050,c_3034,c_3033,c_2953,c_1007,c_996,c_19,c_24,c_25,c_27])).


%------------------------------------------------------------------------------
