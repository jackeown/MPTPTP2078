%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1628+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:01 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 891 expanded)
%              Number of clauses        :  134 ( 204 expanded)
%              Number of leaves         :   16 ( 288 expanded)
%              Depth                    :   16
%              Number of atoms          :  821 (7097 expanded)
%              Number of equality atoms :  103 ( 103 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X3] :
                    ( ? [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ? [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        & r1_orders_2(X1,X5,X6)
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f28])).

fof(f31,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
        & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
                      & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f31,f30])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( r1_tarski(X2,X3)
             => ( ( r2_waybel_0(X0,X1,X2)
                 => r2_waybel_0(X0,X1,X3) )
                & ( r1_waybel_0(X0,X1,X2)
                 => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2,X3] :
                ( r1_tarski(X2,X3)
               => ( ( r2_waybel_0(X0,X1,X2)
                   => r2_waybel_0(X0,X1,X3) )
                  & ( r1_waybel_0(X0,X1,X2)
                   => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ( ( ~ r2_waybel_0(X0,X1,X3)
                  & r2_waybel_0(X0,X1,X2) )
                | ( ~ r1_waybel_0(X0,X1,X3)
                  & r1_waybel_0(X0,X1,X2) ) )
              & r1_tarski(X2,X3) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ( ( ~ r2_waybel_0(X0,X1,X3)
                  & r2_waybel_0(X0,X1,X2) )
                | ( ~ r1_waybel_0(X0,X1,X3)
                  & r1_waybel_0(X0,X1,X2) ) )
              & r1_tarski(X2,X3) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( ( ( ~ r2_waybel_0(X0,X1,X3)
              & r2_waybel_0(X0,X1,X2) )
            | ( ~ r1_waybel_0(X0,X1,X3)
              & r1_waybel_0(X0,X1,X2) ) )
          & r1_tarski(X2,X3) )
     => ( ( ( ~ r2_waybel_0(X0,X1,sK8)
            & r2_waybel_0(X0,X1,sK7) )
          | ( ~ r1_waybel_0(X0,X1,sK8)
            & r1_waybel_0(X0,X1,sK7) ) )
        & r1_tarski(sK7,sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ( ( ~ r2_waybel_0(X0,X1,X3)
                  & r2_waybel_0(X0,X1,X2) )
                | ( ~ r1_waybel_0(X0,X1,X3)
                  & r1_waybel_0(X0,X1,X2) ) )
              & r1_tarski(X2,X3) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X3,X2] :
            ( ( ( ~ r2_waybel_0(X0,sK6,X3)
                & r2_waybel_0(X0,sK6,X2) )
              | ( ~ r1_waybel_0(X0,sK6,X3)
                & r1_waybel_0(X0,sK6,X2) ) )
            & r1_tarski(X2,X3) )
        & l1_waybel_0(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ( ( ~ r2_waybel_0(X0,X1,X3)
                    & r2_waybel_0(X0,X1,X2) )
                  | ( ~ r1_waybel_0(X0,X1,X3)
                    & r1_waybel_0(X0,X1,X2) ) )
                & r1_tarski(X2,X3) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ( ( ~ r2_waybel_0(sK5,X1,X3)
                  & r2_waybel_0(sK5,X1,X2) )
                | ( ~ r1_waybel_0(sK5,X1,X3)
                  & r1_waybel_0(sK5,X1,X2) ) )
              & r1_tarski(X2,X3) )
          & l1_waybel_0(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ( ~ r2_waybel_0(sK5,sK6,sK8)
        & r2_waybel_0(sK5,sK6,sK7) )
      | ( ~ r1_waybel_0(sK5,sK6,sK8)
        & r1_waybel_0(sK5,sK6,sK7) ) )
    & r1_tarski(sK7,sK8)
    & l1_waybel_0(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_struct_0(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f22,f37,f36,f35])).

fof(f57,plain,(
    l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK1(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3))
        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3))
                      & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK1(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).

fof(f40,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
      | ~ r1_orders_2(X1,sK1(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | r1_orders_2(X1,X3,sK0(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X2,X0,X5,X1] :
      ( m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f33])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,
    ( ~ r2_waybel_0(sK5,sK6,sK8)
    | ~ r1_waybel_0(sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,
    ( ~ r2_waybel_0(sK5,sK6,sK8)
    | r1_waybel_0(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f38])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,
    ( r2_waybel_0(sK5,sK6,sK7)
    | r1_waybel_0(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    r1_tarski(sK7,sK8) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,
    ( r2_waybel_0(sK5,sK6,sK7)
    | ~ r1_waybel_0(sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2540,plain,
    ( ~ m1_subset_1(X0_51,X1_51)
    | r2_hidden(X0_51,X1_51)
    | v1_xboole_0(X1_51) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_4919,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,sK7,sK2(sK5,sK6,sK8))),sK8)
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,sK7,sK2(sK5,sK6,sK8))),sK8)
    | v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2540])).

cnf(c_4920,plain,
    ( m1_subset_1(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,sK7,sK2(sK5,sK6,sK8))),sK8) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,sK7,sK2(sK5,sK6,sK8))),sK8) = iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4919])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2539,plain,
    ( m1_subset_1(X0_51,X1_51)
    | ~ m1_subset_1(X2_51,k1_zfmisc_1(X1_51))
    | ~ r2_hidden(X0_51,X2_51) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_4048,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | m1_subset_1(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0_51,sK2(sK5,sK6,sK8))),X1_51)
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0_51,sK2(sK5,sK6,sK8))),X0_51) ),
    inference(instantiation,[status(thm)],[c_2539])).

cnf(c_4768,plain,
    ( m1_subset_1(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,sK7,sK2(sK5,sK6,sK8))),sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(sK8))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,sK7,sK2(sK5,sK6,sK8))),sK7) ),
    inference(instantiation,[status(thm)],[c_4048])).

cnf(c_4769,plain,
    ( m1_subset_1(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,sK7,sK2(sK5,sK6,sK8))),sK8) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(sK8)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,sK7,sK2(sK5,sK6,sK8))),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4768])).

cnf(c_5,plain,
    ( r2_waybel_0(X0,X1,X2)
    | ~ r1_orders_2(X1,sK2(X0,X1,X2),X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,X3),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,negated_conjecture,
    ( l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_539,plain,
    ( r2_waybel_0(sK5,sK6,X0)
    | ~ r1_orders_2(sK6,sK2(sK5,sK6,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,X1),X0)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_5,c_20])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,negated_conjecture,
    ( l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_543,plain,
    ( ~ r2_hidden(k2_waybel_0(sK5,sK6,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r1_orders_2(sK6,sK2(sK5,sK6,X0),X1)
    | r2_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_23,c_22,c_21])).

cnf(c_544,plain,
    ( r2_waybel_0(sK5,sK6,X0)
    | ~ r1_orders_2(sK6,sK2(sK5,sK6,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,X1),X0) ),
    inference(renaming,[status(thm)],[c_543])).

cnf(c_2528,plain,
    ( r2_waybel_0(sK5,sK6,X0_51)
    | ~ r1_orders_2(sK6,sK2(sK5,sK6,X0_51),X1_51)
    | ~ m1_subset_1(X1_51,u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,X1_51),X0_51) ),
    inference(subtyping,[status(esa)],[c_544])).

cnf(c_2669,plain,
    ( r2_waybel_0(sK5,sK6,sK8)
    | ~ r1_orders_2(sK6,sK2(sK5,sK6,sK8),X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,X0_51),sK8) ),
    inference(instantiation,[status(thm)],[c_2528])).

cnf(c_3968,plain,
    ( r2_waybel_0(sK5,sK6,sK8)
    | ~ r1_orders_2(sK6,sK2(sK5,sK6,sK8),sK3(sK5,sK6,X0_51,sK2(sK5,sK6,sK8)))
    | ~ m1_subset_1(sK3(sK5,sK6,X0_51,sK2(sK5,sK6,sK8)),u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0_51,sK2(sK5,sK6,sK8))),sK8) ),
    inference(instantiation,[status(thm)],[c_2669])).

cnf(c_3969,plain,
    ( r2_waybel_0(sK5,sK6,sK8) = iProver_top
    | r1_orders_2(sK6,sK2(sK5,sK6,sK8),sK3(sK5,sK6,X0_51,sK2(sK5,sK6,sK8))) != iProver_top
    | m1_subset_1(sK3(sK5,sK6,X0_51,sK2(sK5,sK6,sK8)),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0_51,sK2(sK5,sK6,sK8))),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3968])).

cnf(c_3971,plain,
    ( r2_waybel_0(sK5,sK6,sK8) = iProver_top
    | r1_orders_2(sK6,sK2(sK5,sK6,sK8),sK3(sK5,sK6,sK7,sK2(sK5,sK6,sK8))) != iProver_top
    | m1_subset_1(sK3(sK5,sK6,sK7,sK2(sK5,sK6,sK8)),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,sK7,sK2(sK5,sK6,sK8))),sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3969])).

cnf(c_3700,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X0_51))),sK8)
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X0_51))),sK8)
    | v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2540])).

cnf(c_3701,plain,
    ( m1_subset_1(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X0_51))),sK8) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X0_51))),sK8) = iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3700])).

cnf(c_3703,plain,
    ( m1_subset_1(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,sK7))),sK8) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,sK7))),sK8) = iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3701])).

cnf(c_3385,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | m1_subset_1(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X2_51))),X1_51)
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X2_51))),X0_51) ),
    inference(instantiation,[status(thm)],[c_2539])).

cnf(c_3681,plain,
    ( m1_subset_1(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X0_51))),sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(sK8))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X0_51))),sK7) ),
    inference(instantiation,[status(thm)],[c_3385])).

cnf(c_3682,plain,
    ( m1_subset_1(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X0_51))),sK8) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(sK8)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X0_51))),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3681])).

cnf(c_3684,plain,
    ( m1_subset_1(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,sK7))),sK8) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(sK8)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,sK7))),sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3682])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2538,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ r2_hidden(X2_51,X0_51)
    | ~ v1_xboole_0(X1_51) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3380,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X2_51))),X0_51)
    | ~ v1_xboole_0(X1_51) ),
    inference(instantiation,[status(thm)],[c_2538])).

cnf(c_3604,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(sK8))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X0_51))),sK7)
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_3380])).

cnf(c_3605,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK8)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X0_51))),sK7) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3604])).

cnf(c_3607,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK8)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,sK7))),sK7) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3605])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,sK1(X1,X0,X2),X3)
    | ~ r1_waybel_0(X1,X0,X2)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | r2_hidden(k2_waybel_0(X1,X0,X3),X2)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_639,plain,
    ( ~ r1_orders_2(sK6,sK1(sK5,sK6,X0),X1)
    | ~ r1_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,X1),X0)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_3,c_20])).

cnf(c_643,plain,
    ( r2_hidden(k2_waybel_0(sK5,sK6,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r1_waybel_0(sK5,sK6,X0)
    | ~ r1_orders_2(sK6,sK1(sK5,sK6,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_639,c_23,c_22,c_21])).

cnf(c_644,plain,
    ( ~ r1_orders_2(sK6,sK1(sK5,sK6,X0),X1)
    | ~ r1_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,X1),X0) ),
    inference(renaming,[status(thm)],[c_643])).

cnf(c_2523,plain,
    ( ~ r1_orders_2(sK6,sK1(sK5,sK6,X0_51),X1_51)
    | ~ r1_waybel_0(sK5,sK6,X0_51)
    | ~ m1_subset_1(X1_51,u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,X1_51),X0_51) ),
    inference(subtyping,[status(esa)],[c_644])).

cnf(c_3156,plain,
    ( ~ r1_orders_2(sK6,sK1(sK5,sK6,X0_51),sK0(sK5,sK6,sK8,sK1(sK5,sK6,X1_51)))
    | ~ r1_waybel_0(sK5,sK6,X0_51)
    | ~ m1_subset_1(sK0(sK5,sK6,sK8,sK1(sK5,sK6,X1_51)),u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X1_51))),X0_51) ),
    inference(instantiation,[status(thm)],[c_2523])).

cnf(c_3172,plain,
    ( r1_orders_2(sK6,sK1(sK5,sK6,X0_51),sK0(sK5,sK6,sK8,sK1(sK5,sK6,X1_51))) != iProver_top
    | r1_waybel_0(sK5,sK6,X0_51) != iProver_top
    | m1_subset_1(sK0(sK5,sK6,sK8,sK1(sK5,sK6,X1_51)),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X1_51))),X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3156])).

cnf(c_3174,plain,
    ( r1_orders_2(sK6,sK1(sK5,sK6,sK7),sK0(sK5,sK6,sK8,sK1(sK5,sK6,sK7))) != iProver_top
    | r1_waybel_0(sK5,sK6,sK7) != iProver_top
    | m1_subset_1(sK0(sK5,sK6,sK8,sK1(sK5,sK6,sK7)),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,sK7))),sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3172])).

cnf(c_2902,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0_51,sK4(u1_struct_0(sK6)))),X0_51)
    | ~ v1_xboole_0(X1_51) ),
    inference(instantiation,[status(thm)],[c_2538])).

cnf(c_3052,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(sK8))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,sK7,sK4(u1_struct_0(sK6)))),sK7)
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2902])).

cnf(c_3053,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK8)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,sK7,sK4(u1_struct_0(sK6)))),sK7) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3052])).

cnf(c_2,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_579,plain,
    ( r1_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK0(sK5,sK6,X0,X1),u1_struct_0(sK6))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_2,c_20])).

cnf(c_583,plain,
    ( m1_subset_1(sK0(sK5,sK6,X0,X1),u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r1_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_579,c_23,c_22,c_21])).

cnf(c_584,plain,
    ( r1_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK0(sK5,sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_583])).

cnf(c_2526,plain,
    ( r1_waybel_0(sK5,sK6,X0_51)
    | ~ m1_subset_1(X1_51,u1_struct_0(sK6))
    | m1_subset_1(sK0(sK5,sK6,X0_51,X1_51),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_584])).

cnf(c_2754,plain,
    ( r1_waybel_0(sK5,sK6,X0_51)
    | m1_subset_1(sK0(sK5,sK6,X0_51,sK1(sK5,sK6,X1_51)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK1(sK5,sK6,X1_51),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2526])).

cnf(c_3026,plain,
    ( r1_waybel_0(sK5,sK6,sK8)
    | m1_subset_1(sK0(sK5,sK6,sK8,sK1(sK5,sK6,X0_51)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK1(sK5,sK6,X0_51),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2754])).

cnf(c_3027,plain,
    ( r1_waybel_0(sK5,sK6,sK8) = iProver_top
    | m1_subset_1(sK0(sK5,sK6,sK8,sK1(sK5,sK6,X0_51)),u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK1(sK5,sK6,X0_51),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3026])).

cnf(c_3029,plain,
    ( r1_waybel_0(sK5,sK6,sK8) = iProver_top
    | m1_subset_1(sK0(sK5,sK6,sK8,sK1(sK5,sK6,sK7)),u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK1(sK5,sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3027])).

cnf(c_1,plain,
    ( r1_orders_2(X0,X1,sK0(X2,X0,X3,X1))
    | r1_waybel_0(X2,X0,X3)
    | ~ l1_waybel_0(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_struct_0(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_619,plain,
    ( r1_orders_2(sK6,X0,sK0(sK5,sK6,X1,X0))
    | r1_waybel_0(sK5,sK6,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_1,c_20])).

cnf(c_623,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r1_waybel_0(sK5,sK6,X1)
    | r1_orders_2(sK6,X0,sK0(sK5,sK6,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_619,c_23,c_22,c_21])).

cnf(c_624,plain,
    ( r1_orders_2(sK6,X0,sK0(sK5,sK6,X1,X0))
    | r1_waybel_0(sK5,sK6,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_623])).

cnf(c_2524,plain,
    ( r1_orders_2(sK6,X0_51,sK0(sK5,sK6,X1_51,X0_51))
    | r1_waybel_0(sK5,sK6,X1_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_624])).

cnf(c_2832,plain,
    ( r1_orders_2(sK6,X0_51,sK0(sK5,sK6,sK8,X0_51))
    | r1_waybel_0(sK5,sK6,sK8)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2524])).

cnf(c_2991,plain,
    ( r1_orders_2(sK6,sK1(sK5,sK6,X0_51),sK0(sK5,sK6,sK8,sK1(sK5,sK6,X0_51)))
    | r1_waybel_0(sK5,sK6,sK8)
    | ~ m1_subset_1(sK1(sK5,sK6,X0_51),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2832])).

cnf(c_2992,plain,
    ( r1_orders_2(sK6,sK1(sK5,sK6,X0_51),sK0(sK5,sK6,sK8,sK1(sK5,sK6,X0_51))) = iProver_top
    | r1_waybel_0(sK5,sK6,sK8) = iProver_top
    | m1_subset_1(sK1(sK5,sK6,X0_51),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2991])).

cnf(c_2994,plain,
    ( r1_orders_2(sK6,sK1(sK5,sK6,sK7),sK0(sK5,sK6,sK8,sK1(sK5,sK6,sK7))) = iProver_top
    | r1_waybel_0(sK5,sK6,sK8) = iProver_top
    | m1_subset_1(sK1(sK5,sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2992])).

cnf(c_0,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_599,plain,
    ( r1_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X0,X1)),X0)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_0,c_20])).

cnf(c_603,plain,
    ( ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r1_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_599,c_23,c_22,c_21])).

cnf(c_604,plain,
    ( r1_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X0,X1)),X0) ),
    inference(renaming,[status(thm)],[c_603])).

cnf(c_2525,plain,
    ( r1_waybel_0(sK5,sK6,X0_51)
    | ~ m1_subset_1(X1_51,u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X0_51,X1_51)),X0_51) ),
    inference(subtyping,[status(esa)],[c_604])).

cnf(c_2827,plain,
    ( r1_waybel_0(sK5,sK6,sK8)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,X0_51)),sK8) ),
    inference(instantiation,[status(thm)],[c_2525])).

cnf(c_2951,plain,
    ( r1_waybel_0(sK5,sK6,sK8)
    | ~ m1_subset_1(sK1(sK5,sK6,X0_51),u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X0_51))),sK8) ),
    inference(instantiation,[status(thm)],[c_2827])).

cnf(c_2952,plain,
    ( r1_waybel_0(sK5,sK6,sK8) = iProver_top
    | m1_subset_1(sK1(sK5,sK6,X0_51),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,X0_51))),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2951])).

cnf(c_2954,plain,
    ( r1_waybel_0(sK5,sK6,sK8) = iProver_top
    | m1_subset_1(sK1(sK5,sK6,sK7),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,sK8,sK1(sK5,sK6,sK7))),sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2952])).

cnf(c_8,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | r1_orders_2(X1,X3,sK3(X0,X1,X2,X3))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_482,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | r1_orders_2(sK6,X1,sK3(sK5,sK6,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_8,c_20])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r1_orders_2(sK6,X1,sK3(sK5,sK6,X0,X1))
    | ~ r2_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_23,c_22,c_21])).

cnf(c_487,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | r1_orders_2(sK6,X1,sK3(sK5,sK6,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_486])).

cnf(c_2531,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0_51)
    | r1_orders_2(sK6,X1_51,sK3(sK5,sK6,X0_51,X1_51))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_487])).

cnf(c_2711,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0_51)
    | r1_orders_2(sK6,sK2(sK5,sK6,sK8),sK3(sK5,sK6,X0_51,sK2(sK5,sK6,sK8)))
    | ~ m1_subset_1(sK2(sK5,sK6,sK8),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2531])).

cnf(c_2722,plain,
    ( r2_waybel_0(sK5,sK6,X0_51) != iProver_top
    | r1_orders_2(sK6,sK2(sK5,sK6,sK8),sK3(sK5,sK6,X0_51,sK2(sK5,sK6,sK8))) = iProver_top
    | m1_subset_1(sK2(sK5,sK6,sK8),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2711])).

cnf(c_2724,plain,
    ( r2_waybel_0(sK5,sK6,sK7) != iProver_top
    | r1_orders_2(sK6,sK2(sK5,sK6,sK8),sK3(sK5,sK6,sK7,sK2(sK5,sK6,sK8))) = iProver_top
    | m1_subset_1(sK2(sK5,sK6,sK8),u1_struct_0(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2722])).

cnf(c_7,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_502,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0,X1)),X0)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_7,c_20])).

cnf(c_506,plain,
    ( r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_23,c_22,c_21])).

cnf(c_507,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0,X1)),X0) ),
    inference(renaming,[status(thm)],[c_506])).

cnf(c_2530,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0_51)
    | ~ m1_subset_1(X1_51,u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0_51,X1_51)),X0_51) ),
    inference(subtyping,[status(esa)],[c_507])).

cnf(c_2712,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0_51)
    | ~ m1_subset_1(sK2(sK5,sK6,sK8),u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0_51,sK2(sK5,sK6,sK8))),X0_51) ),
    inference(instantiation,[status(thm)],[c_2530])).

cnf(c_2718,plain,
    ( r2_waybel_0(sK5,sK6,X0_51) != iProver_top
    | m1_subset_1(sK2(sK5,sK6,sK8),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0_51,sK2(sK5,sK6,sK8))),X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2712])).

cnf(c_2720,plain,
    ( r2_waybel_0(sK5,sK6,sK7) != iProver_top
    | m1_subset_1(sK2(sK5,sK6,sK8),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,sK7,sK2(sK5,sK6,sK8))),sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2718])).

cnf(c_9,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_462,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK3(sK5,sK6,X0,X1),u1_struct_0(sK6))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_9,c_20])).

cnf(c_466,plain,
    ( m1_subset_1(sK3(sK5,sK6,X0,X1),u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_23,c_22,c_21])).

cnf(c_467,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK3(sK5,sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_466])).

cnf(c_2532,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0_51)
    | ~ m1_subset_1(X1_51,u1_struct_0(sK6))
    | m1_subset_1(sK3(sK5,sK6,X0_51,X1_51),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_467])).

cnf(c_2713,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0_51)
    | m1_subset_1(sK3(sK5,sK6,X0_51,sK2(sK5,sK6,sK8)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK5,sK6,sK8),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2532])).

cnf(c_2714,plain,
    ( r2_waybel_0(sK5,sK6,X0_51) != iProver_top
    | m1_subset_1(sK3(sK5,sK6,X0_51,sK2(sK5,sK6,sK8)),u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK2(sK5,sK6,sK8),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2713])).

cnf(c_2716,plain,
    ( r2_waybel_0(sK5,sK6,sK7) != iProver_top
    | m1_subset_1(sK3(sK5,sK6,sK7,sK2(sK5,sK6,sK8)),u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK2(sK5,sK6,sK8),u1_struct_0(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2714])).

cnf(c_2677,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0_51)
    | ~ m1_subset_1(sK4(u1_struct_0(sK6)),u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0_51,sK4(u1_struct_0(sK6)))),X0_51) ),
    inference(instantiation,[status(thm)],[c_2530])).

cnf(c_2685,plain,
    ( r2_waybel_0(sK5,sK6,X0_51) != iProver_top
    | m1_subset_1(sK4(u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0_51,sK4(u1_struct_0(sK6)))),X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2677])).

cnf(c_2687,plain,
    ( r2_waybel_0(sK5,sK6,sK7) != iProver_top
    | m1_subset_1(sK4(u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,sK7,sK4(u1_struct_0(sK6)))),sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2685])).

cnf(c_10,plain,
    ( m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2541,plain,
    ( m1_subset_1(sK4(X0_51),X0_51) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2674,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2541])).

cnf(c_2679,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2674])).

cnf(c_6,plain,
    ( r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_522,plain,
    ( r2_waybel_0(sK5,sK6,X0)
    | m1_subset_1(sK2(sK5,sK6,X0),u1_struct_0(sK6))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_6,c_20])).

cnf(c_526,plain,
    ( m1_subset_1(sK2(sK5,sK6,X0),u1_struct_0(sK6))
    | r2_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_522,c_23,c_22,c_21])).

cnf(c_527,plain,
    ( r2_waybel_0(sK5,sK6,X0)
    | m1_subset_1(sK2(sK5,sK6,X0),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_526])).

cnf(c_2529,plain,
    ( r2_waybel_0(sK5,sK6,X0_51)
    | m1_subset_1(sK2(sK5,sK6,X0_51),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_527])).

cnf(c_2646,plain,
    ( r2_waybel_0(sK5,sK6,sK8)
    | m1_subset_1(sK2(sK5,sK6,sK8),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2529])).

cnf(c_2647,plain,
    ( r2_waybel_0(sK5,sK6,sK8) = iProver_top
    | m1_subset_1(sK2(sK5,sK6,sK8),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2646])).

cnf(c_15,negated_conjecture,
    ( ~ r2_waybel_0(sK5,sK6,sK8)
    | ~ r1_waybel_0(sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1436,plain,
    ( ~ r1_waybel_0(sK5,sK6,sK8)
    | m1_subset_1(sK2(sK5,sK6,sK8),u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_15,c_527])).

cnf(c_1437,plain,
    ( r1_waybel_0(sK5,sK6,sK8) != iProver_top
    | m1_subset_1(sK2(sK5,sK6,sK8),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1436])).

cnf(c_16,negated_conjecture,
    ( ~ r2_waybel_0(sK5,sK6,sK8)
    | r1_waybel_0(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_4,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_562,plain,
    ( ~ r1_waybel_0(sK5,sK6,X0)
    | m1_subset_1(sK1(sK5,sK6,X0),u1_struct_0(sK6))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_4,c_20])).

cnf(c_566,plain,
    ( m1_subset_1(sK1(sK5,sK6,X0),u1_struct_0(sK6))
    | ~ r1_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_562,c_23,c_22,c_21])).

cnf(c_567,plain,
    ( ~ r1_waybel_0(sK5,sK6,X0)
    | m1_subset_1(sK1(sK5,sK6,X0),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_566])).

cnf(c_1194,plain,
    ( ~ r2_waybel_0(sK5,sK6,sK8)
    | m1_subset_1(sK1(sK5,sK6,sK7),u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_16,c_567])).

cnf(c_1195,plain,
    ( r2_waybel_0(sK5,sK6,sK8) != iProver_top
    | m1_subset_1(sK1(sK5,sK6,sK7),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1194])).

cnf(c_18,negated_conjecture,
    ( r2_waybel_0(sK5,sK6,sK7)
    | r1_waybel_0(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1168,plain,
    ( r2_waybel_0(sK5,sK6,sK7)
    | m1_subset_1(sK1(sK5,sK6,sK7),u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_18,c_567])).

cnf(c_1169,plain,
    ( r2_waybel_0(sK5,sK6,sK7) = iProver_top
    | m1_subset_1(sK1(sK5,sK6,sK7),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1168])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK7,sK8) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_251,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK8)) ),
    inference(resolution,[status(thm)],[c_12,c_19])).

cnf(c_252,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_251])).

cnf(c_32,plain,
    ( r2_waybel_0(sK5,sK6,sK8) != iProver_top
    | r1_waybel_0(sK5,sK6,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_31,plain,
    ( r2_waybel_0(sK5,sK6,sK8) != iProver_top
    | r1_waybel_0(sK5,sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( r2_waybel_0(sK5,sK6,sK7)
    | ~ r1_waybel_0(sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_30,plain,
    ( r2_waybel_0(sK5,sK6,sK7) = iProver_top
    | r1_waybel_0(sK5,sK6,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_29,plain,
    ( r2_waybel_0(sK5,sK6,sK7) = iProver_top
    | r1_waybel_0(sK5,sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4920,c_4769,c_3971,c_3703,c_3684,c_3607,c_3174,c_3053,c_3029,c_2994,c_2954,c_2724,c_2720,c_2716,c_2687,c_2679,c_2647,c_1437,c_1195,c_1169,c_252,c_32,c_31,c_30,c_29])).


%------------------------------------------------------------------------------
