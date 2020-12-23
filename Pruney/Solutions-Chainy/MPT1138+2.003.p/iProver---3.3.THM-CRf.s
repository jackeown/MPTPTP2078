%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:00 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  141 (1059 expanded)
%              Number of clauses        :   87 ( 274 expanded)
%              Number of leaves         :   14 ( 356 expanded)
%              Depth                    :   21
%              Number of atoms          :  519 (6780 expanded)
%              Number of equality atoms :  136 ( 319 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                     => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X1,X3)
                  & r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X1,X3)
                  & r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r1_orders_2(X0,X2,X3)
          & r1_orders_2(X0,X1,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK8)
        & r1_orders_2(X0,X2,sK8)
        & r1_orders_2(X0,X1,X2)
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X1,X3)
              & r1_orders_2(X0,X2,X3)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r1_orders_2(X0,X1,X3)
            & r1_orders_2(X0,sK7,X3)
            & r1_orders_2(X0,X1,sK7)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X1,X3)
                  & r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_orders_2(X0,sK6,X3)
                & r1_orders_2(X0,X2,X3)
                & r1_orders_2(X0,sK6,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(sK5,X1,X3)
                  & r1_orders_2(sK5,X2,X3)
                  & r1_orders_2(sK5,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK5)) )
              & m1_subset_1(X2,u1_struct_0(sK5)) )
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l1_orders_2(sK5)
      & v4_orders_2(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_orders_2(sK5,sK6,sK8)
    & r1_orders_2(sK5,sK7,sK8)
    & r1_orders_2(sK5,sK6,sK7)
    & m1_subset_1(sK8,u1_struct_0(sK5))
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l1_orders_2(sK5)
    & v4_orders_2(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f19,f33,f32,f31,f30])).

fof(f55,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f11])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
     => ( r2_hidden(sK1(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(sK1(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f22])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X2)
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    r1_orders_2(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f34])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)) = X0
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    r1_orders_2(sK5,sK7,sK8) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f34])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v4_orders_2(X0)
          | ~ r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v4_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0] :
      ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => r2_hidden(k4_tarski(X2,X4),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ? [X2,X3,X4] :
                ( ~ r2_hidden(k4_tarski(X2,X4),X0)
                & r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3,X4] :
                ( r2_hidden(k4_tarski(X2,X4),X0)
                | ~ r2_hidden(k4_tarski(X3,X4),X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ? [X2,X3,X4] :
                ( ~ r2_hidden(k4_tarski(X2,X4),X0)
                & r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2,X3,X4] :
          ( ~ r2_hidden(k4_tarski(X2,X4),X0)
          & r2_hidden(k4_tarski(X3,X4),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X4,X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
              & r2_hidden(sK4(X0,X1),X1)
              & r2_hidden(sK3(X0,X1),X1)
              & r2_hidden(sK2(X0,X1),X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f26])).

fof(f42,plain,(
    ! [X6,X0,X7,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X7),X0)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f61,plain,(
    ~ r1_orders_2(sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_18,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_25,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_306,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_307,plain,
    ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_2210,plain,
    ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(sK0(X3,X1,X2),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2223,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(sK0(X3,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3104,plain,
    ( r2_hidden(X0,u1_orders_2(sK5)) != iProver_top
    | r2_hidden(sK0(X0,u1_struct_0(sK5),u1_struct_0(sK5)),u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_2223])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(sK1(X3,X1,X2),X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2224,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(sK1(X3,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3421,plain,
    ( r2_hidden(X0,u1_orders_2(sK5)) != iProver_top
    | r2_hidden(sK1(X0,u1_struct_0(sK5),u1_struct_0(sK5)),u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_2224])).

cnf(c_21,negated_conjecture,
    ( r1_orders_2(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_17,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_313,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_314,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK5))
    | sK7 != X0
    | sK6 != X1
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_314])).

cnf(c_405,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5)) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_407,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_24,c_23])).

cnf(c_2207,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X0)
    | k4_tarski(sK0(X3,X1,X2),sK1(X3,X1,X2)) = X3 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2222,plain,
    ( k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)) = X0
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X0,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5703,plain,
    ( k4_tarski(sK0(X0,u1_struct_0(sK5),u1_struct_0(sK5)),sK1(X0,u1_struct_0(sK5),u1_struct_0(sK5))) = X0
    | r2_hidden(X0,u1_orders_2(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_2222])).

cnf(c_5716,plain,
    ( k4_tarski(sK0(k4_tarski(sK6,sK7),u1_struct_0(sK5),u1_struct_0(sK5)),sK1(k4_tarski(sK6,sK7),u1_struct_0(sK5),u1_struct_0(sK5))) = k4_tarski(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_2207,c_5703])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2228,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5974,plain,
    ( r2_hidden(sK0(k4_tarski(sK6,sK7),u1_struct_0(sK5),u1_struct_0(sK5)),X0) != iProver_top
    | r2_hidden(sK1(k4_tarski(sK6,sK7),u1_struct_0(sK5),u1_struct_0(sK5)),X1) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5716,c_2228])).

cnf(c_6147,plain,
    ( r2_hidden(sK0(k4_tarski(sK6,sK7),u1_struct_0(sK5),u1_struct_0(sK5)),X0) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(X0,u1_struct_0(sK5))) = iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3421,c_5974])).

cnf(c_29,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_30,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_406,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_6152,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(X0,u1_struct_0(sK5))) = iProver_top
    | r2_hidden(sK0(k4_tarski(sK6,sK7),u1_struct_0(sK5),u1_struct_0(sK5)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6147,c_29,c_30,c_406])).

cnf(c_6153,plain,
    ( r2_hidden(sK0(k4_tarski(sK6,sK7),u1_struct_0(sK5),u1_struct_0(sK5)),X0) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(X0,u1_struct_0(sK5))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6152])).

cnf(c_6160,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))) = iProver_top
    | r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3104,c_6153])).

cnf(c_6163,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6160,c_29,c_30,c_406])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2226,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6169,plain,
    ( r2_hidden(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6163,c_2226])).

cnf(c_20,negated_conjecture,
    ( r1_orders_2(sK5,sK7,sK8) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK5))
    | sK7 != X1
    | sK8 != X0
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_314])).

cnf(c_394,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | r2_hidden(k4_tarski(sK7,sK8),u1_orders_2(sK5)) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_396,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),u1_orders_2(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_23,c_22])).

cnf(c_2208,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),u1_orders_2(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_5715,plain,
    ( k4_tarski(sK0(k4_tarski(sK7,sK8),u1_struct_0(sK5),u1_struct_0(sK5)),sK1(k4_tarski(sK7,sK8),u1_struct_0(sK5),u1_struct_0(sK5))) = k4_tarski(sK7,sK8) ),
    inference(superposition,[status(thm)],[c_2208,c_5703])).

cnf(c_5927,plain,
    ( r2_hidden(sK0(k4_tarski(sK7,sK8),u1_struct_0(sK5),u1_struct_0(sK5)),X0) != iProver_top
    | r2_hidden(sK1(k4_tarski(sK7,sK8),u1_struct_0(sK5),u1_struct_0(sK5)),X1) != iProver_top
    | r2_hidden(k4_tarski(sK7,sK8),k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5715,c_2228])).

cnf(c_6085,plain,
    ( r2_hidden(sK0(k4_tarski(sK7,sK8),u1_struct_0(sK5),u1_struct_0(sK5)),X0) != iProver_top
    | r2_hidden(k4_tarski(sK7,sK8),k2_zfmisc_1(X0,u1_struct_0(sK5))) = iProver_top
    | r2_hidden(k4_tarski(sK7,sK8),u1_orders_2(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3421,c_5927])).

cnf(c_31,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_395,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(k4_tarski(sK7,sK8),u1_orders_2(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_6090,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),k2_zfmisc_1(X0,u1_struct_0(sK5))) = iProver_top
    | r2_hidden(sK0(k4_tarski(sK7,sK8),u1_struct_0(sK5),u1_struct_0(sK5)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6085,c_30,c_31,c_395])).

cnf(c_6091,plain,
    ( r2_hidden(sK0(k4_tarski(sK7,sK8),u1_struct_0(sK5),u1_struct_0(sK5)),X0) != iProver_top
    | r2_hidden(k4_tarski(sK7,sK8),k2_zfmisc_1(X0,u1_struct_0(sK5))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6090])).

cnf(c_6098,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))) = iProver_top
    | r2_hidden(k4_tarski(sK7,sK8),u1_orders_2(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3104,c_6091])).

cnf(c_6101,plain,
    ( r2_hidden(k4_tarski(sK7,sK8),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6098,c_30,c_31,c_395])).

cnf(c_6107,plain,
    ( r2_hidden(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6101,c_2226])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2227,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6106,plain,
    ( r2_hidden(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6101,c_2227])).

cnf(c_15,plain,
    ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v4_orders_2(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_26,negated_conjecture,
    ( v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_293,plain,
    ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_294,plain,
    ( r8_relat_2(u1_orders_2(sK5),u1_struct_0(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_45,plain,
    ( r8_relat_2(u1_orders_2(sK5),u1_struct_0(sK5))
    | ~ l1_orders_2(sK5)
    | ~ v4_orders_2(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_296,plain,
    ( r8_relat_2(u1_orders_2(sK5),u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_294,c_26,c_25,c_45])).

cnf(c_2211,plain,
    ( r8_relat_2(u1_orders_2(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_13,plain,
    ( ~ r8_relat_2(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X4,X1)
    | ~ r2_hidden(k4_tarski(X3,X2),X0)
    | ~ r2_hidden(k4_tarski(X4,X3),X0)
    | r2_hidden(k4_tarski(X4,X2),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2215,plain,
    ( r8_relat_2(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X3,X1) != iProver_top
    | r2_hidden(X4,X1) != iProver_top
    | r2_hidden(k4_tarski(X3,X2),X0) != iProver_top
    | r2_hidden(k4_tarski(X4,X3),X0) != iProver_top
    | r2_hidden(k4_tarski(X4,X2),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3566,plain,
    ( r8_relat_2(u1_orders_2(sK5),X0) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(k4_tarski(X1,sK7),u1_orders_2(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X1,sK8),u1_orders_2(sK5)) = iProver_top
    | r2_hidden(sK7,X0) != iProver_top
    | r2_hidden(sK8,X0) != iProver_top
    | v1_relat_1(u1_orders_2(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2208,c_2215])).

cnf(c_28,plain,
    ( l1_orders_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_35,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_37,plain,
    ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) = iProver_top
    | l1_orders_2(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2388,plain,
    ( ~ m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | v1_relat_1(u1_orders_2(sK5)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2389,plain,
    ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) != iProver_top
    | v1_relat_1(u1_orders_2(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2388])).

cnf(c_4652,plain,
    ( r2_hidden(sK8,X0) != iProver_top
    | r2_hidden(sK7,X0) != iProver_top
    | r2_hidden(k4_tarski(X1,sK8),u1_orders_2(sK5)) = iProver_top
    | r2_hidden(k4_tarski(X1,sK7),u1_orders_2(sK5)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r8_relat_2(u1_orders_2(sK5),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3566,c_28,c_37,c_2389])).

cnf(c_4653,plain,
    ( r8_relat_2(u1_orders_2(sK5),X0) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(k4_tarski(X1,sK7),u1_orders_2(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X1,sK8),u1_orders_2(sK5)) = iProver_top
    | r2_hidden(sK7,X0) != iProver_top
    | r2_hidden(sK8,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4652])).

cnf(c_4664,plain,
    ( r8_relat_2(u1_orders_2(sK5),X0) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK8),u1_orders_2(sK5)) = iProver_top
    | r2_hidden(sK7,X0) != iProver_top
    | r2_hidden(sK8,X0) != iProver_top
    | r2_hidden(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2207,c_4653])).

cnf(c_19,negated_conjecture,
    ( ~ r1_orders_2(sK5,sK6,sK8) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_16,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_331,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_332,plain,
    ( r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK5))
    | sK8 != X0
    | sK6 != X1
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_332])).

cnf(c_383,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(k4_tarski(sK6,sK8),u1_orders_2(sK5)) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_384,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(k4_tarski(sK6,sK8),u1_orders_2(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_4669,plain,
    ( r8_relat_2(u1_orders_2(sK5),X0) != iProver_top
    | r2_hidden(sK7,X0) != iProver_top
    | r2_hidden(sK8,X0) != iProver_top
    | r2_hidden(sK6,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4664,c_29,c_31,c_384])).

cnf(c_4679,plain,
    ( r2_hidden(sK7,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK8,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2211,c_4669])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6169,c_6107,c_6106,c_4679])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:15:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.05/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/0.94  
% 3.05/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.05/0.94  
% 3.05/0.94  ------  iProver source info
% 3.05/0.94  
% 3.05/0.94  git: date: 2020-06-30 10:37:57 +0100
% 3.05/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.05/0.94  git: non_committed_changes: false
% 3.05/0.94  git: last_make_outside_of_git: false
% 3.05/0.94  
% 3.05/0.94  ------ 
% 3.05/0.94  
% 3.05/0.94  ------ Input Options
% 3.05/0.94  
% 3.05/0.94  --out_options                           all
% 3.05/0.94  --tptp_safe_out                         true
% 3.05/0.94  --problem_path                          ""
% 3.05/0.94  --include_path                          ""
% 3.05/0.94  --clausifier                            res/vclausify_rel
% 3.05/0.94  --clausifier_options                    --mode clausify
% 3.05/0.94  --stdin                                 false
% 3.05/0.94  --stats_out                             all
% 3.05/0.94  
% 3.05/0.94  ------ General Options
% 3.05/0.94  
% 3.05/0.94  --fof                                   false
% 3.05/0.94  --time_out_real                         305.
% 3.05/0.94  --time_out_virtual                      -1.
% 3.05/0.94  --symbol_type_check                     false
% 3.05/0.94  --clausify_out                          false
% 3.05/0.94  --sig_cnt_out                           false
% 3.05/0.94  --trig_cnt_out                          false
% 3.05/0.94  --trig_cnt_out_tolerance                1.
% 3.05/0.94  --trig_cnt_out_sk_spl                   false
% 3.05/0.94  --abstr_cl_out                          false
% 3.05/0.94  
% 3.05/0.94  ------ Global Options
% 3.05/0.94  
% 3.05/0.94  --schedule                              default
% 3.05/0.94  --add_important_lit                     false
% 3.05/0.94  --prop_solver_per_cl                    1000
% 3.05/0.94  --min_unsat_core                        false
% 3.05/0.94  --soft_assumptions                      false
% 3.05/0.94  --soft_lemma_size                       3
% 3.05/0.94  --prop_impl_unit_size                   0
% 3.05/0.94  --prop_impl_unit                        []
% 3.05/0.94  --share_sel_clauses                     true
% 3.05/0.94  --reset_solvers                         false
% 3.05/0.94  --bc_imp_inh                            [conj_cone]
% 3.05/0.94  --conj_cone_tolerance                   3.
% 3.05/0.94  --extra_neg_conj                        none
% 3.05/0.94  --large_theory_mode                     true
% 3.05/0.94  --prolific_symb_bound                   200
% 3.05/0.94  --lt_threshold                          2000
% 3.05/0.94  --clause_weak_htbl                      true
% 3.05/0.94  --gc_record_bc_elim                     false
% 3.05/0.94  
% 3.05/0.94  ------ Preprocessing Options
% 3.05/0.94  
% 3.05/0.94  --preprocessing_flag                    true
% 3.05/0.94  --time_out_prep_mult                    0.1
% 3.05/0.94  --splitting_mode                        input
% 3.05/0.94  --splitting_grd                         true
% 3.05/0.94  --splitting_cvd                         false
% 3.05/0.94  --splitting_cvd_svl                     false
% 3.05/0.94  --splitting_nvd                         32
% 3.05/0.94  --sub_typing                            true
% 3.05/0.94  --prep_gs_sim                           true
% 3.05/0.94  --prep_unflatten                        true
% 3.05/0.94  --prep_res_sim                          true
% 3.05/0.94  --prep_upred                            true
% 3.05/0.94  --prep_sem_filter                       exhaustive
% 3.05/0.94  --prep_sem_filter_out                   false
% 3.05/0.94  --pred_elim                             true
% 3.05/0.94  --res_sim_input                         true
% 3.05/0.94  --eq_ax_congr_red                       true
% 3.05/0.94  --pure_diseq_elim                       true
% 3.05/0.94  --brand_transform                       false
% 3.05/0.94  --non_eq_to_eq                          false
% 3.05/0.94  --prep_def_merge                        true
% 3.05/0.94  --prep_def_merge_prop_impl              false
% 3.05/0.94  --prep_def_merge_mbd                    true
% 3.05/0.94  --prep_def_merge_tr_red                 false
% 3.05/0.94  --prep_def_merge_tr_cl                  false
% 3.05/0.94  --smt_preprocessing                     true
% 3.05/0.94  --smt_ac_axioms                         fast
% 3.05/0.94  --preprocessed_out                      false
% 3.05/0.94  --preprocessed_stats                    false
% 3.05/0.94  
% 3.05/0.94  ------ Abstraction refinement Options
% 3.05/0.94  
% 3.05/0.94  --abstr_ref                             []
% 3.05/0.94  --abstr_ref_prep                        false
% 3.05/0.94  --abstr_ref_until_sat                   false
% 3.05/0.94  --abstr_ref_sig_restrict                funpre
% 3.05/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/0.94  --abstr_ref_under                       []
% 3.05/0.94  
% 3.05/0.94  ------ SAT Options
% 3.05/0.94  
% 3.05/0.94  --sat_mode                              false
% 3.05/0.94  --sat_fm_restart_options                ""
% 3.05/0.94  --sat_gr_def                            false
% 3.05/0.94  --sat_epr_types                         true
% 3.05/0.94  --sat_non_cyclic_types                  false
% 3.05/0.94  --sat_finite_models                     false
% 3.05/0.94  --sat_fm_lemmas                         false
% 3.05/0.94  --sat_fm_prep                           false
% 3.05/0.94  --sat_fm_uc_incr                        true
% 3.05/0.94  --sat_out_model                         small
% 3.05/0.94  --sat_out_clauses                       false
% 3.05/0.94  
% 3.05/0.94  ------ QBF Options
% 3.05/0.94  
% 3.05/0.94  --qbf_mode                              false
% 3.05/0.94  --qbf_elim_univ                         false
% 3.05/0.94  --qbf_dom_inst                          none
% 3.05/0.94  --qbf_dom_pre_inst                      false
% 3.05/0.94  --qbf_sk_in                             false
% 3.05/0.94  --qbf_pred_elim                         true
% 3.05/0.94  --qbf_split                             512
% 3.05/0.94  
% 3.05/0.94  ------ BMC1 Options
% 3.05/0.94  
% 3.05/0.94  --bmc1_incremental                      false
% 3.05/0.94  --bmc1_axioms                           reachable_all
% 3.05/0.94  --bmc1_min_bound                        0
% 3.05/0.94  --bmc1_max_bound                        -1
% 3.05/0.94  --bmc1_max_bound_default                -1
% 3.05/0.94  --bmc1_symbol_reachability              true
% 3.05/0.94  --bmc1_property_lemmas                  false
% 3.05/0.94  --bmc1_k_induction                      false
% 3.05/0.94  --bmc1_non_equiv_states                 false
% 3.05/0.94  --bmc1_deadlock                         false
% 3.05/0.94  --bmc1_ucm                              false
% 3.05/0.94  --bmc1_add_unsat_core                   none
% 3.05/0.94  --bmc1_unsat_core_children              false
% 3.05/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/0.94  --bmc1_out_stat                         full
% 3.05/0.94  --bmc1_ground_init                      false
% 3.05/0.94  --bmc1_pre_inst_next_state              false
% 3.05/0.94  --bmc1_pre_inst_state                   false
% 3.05/0.94  --bmc1_pre_inst_reach_state             false
% 3.05/0.94  --bmc1_out_unsat_core                   false
% 3.05/0.94  --bmc1_aig_witness_out                  false
% 3.05/0.94  --bmc1_verbose                          false
% 3.05/0.94  --bmc1_dump_clauses_tptp                false
% 3.05/0.94  --bmc1_dump_unsat_core_tptp             false
% 3.05/0.94  --bmc1_dump_file                        -
% 3.05/0.94  --bmc1_ucm_expand_uc_limit              128
% 3.05/0.94  --bmc1_ucm_n_expand_iterations          6
% 3.05/0.94  --bmc1_ucm_extend_mode                  1
% 3.05/0.94  --bmc1_ucm_init_mode                    2
% 3.05/0.94  --bmc1_ucm_cone_mode                    none
% 3.05/0.94  --bmc1_ucm_reduced_relation_type        0
% 3.05/0.94  --bmc1_ucm_relax_model                  4
% 3.05/0.94  --bmc1_ucm_full_tr_after_sat            true
% 3.05/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/0.94  --bmc1_ucm_layered_model                none
% 3.05/0.94  --bmc1_ucm_max_lemma_size               10
% 3.05/0.94  
% 3.05/0.94  ------ AIG Options
% 3.05/0.94  
% 3.05/0.94  --aig_mode                              false
% 3.05/0.94  
% 3.05/0.94  ------ Instantiation Options
% 3.05/0.94  
% 3.05/0.94  --instantiation_flag                    true
% 3.05/0.94  --inst_sos_flag                         false
% 3.05/0.94  --inst_sos_phase                        true
% 3.05/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/0.94  --inst_lit_sel_side                     num_symb
% 3.05/0.94  --inst_solver_per_active                1400
% 3.05/0.94  --inst_solver_calls_frac                1.
% 3.05/0.94  --inst_passive_queue_type               priority_queues
% 3.05/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/0.94  --inst_passive_queues_freq              [25;2]
% 3.05/0.94  --inst_dismatching                      true
% 3.05/0.94  --inst_eager_unprocessed_to_passive     true
% 3.05/0.94  --inst_prop_sim_given                   true
% 3.05/0.94  --inst_prop_sim_new                     false
% 3.05/0.94  --inst_subs_new                         false
% 3.05/0.94  --inst_eq_res_simp                      false
% 3.05/0.94  --inst_subs_given                       false
% 3.05/0.94  --inst_orphan_elimination               true
% 3.05/0.94  --inst_learning_loop_flag               true
% 3.05/0.94  --inst_learning_start                   3000
% 3.05/0.94  --inst_learning_factor                  2
% 3.05/0.94  --inst_start_prop_sim_after_learn       3
% 3.05/0.94  --inst_sel_renew                        solver
% 3.05/0.94  --inst_lit_activity_flag                true
% 3.05/0.94  --inst_restr_to_given                   false
% 3.05/0.94  --inst_activity_threshold               500
% 3.05/0.94  --inst_out_proof                        true
% 3.05/0.94  
% 3.05/0.94  ------ Resolution Options
% 3.05/0.94  
% 3.05/0.94  --resolution_flag                       true
% 3.05/0.94  --res_lit_sel                           adaptive
% 3.05/0.94  --res_lit_sel_side                      none
% 3.05/0.94  --res_ordering                          kbo
% 3.05/0.94  --res_to_prop_solver                    active
% 3.05/0.94  --res_prop_simpl_new                    false
% 3.05/0.94  --res_prop_simpl_given                  true
% 3.05/0.94  --res_passive_queue_type                priority_queues
% 3.05/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/0.94  --res_passive_queues_freq               [15;5]
% 3.05/0.94  --res_forward_subs                      full
% 3.05/0.94  --res_backward_subs                     full
% 3.05/0.94  --res_forward_subs_resolution           true
% 3.05/0.94  --res_backward_subs_resolution          true
% 3.05/0.94  --res_orphan_elimination                true
% 3.05/0.94  --res_time_limit                        2.
% 3.05/0.94  --res_out_proof                         true
% 3.05/0.94  
% 3.05/0.94  ------ Superposition Options
% 3.05/0.94  
% 3.05/0.94  --superposition_flag                    true
% 3.05/0.94  --sup_passive_queue_type                priority_queues
% 3.05/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/0.94  --sup_passive_queues_freq               [8;1;4]
% 3.05/0.94  --demod_completeness_check              fast
% 3.05/0.94  --demod_use_ground                      true
% 3.05/0.94  --sup_to_prop_solver                    passive
% 3.05/0.94  --sup_prop_simpl_new                    true
% 3.05/0.94  --sup_prop_simpl_given                  true
% 3.05/0.94  --sup_fun_splitting                     false
% 3.05/0.94  --sup_smt_interval                      50000
% 3.05/0.94  
% 3.05/0.94  ------ Superposition Simplification Setup
% 3.05/0.94  
% 3.05/0.94  --sup_indices_passive                   []
% 3.05/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.94  --sup_full_bw                           [BwDemod]
% 3.05/0.94  --sup_immed_triv                        [TrivRules]
% 3.05/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.94  --sup_immed_bw_main                     []
% 3.05/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.94  
% 3.05/0.94  ------ Combination Options
% 3.05/0.94  
% 3.05/0.94  --comb_res_mult                         3
% 3.05/0.94  --comb_sup_mult                         2
% 3.05/0.94  --comb_inst_mult                        10
% 3.05/0.94  
% 3.05/0.94  ------ Debug Options
% 3.05/0.94  
% 3.05/0.94  --dbg_backtrace                         false
% 3.05/0.94  --dbg_dump_prop_clauses                 false
% 3.05/0.94  --dbg_dump_prop_clauses_file            -
% 3.05/0.94  --dbg_out_stat                          false
% 3.05/0.94  ------ Parsing...
% 3.05/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.05/0.94  
% 3.05/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.05/0.94  
% 3.05/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.05/0.94  
% 3.05/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.05/0.94  ------ Proving...
% 3.05/0.94  ------ Problem Properties 
% 3.05/0.94  
% 3.05/0.94  
% 3.05/0.94  clauses                                 24
% 3.05/0.94  conjectures                             3
% 3.05/0.94  EPR                                     2
% 3.05/0.94  Horn                                    19
% 3.05/0.94  unary                                   10
% 3.05/0.94  binary                                  3
% 3.05/0.94  lits                                    54
% 3.05/0.94  lits eq                                 3
% 3.05/0.94  fd_pure                                 0
% 3.05/0.94  fd_pseudo                               0
% 3.05/0.94  fd_cond                                 0
% 3.05/0.94  fd_pseudo_cond                          0
% 3.05/0.94  AC symbols                              0
% 3.05/0.94  
% 3.05/0.94  ------ Schedule dynamic 5 is on 
% 3.05/0.94  
% 3.05/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.05/0.94  
% 3.05/0.94  
% 3.05/0.94  ------ 
% 3.05/0.94  Current options:
% 3.05/0.94  ------ 
% 3.05/0.94  
% 3.05/0.94  ------ Input Options
% 3.05/0.94  
% 3.05/0.94  --out_options                           all
% 3.05/0.94  --tptp_safe_out                         true
% 3.05/0.94  --problem_path                          ""
% 3.05/0.94  --include_path                          ""
% 3.05/0.94  --clausifier                            res/vclausify_rel
% 3.05/0.94  --clausifier_options                    --mode clausify
% 3.05/0.94  --stdin                                 false
% 3.05/0.94  --stats_out                             all
% 3.05/0.94  
% 3.05/0.94  ------ General Options
% 3.05/0.94  
% 3.05/0.94  --fof                                   false
% 3.05/0.94  --time_out_real                         305.
% 3.05/0.94  --time_out_virtual                      -1.
% 3.05/0.94  --symbol_type_check                     false
% 3.05/0.94  --clausify_out                          false
% 3.05/0.94  --sig_cnt_out                           false
% 3.05/0.94  --trig_cnt_out                          false
% 3.05/0.94  --trig_cnt_out_tolerance                1.
% 3.05/0.94  --trig_cnt_out_sk_spl                   false
% 3.05/0.94  --abstr_cl_out                          false
% 3.05/0.94  
% 3.05/0.94  ------ Global Options
% 3.05/0.94  
% 3.05/0.94  --schedule                              default
% 3.05/0.94  --add_important_lit                     false
% 3.05/0.94  --prop_solver_per_cl                    1000
% 3.05/0.94  --min_unsat_core                        false
% 3.05/0.94  --soft_assumptions                      false
% 3.05/0.94  --soft_lemma_size                       3
% 3.05/0.94  --prop_impl_unit_size                   0
% 3.05/0.94  --prop_impl_unit                        []
% 3.05/0.94  --share_sel_clauses                     true
% 3.05/0.94  --reset_solvers                         false
% 3.05/0.94  --bc_imp_inh                            [conj_cone]
% 3.05/0.94  --conj_cone_tolerance                   3.
% 3.05/0.94  --extra_neg_conj                        none
% 3.05/0.94  --large_theory_mode                     true
% 3.05/0.94  --prolific_symb_bound                   200
% 3.05/0.94  --lt_threshold                          2000
% 3.05/0.94  --clause_weak_htbl                      true
% 3.05/0.94  --gc_record_bc_elim                     false
% 3.05/0.94  
% 3.05/0.94  ------ Preprocessing Options
% 3.05/0.94  
% 3.05/0.94  --preprocessing_flag                    true
% 3.05/0.94  --time_out_prep_mult                    0.1
% 3.05/0.94  --splitting_mode                        input
% 3.05/0.94  --splitting_grd                         true
% 3.05/0.94  --splitting_cvd                         false
% 3.05/0.94  --splitting_cvd_svl                     false
% 3.05/0.94  --splitting_nvd                         32
% 3.05/0.94  --sub_typing                            true
% 3.05/0.94  --prep_gs_sim                           true
% 3.05/0.94  --prep_unflatten                        true
% 3.05/0.94  --prep_res_sim                          true
% 3.05/0.94  --prep_upred                            true
% 3.05/0.94  --prep_sem_filter                       exhaustive
% 3.05/0.94  --prep_sem_filter_out                   false
% 3.05/0.94  --pred_elim                             true
% 3.05/0.94  --res_sim_input                         true
% 3.05/0.94  --eq_ax_congr_red                       true
% 3.05/0.94  --pure_diseq_elim                       true
% 3.05/0.94  --brand_transform                       false
% 3.05/0.94  --non_eq_to_eq                          false
% 3.05/0.94  --prep_def_merge                        true
% 3.05/0.94  --prep_def_merge_prop_impl              false
% 3.05/0.94  --prep_def_merge_mbd                    true
% 3.05/0.94  --prep_def_merge_tr_red                 false
% 3.05/0.94  --prep_def_merge_tr_cl                  false
% 3.05/0.94  --smt_preprocessing                     true
% 3.05/0.94  --smt_ac_axioms                         fast
% 3.05/0.94  --preprocessed_out                      false
% 3.05/0.94  --preprocessed_stats                    false
% 3.05/0.94  
% 3.05/0.94  ------ Abstraction refinement Options
% 3.05/0.94  
% 3.05/0.94  --abstr_ref                             []
% 3.05/0.94  --abstr_ref_prep                        false
% 3.05/0.94  --abstr_ref_until_sat                   false
% 3.05/0.94  --abstr_ref_sig_restrict                funpre
% 3.05/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/0.94  --abstr_ref_under                       []
% 3.05/0.94  
% 3.05/0.94  ------ SAT Options
% 3.05/0.94  
% 3.05/0.94  --sat_mode                              false
% 3.05/0.94  --sat_fm_restart_options                ""
% 3.05/0.94  --sat_gr_def                            false
% 3.05/0.94  --sat_epr_types                         true
% 3.05/0.94  --sat_non_cyclic_types                  false
% 3.05/0.94  --sat_finite_models                     false
% 3.05/0.94  --sat_fm_lemmas                         false
% 3.05/0.94  --sat_fm_prep                           false
% 3.05/0.94  --sat_fm_uc_incr                        true
% 3.05/0.94  --sat_out_model                         small
% 3.05/0.94  --sat_out_clauses                       false
% 3.05/0.94  
% 3.05/0.94  ------ QBF Options
% 3.05/0.94  
% 3.05/0.94  --qbf_mode                              false
% 3.05/0.94  --qbf_elim_univ                         false
% 3.05/0.94  --qbf_dom_inst                          none
% 3.05/0.94  --qbf_dom_pre_inst                      false
% 3.05/0.94  --qbf_sk_in                             false
% 3.05/0.94  --qbf_pred_elim                         true
% 3.05/0.94  --qbf_split                             512
% 3.05/0.94  
% 3.05/0.94  ------ BMC1 Options
% 3.05/0.94  
% 3.05/0.94  --bmc1_incremental                      false
% 3.05/0.94  --bmc1_axioms                           reachable_all
% 3.05/0.94  --bmc1_min_bound                        0
% 3.05/0.94  --bmc1_max_bound                        -1
% 3.05/0.94  --bmc1_max_bound_default                -1
% 3.05/0.94  --bmc1_symbol_reachability              true
% 3.05/0.94  --bmc1_property_lemmas                  false
% 3.05/0.94  --bmc1_k_induction                      false
% 3.05/0.94  --bmc1_non_equiv_states                 false
% 3.05/0.94  --bmc1_deadlock                         false
% 3.05/0.94  --bmc1_ucm                              false
% 3.05/0.94  --bmc1_add_unsat_core                   none
% 3.05/0.94  --bmc1_unsat_core_children              false
% 3.05/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/0.94  --bmc1_out_stat                         full
% 3.05/0.94  --bmc1_ground_init                      false
% 3.05/0.94  --bmc1_pre_inst_next_state              false
% 3.05/0.94  --bmc1_pre_inst_state                   false
% 3.05/0.94  --bmc1_pre_inst_reach_state             false
% 3.05/0.94  --bmc1_out_unsat_core                   false
% 3.05/0.94  --bmc1_aig_witness_out                  false
% 3.05/0.94  --bmc1_verbose                          false
% 3.05/0.94  --bmc1_dump_clauses_tptp                false
% 3.05/0.94  --bmc1_dump_unsat_core_tptp             false
% 3.05/0.94  --bmc1_dump_file                        -
% 3.05/0.94  --bmc1_ucm_expand_uc_limit              128
% 3.05/0.94  --bmc1_ucm_n_expand_iterations          6
% 3.05/0.94  --bmc1_ucm_extend_mode                  1
% 3.05/0.94  --bmc1_ucm_init_mode                    2
% 3.05/0.94  --bmc1_ucm_cone_mode                    none
% 3.05/0.94  --bmc1_ucm_reduced_relation_type        0
% 3.05/0.94  --bmc1_ucm_relax_model                  4
% 3.05/0.94  --bmc1_ucm_full_tr_after_sat            true
% 3.05/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/0.94  --bmc1_ucm_layered_model                none
% 3.05/0.94  --bmc1_ucm_max_lemma_size               10
% 3.05/0.94  
% 3.05/0.94  ------ AIG Options
% 3.05/0.94  
% 3.05/0.94  --aig_mode                              false
% 3.05/0.94  
% 3.05/0.94  ------ Instantiation Options
% 3.05/0.94  
% 3.05/0.94  --instantiation_flag                    true
% 3.05/0.94  --inst_sos_flag                         false
% 3.05/0.94  --inst_sos_phase                        true
% 3.05/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/0.94  --inst_lit_sel_side                     none
% 3.05/0.94  --inst_solver_per_active                1400
% 3.05/0.94  --inst_solver_calls_frac                1.
% 3.05/0.94  --inst_passive_queue_type               priority_queues
% 3.05/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/0.94  --inst_passive_queues_freq              [25;2]
% 3.05/0.94  --inst_dismatching                      true
% 3.05/0.94  --inst_eager_unprocessed_to_passive     true
% 3.05/0.94  --inst_prop_sim_given                   true
% 3.05/0.94  --inst_prop_sim_new                     false
% 3.05/0.94  --inst_subs_new                         false
% 3.05/0.94  --inst_eq_res_simp                      false
% 3.05/0.94  --inst_subs_given                       false
% 3.05/0.94  --inst_orphan_elimination               true
% 3.05/0.94  --inst_learning_loop_flag               true
% 3.05/0.94  --inst_learning_start                   3000
% 3.05/0.94  --inst_learning_factor                  2
% 3.05/0.94  --inst_start_prop_sim_after_learn       3
% 3.05/0.94  --inst_sel_renew                        solver
% 3.05/0.94  --inst_lit_activity_flag                true
% 3.05/0.94  --inst_restr_to_given                   false
% 3.05/0.94  --inst_activity_threshold               500
% 3.05/0.94  --inst_out_proof                        true
% 3.05/0.94  
% 3.05/0.94  ------ Resolution Options
% 3.05/0.94  
% 3.05/0.94  --resolution_flag                       false
% 3.05/0.94  --res_lit_sel                           adaptive
% 3.05/0.94  --res_lit_sel_side                      none
% 3.05/0.94  --res_ordering                          kbo
% 3.05/0.94  --res_to_prop_solver                    active
% 3.05/0.94  --res_prop_simpl_new                    false
% 3.05/0.94  --res_prop_simpl_given                  true
% 3.05/0.94  --res_passive_queue_type                priority_queues
% 3.05/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/0.94  --res_passive_queues_freq               [15;5]
% 3.05/0.94  --res_forward_subs                      full
% 3.05/0.94  --res_backward_subs                     full
% 3.05/0.94  --res_forward_subs_resolution           true
% 3.05/0.94  --res_backward_subs_resolution          true
% 3.05/0.94  --res_orphan_elimination                true
% 3.05/0.94  --res_time_limit                        2.
% 3.05/0.94  --res_out_proof                         true
% 3.05/0.94  
% 3.05/0.94  ------ Superposition Options
% 3.05/0.94  
% 3.05/0.94  --superposition_flag                    true
% 3.05/0.94  --sup_passive_queue_type                priority_queues
% 3.05/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/0.94  --sup_passive_queues_freq               [8;1;4]
% 3.05/0.94  --demod_completeness_check              fast
% 3.05/0.94  --demod_use_ground                      true
% 3.05/0.94  --sup_to_prop_solver                    passive
% 3.05/0.94  --sup_prop_simpl_new                    true
% 3.05/0.94  --sup_prop_simpl_given                  true
% 3.05/0.94  --sup_fun_splitting                     false
% 3.05/0.94  --sup_smt_interval                      50000
% 3.05/0.94  
% 3.05/0.94  ------ Superposition Simplification Setup
% 3.05/0.94  
% 3.05/0.94  --sup_indices_passive                   []
% 3.05/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.94  --sup_full_bw                           [BwDemod]
% 3.05/0.94  --sup_immed_triv                        [TrivRules]
% 3.05/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.94  --sup_immed_bw_main                     []
% 3.05/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.94  
% 3.05/0.94  ------ Combination Options
% 3.05/0.94  
% 3.05/0.94  --comb_res_mult                         3
% 3.05/0.94  --comb_sup_mult                         2
% 3.05/0.94  --comb_inst_mult                        10
% 3.05/0.94  
% 3.05/0.94  ------ Debug Options
% 3.05/0.94  
% 3.05/0.94  --dbg_backtrace                         false
% 3.05/0.94  --dbg_dump_prop_clauses                 false
% 3.05/0.94  --dbg_dump_prop_clauses_file            -
% 3.05/0.94  --dbg_out_stat                          false
% 3.05/0.94  
% 3.05/0.94  
% 3.05/0.94  
% 3.05/0.94  
% 3.05/0.94  ------ Proving...
% 3.05/0.94  
% 3.05/0.94  
% 3.05/0.94  % SZS status Theorem for theBenchmark.p
% 3.05/0.94  
% 3.05/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 3.05/0.94  
% 3.05/0.94  fof(f7,axiom,(
% 3.05/0.94    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 3.05/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.94  
% 3.05/0.94  fof(f17,plain,(
% 3.05/0.94    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.05/0.94    inference(ennf_transformation,[],[f7])).
% 3.05/0.94  
% 3.05/0.94  fof(f53,plain,(
% 3.05/0.94    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 3.05/0.94    inference(cnf_transformation,[],[f17])).
% 3.05/0.94  
% 3.05/0.94  fof(f8,conjecture,(
% 3.05/0.94    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) => r1_orders_2(X0,X1,X3))))))),
% 3.05/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.94  
% 3.05/0.94  fof(f9,negated_conjecture,(
% 3.05/0.94    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) => r1_orders_2(X0,X1,X3))))))),
% 3.05/0.94    inference(negated_conjecture,[],[f8])).
% 3.05/0.94  
% 3.05/0.94  fof(f18,plain,(
% 3.05/0.94    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_orders_2(X0,X1,X3) & (r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v4_orders_2(X0)))),
% 3.05/0.94    inference(ennf_transformation,[],[f9])).
% 3.05/0.94  
% 3.05/0.94  fof(f19,plain,(
% 3.05/0.94    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 3.05/0.94    inference(flattening,[],[f18])).
% 3.05/0.94  
% 3.05/0.94  fof(f33,plain,(
% 3.05/0.94    ( ! [X2,X0,X1] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK8) & r1_orders_2(X0,X2,sK8) & r1_orders_2(X0,X1,X2) & m1_subset_1(sK8,u1_struct_0(X0)))) )),
% 3.05/0.94    introduced(choice_axiom,[])).
% 3.05/0.94  
% 3.05/0.94  fof(f32,plain,(
% 3.05/0.94    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r1_orders_2(X0,X1,X3) & r1_orders_2(X0,sK7,X3) & r1_orders_2(X0,X1,sK7) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK7,u1_struct_0(X0)))) )),
% 3.05/0.94    introduced(choice_axiom,[])).
% 3.05/0.94  
% 3.05/0.94  fof(f31,plain,(
% 3.05/0.94    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~r1_orders_2(X0,sK6,X3) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,sK6,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 3.05/0.94    introduced(choice_axiom,[])).
% 3.05/0.94  
% 3.05/0.94  fof(f30,plain,(
% 3.05/0.94    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v4_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_orders_2(sK5,X1,X3) & r1_orders_2(sK5,X2,X3) & r1_orders_2(sK5,X1,X2) & m1_subset_1(X3,u1_struct_0(sK5))) & m1_subset_1(X2,u1_struct_0(sK5))) & m1_subset_1(X1,u1_struct_0(sK5))) & l1_orders_2(sK5) & v4_orders_2(sK5))),
% 3.05/0.94    introduced(choice_axiom,[])).
% 3.05/0.94  
% 3.05/0.94  fof(f34,plain,(
% 3.05/0.94    (((~r1_orders_2(sK5,sK6,sK8) & r1_orders_2(sK5,sK7,sK8) & r1_orders_2(sK5,sK6,sK7) & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_subset_1(sK6,u1_struct_0(sK5))) & l1_orders_2(sK5) & v4_orders_2(sK5)),
% 3.05/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f19,f33,f32,f31,f30])).
% 3.05/0.94  
% 3.05/0.94  fof(f55,plain,(
% 3.05/0.94    l1_orders_2(sK5)),
% 3.05/0.94    inference(cnf_transformation,[],[f34])).
% 3.05/0.94  
% 3.05/0.94  fof(f3,axiom,(
% 3.05/0.94    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 3.05/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.94  
% 3.05/0.94  fof(f11,plain,(
% 3.05/0.94    ! [X0,X1,X2,X3] : ((? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.05/0.94    inference(ennf_transformation,[],[f3])).
% 3.05/0.94  
% 3.05/0.94  fof(f12,plain,(
% 3.05/0.94    ! [X0,X1,X2,X3] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.05/0.94    inference(flattening,[],[f11])).
% 3.05/0.94  
% 3.05/0.94  fof(f22,plain,(
% 3.05/0.94    ! [X2,X1,X0] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) => (r2_hidden(sK1(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)) = X0))),
% 3.05/0.94    introduced(choice_axiom,[])).
% 3.05/0.94  
% 3.05/0.94  fof(f23,plain,(
% 3.05/0.94    ! [X0,X1,X2,X3] : ((r2_hidden(sK1(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.05/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f22])).
% 3.05/0.94  
% 3.05/0.94  fof(f40,plain,(
% 3.05/0.94    ( ! [X2,X0,X3,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 3.05/0.94    inference(cnf_transformation,[],[f23])).
% 3.05/0.94  
% 3.05/0.94  fof(f41,plain,(
% 3.05/0.94    ( ! [X2,X0,X3,X1] : (r2_hidden(sK1(X0,X1,X2),X2) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 3.05/0.94    inference(cnf_transformation,[],[f23])).
% 3.05/0.94  
% 3.05/0.94  fof(f59,plain,(
% 3.05/0.94    r1_orders_2(sK5,sK6,sK7)),
% 3.05/0.94    inference(cnf_transformation,[],[f34])).
% 3.05/0.94  
% 3.05/0.94  fof(f6,axiom,(
% 3.05/0.94    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 3.05/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.94  
% 3.05/0.94  fof(f16,plain,(
% 3.05/0.94    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.05/0.94    inference(ennf_transformation,[],[f6])).
% 3.05/0.94  
% 3.05/0.94  fof(f29,plain,(
% 3.05/0.94    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.05/0.94    inference(nnf_transformation,[],[f16])).
% 3.05/0.94  
% 3.05/0.94  fof(f51,plain,(
% 3.05/0.94    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.05/0.94    inference(cnf_transformation,[],[f29])).
% 3.05/0.94  
% 3.05/0.94  fof(f56,plain,(
% 3.05/0.94    m1_subset_1(sK6,u1_struct_0(sK5))),
% 3.05/0.94    inference(cnf_transformation,[],[f34])).
% 3.05/0.94  
% 3.05/0.94  fof(f57,plain,(
% 3.05/0.94    m1_subset_1(sK7,u1_struct_0(sK5))),
% 3.05/0.94    inference(cnf_transformation,[],[f34])).
% 3.05/0.94  
% 3.05/0.94  fof(f39,plain,(
% 3.05/0.94    ( ! [X2,X0,X3,X1] : (k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)) = X0 | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 3.05/0.94    inference(cnf_transformation,[],[f23])).
% 3.05/0.94  
% 3.05/0.94  fof(f1,axiom,(
% 3.05/0.94    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.05/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.94  
% 3.05/0.94  fof(f20,plain,(
% 3.05/0.94    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.05/0.94    inference(nnf_transformation,[],[f1])).
% 3.05/0.94  
% 3.05/0.94  fof(f21,plain,(
% 3.05/0.94    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.05/0.94    inference(flattening,[],[f20])).
% 3.05/0.94  
% 3.05/0.94  fof(f37,plain,(
% 3.05/0.94    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 3.05/0.94    inference(cnf_transformation,[],[f21])).
% 3.05/0.94  
% 3.05/0.94  fof(f35,plain,(
% 3.05/0.94    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.05/0.94    inference(cnf_transformation,[],[f21])).
% 3.05/0.94  
% 3.05/0.94  fof(f60,plain,(
% 3.05/0.94    r1_orders_2(sK5,sK7,sK8)),
% 3.05/0.94    inference(cnf_transformation,[],[f34])).
% 3.05/0.94  
% 3.05/0.94  fof(f58,plain,(
% 3.05/0.94    m1_subset_1(sK8,u1_struct_0(sK5))),
% 3.05/0.94    inference(cnf_transformation,[],[f34])).
% 3.05/0.94  
% 3.05/0.94  fof(f36,plain,(
% 3.05/0.94    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.05/0.94    inference(cnf_transformation,[],[f21])).
% 3.05/0.94  
% 3.05/0.94  fof(f5,axiom,(
% 3.05/0.94    ! [X0] : (l1_orders_2(X0) => (v4_orders_2(X0) <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 3.05/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.94  
% 3.05/0.94  fof(f15,plain,(
% 3.05/0.94    ! [X0] : ((v4_orders_2(X0) <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.05/0.94    inference(ennf_transformation,[],[f5])).
% 3.05/0.94  
% 3.05/0.94  fof(f28,plain,(
% 3.05/0.94    ! [X0] : (((v4_orders_2(X0) | ~r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))) & (r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v4_orders_2(X0))) | ~l1_orders_2(X0))),
% 3.05/0.94    inference(nnf_transformation,[],[f15])).
% 3.05/0.94  
% 3.05/0.94  fof(f49,plain,(
% 3.05/0.94    ( ! [X0] : (r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v4_orders_2(X0) | ~l1_orders_2(X0)) )),
% 3.05/0.94    inference(cnf_transformation,[],[f28])).
% 3.05/0.94  
% 3.05/0.94  fof(f54,plain,(
% 3.05/0.94    v4_orders_2(sK5)),
% 3.05/0.94    inference(cnf_transformation,[],[f34])).
% 3.05/0.94  
% 3.05/0.94  fof(f4,axiom,(
% 3.05/0.94    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => r2_hidden(k4_tarski(X2,X4),X0))))),
% 3.05/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.94  
% 3.05/0.94  fof(f13,plain,(
% 3.05/0.94    ! [X0] : (! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))) | ~v1_relat_1(X0))),
% 3.05/0.94    inference(ennf_transformation,[],[f4])).
% 3.05/0.94  
% 3.05/0.94  fof(f14,plain,(
% 3.05/0.94    ! [X0] : (! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 3.05/0.94    inference(flattening,[],[f13])).
% 3.05/0.94  
% 3.05/0.94  fof(f24,plain,(
% 3.05/0.94    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | ? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 3.05/0.94    inference(nnf_transformation,[],[f14])).
% 3.05/0.94  
% 3.05/0.94  fof(f25,plain,(
% 3.05/0.94    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | ? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X5,X6,X7] : (r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 3.05/0.94    inference(rectify,[],[f24])).
% 3.05/0.94  
% 3.05/0.94  fof(f26,plain,(
% 3.05/0.94    ! [X1,X0] : (? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (~r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0) & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) & r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK2(X0,X1),X1)))),
% 3.05/0.94    introduced(choice_axiom,[])).
% 3.05/0.94  
% 3.05/0.94  fof(f27,plain,(
% 3.05/0.94    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | (~r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0) & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) & r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK2(X0,X1),X1))) & (! [X5,X6,X7] : (r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 3.05/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f26])).
% 3.05/0.94  
% 3.05/0.94  fof(f42,plain,(
% 3.05/0.94    ( ! [X6,X0,X7,X5,X1] : (r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X1) | ~r8_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 3.05/0.94    inference(cnf_transformation,[],[f27])).
% 3.05/0.94  
% 3.05/0.94  fof(f2,axiom,(
% 3.05/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.05/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.94  
% 3.05/0.94  fof(f10,plain,(
% 3.05/0.94    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.94    inference(ennf_transformation,[],[f2])).
% 3.05/0.94  
% 3.05/0.94  fof(f38,plain,(
% 3.05/0.94    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.94    inference(cnf_transformation,[],[f10])).
% 3.05/0.94  
% 3.05/0.94  fof(f61,plain,(
% 3.05/0.94    ~r1_orders_2(sK5,sK6,sK8)),
% 3.05/0.94    inference(cnf_transformation,[],[f34])).
% 3.05/0.94  
% 3.05/0.94  fof(f52,plain,(
% 3.05/0.94    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.05/0.94    inference(cnf_transformation,[],[f29])).
% 3.05/0.94  
% 3.05/0.94  cnf(c_18,plain,
% 3.05/0.94      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.05/0.94      | ~ l1_orders_2(X0) ),
% 3.05/0.94      inference(cnf_transformation,[],[f53]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_25,negated_conjecture,
% 3.05/0.94      ( l1_orders_2(sK5) ),
% 3.05/0.94      inference(cnf_transformation,[],[f55]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_306,plain,
% 3.05/0.94      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.05/0.94      | sK5 != X0 ),
% 3.05/0.94      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_307,plain,
% 3.05/0.94      ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) ),
% 3.05/0.94      inference(unflattening,[status(thm)],[c_306]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_2210,plain,
% 3.05/0.94      ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) = iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_5,plain,
% 3.05/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.94      | ~ r2_hidden(X3,X0)
% 3.05/0.94      | r2_hidden(sK0(X3,X1,X2),X1) ),
% 3.05/0.94      inference(cnf_transformation,[],[f40]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_2223,plain,
% 3.05/0.94      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.05/0.94      | r2_hidden(X3,X0) != iProver_top
% 3.05/0.94      | r2_hidden(sK0(X3,X1,X2),X1) = iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_3104,plain,
% 3.05/0.94      ( r2_hidden(X0,u1_orders_2(sK5)) != iProver_top
% 3.05/0.94      | r2_hidden(sK0(X0,u1_struct_0(sK5),u1_struct_0(sK5)),u1_struct_0(sK5)) = iProver_top ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_2210,c_2223]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_4,plain,
% 3.05/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.94      | ~ r2_hidden(X3,X0)
% 3.05/0.94      | r2_hidden(sK1(X3,X1,X2),X2) ),
% 3.05/0.94      inference(cnf_transformation,[],[f41]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_2224,plain,
% 3.05/0.94      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.05/0.94      | r2_hidden(X3,X0) != iProver_top
% 3.05/0.94      | r2_hidden(sK1(X3,X1,X2),X2) = iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_3421,plain,
% 3.05/0.94      ( r2_hidden(X0,u1_orders_2(sK5)) != iProver_top
% 3.05/0.94      | r2_hidden(sK1(X0,u1_struct_0(sK5),u1_struct_0(sK5)),u1_struct_0(sK5)) = iProver_top ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_2210,c_2224]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_21,negated_conjecture,
% 3.05/0.94      ( r1_orders_2(sK5,sK6,sK7) ),
% 3.05/0.94      inference(cnf_transformation,[],[f59]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_17,plain,
% 3.05/0.94      ( ~ r1_orders_2(X0,X1,X2)
% 3.05/0.94      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.05/0.94      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.05/0.94      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 3.05/0.94      | ~ l1_orders_2(X0) ),
% 3.05/0.94      inference(cnf_transformation,[],[f51]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_313,plain,
% 3.05/0.94      ( ~ r1_orders_2(X0,X1,X2)
% 3.05/0.94      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.05/0.94      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.05/0.94      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 3.05/0.94      | sK5 != X0 ),
% 3.05/0.94      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_314,plain,
% 3.05/0.94      ( ~ r1_orders_2(sK5,X0,X1)
% 3.05/0.94      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.05/0.94      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.05/0.94      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) ),
% 3.05/0.94      inference(unflattening,[status(thm)],[c_313]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_404,plain,
% 3.05/0.94      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.05/0.94      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.05/0.94      | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK5))
% 3.05/0.94      | sK7 != X0
% 3.05/0.94      | sK6 != X1
% 3.05/0.94      | sK5 != sK5 ),
% 3.05/0.94      inference(resolution_lifted,[status(thm)],[c_21,c_314]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_405,plain,
% 3.05/0.94      ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 3.05/0.94      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 3.05/0.94      | r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5)) ),
% 3.05/0.94      inference(unflattening,[status(thm)],[c_404]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_24,negated_conjecture,
% 3.05/0.94      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 3.05/0.94      inference(cnf_transformation,[],[f56]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_23,negated_conjecture,
% 3.05/0.94      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.05/0.94      inference(cnf_transformation,[],[f57]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_407,plain,
% 3.05/0.94      ( r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5)) ),
% 3.05/0.94      inference(global_propositional_subsumption,
% 3.05/0.94                [status(thm)],
% 3.05/0.94                [c_405,c_24,c_23]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_2207,plain,
% 3.05/0.94      ( r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5)) = iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_6,plain,
% 3.05/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.94      | ~ r2_hidden(X3,X0)
% 3.05/0.94      | k4_tarski(sK0(X3,X1,X2),sK1(X3,X1,X2)) = X3 ),
% 3.05/0.94      inference(cnf_transformation,[],[f39]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_2222,plain,
% 3.05/0.94      ( k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)) = X0
% 3.05/0.94      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.05/0.94      | r2_hidden(X0,X3) != iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_5703,plain,
% 3.05/0.94      ( k4_tarski(sK0(X0,u1_struct_0(sK5),u1_struct_0(sK5)),sK1(X0,u1_struct_0(sK5),u1_struct_0(sK5))) = X0
% 3.05/0.94      | r2_hidden(X0,u1_orders_2(sK5)) != iProver_top ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_2210,c_2222]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_5716,plain,
% 3.05/0.94      ( k4_tarski(sK0(k4_tarski(sK6,sK7),u1_struct_0(sK5),u1_struct_0(sK5)),sK1(k4_tarski(sK6,sK7),u1_struct_0(sK5),u1_struct_0(sK5))) = k4_tarski(sK6,sK7) ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_2207,c_5703]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_0,plain,
% 3.05/0.94      ( ~ r2_hidden(X0,X1)
% 3.05/0.94      | ~ r2_hidden(X2,X3)
% 3.05/0.94      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.05/0.94      inference(cnf_transformation,[],[f37]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_2228,plain,
% 3.05/0.94      ( r2_hidden(X0,X1) != iProver_top
% 3.05/0.94      | r2_hidden(X2,X3) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_5974,plain,
% 3.05/0.94      ( r2_hidden(sK0(k4_tarski(sK6,sK7),u1_struct_0(sK5),u1_struct_0(sK5)),X0) != iProver_top
% 3.05/0.94      | r2_hidden(sK1(k4_tarski(sK6,sK7),u1_struct_0(sK5),u1_struct_0(sK5)),X1) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_5716,c_2228]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_6147,plain,
% 3.05/0.94      ( r2_hidden(sK0(k4_tarski(sK6,sK7),u1_struct_0(sK5),u1_struct_0(sK5)),X0) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(X0,u1_struct_0(sK5))) = iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5)) != iProver_top ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_3421,c_5974]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_29,plain,
% 3.05/0.94      ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_30,plain,
% 3.05/0.94      ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_406,plain,
% 3.05/0.94      ( m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
% 3.05/0.94      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5)) = iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_6152,plain,
% 3.05/0.94      ( r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(X0,u1_struct_0(sK5))) = iProver_top
% 3.05/0.94      | r2_hidden(sK0(k4_tarski(sK6,sK7),u1_struct_0(sK5),u1_struct_0(sK5)),X0) != iProver_top ),
% 3.05/0.94      inference(global_propositional_subsumption,
% 3.05/0.94                [status(thm)],
% 3.05/0.94                [c_6147,c_29,c_30,c_406]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_6153,plain,
% 3.05/0.94      ( r2_hidden(sK0(k4_tarski(sK6,sK7),u1_struct_0(sK5),u1_struct_0(sK5)),X0) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(X0,u1_struct_0(sK5))) = iProver_top ),
% 3.05/0.94      inference(renaming,[status(thm)],[c_6152]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_6160,plain,
% 3.05/0.94      ( r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))) = iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5)) != iProver_top ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_3104,c_6153]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_6163,plain,
% 3.05/0.94      ( r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))) = iProver_top ),
% 3.05/0.94      inference(global_propositional_subsumption,
% 3.05/0.94                [status(thm)],
% 3.05/0.94                [c_6160,c_29,c_30,c_406]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_2,plain,
% 3.05/0.94      ( r2_hidden(X0,X1)
% 3.05/0.94      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.05/0.94      inference(cnf_transformation,[],[f35]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_2226,plain,
% 3.05/0.94      ( r2_hidden(X0,X1) = iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_6169,plain,
% 3.05/0.94      ( r2_hidden(sK6,u1_struct_0(sK5)) = iProver_top ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_6163,c_2226]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_20,negated_conjecture,
% 3.05/0.94      ( r1_orders_2(sK5,sK7,sK8) ),
% 3.05/0.94      inference(cnf_transformation,[],[f60]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_393,plain,
% 3.05/0.94      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.05/0.94      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.05/0.94      | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK5))
% 3.05/0.94      | sK7 != X1
% 3.05/0.94      | sK8 != X0
% 3.05/0.94      | sK5 != sK5 ),
% 3.05/0.94      inference(resolution_lifted,[status(thm)],[c_20,c_314]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_394,plain,
% 3.05/0.94      ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 3.05/0.94      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 3.05/0.94      | r2_hidden(k4_tarski(sK7,sK8),u1_orders_2(sK5)) ),
% 3.05/0.94      inference(unflattening,[status(thm)],[c_393]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_22,negated_conjecture,
% 3.05/0.94      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 3.05/0.94      inference(cnf_transformation,[],[f58]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_396,plain,
% 3.05/0.94      ( r2_hidden(k4_tarski(sK7,sK8),u1_orders_2(sK5)) ),
% 3.05/0.94      inference(global_propositional_subsumption,
% 3.05/0.94                [status(thm)],
% 3.05/0.94                [c_394,c_23,c_22]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_2208,plain,
% 3.05/0.94      ( r2_hidden(k4_tarski(sK7,sK8),u1_orders_2(sK5)) = iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_5715,plain,
% 3.05/0.94      ( k4_tarski(sK0(k4_tarski(sK7,sK8),u1_struct_0(sK5),u1_struct_0(sK5)),sK1(k4_tarski(sK7,sK8),u1_struct_0(sK5),u1_struct_0(sK5))) = k4_tarski(sK7,sK8) ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_2208,c_5703]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_5927,plain,
% 3.05/0.94      ( r2_hidden(sK0(k4_tarski(sK7,sK8),u1_struct_0(sK5),u1_struct_0(sK5)),X0) != iProver_top
% 3.05/0.94      | r2_hidden(sK1(k4_tarski(sK7,sK8),u1_struct_0(sK5),u1_struct_0(sK5)),X1) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(sK7,sK8),k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_5715,c_2228]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_6085,plain,
% 3.05/0.94      ( r2_hidden(sK0(k4_tarski(sK7,sK8),u1_struct_0(sK5),u1_struct_0(sK5)),X0) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(sK7,sK8),k2_zfmisc_1(X0,u1_struct_0(sK5))) = iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(sK7,sK8),u1_orders_2(sK5)) != iProver_top ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_3421,c_5927]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_31,plain,
% 3.05/0.94      ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_395,plain,
% 3.05/0.94      ( m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
% 3.05/0.94      | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(sK7,sK8),u1_orders_2(sK5)) = iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_6090,plain,
% 3.05/0.94      ( r2_hidden(k4_tarski(sK7,sK8),k2_zfmisc_1(X0,u1_struct_0(sK5))) = iProver_top
% 3.05/0.94      | r2_hidden(sK0(k4_tarski(sK7,sK8),u1_struct_0(sK5),u1_struct_0(sK5)),X0) != iProver_top ),
% 3.05/0.94      inference(global_propositional_subsumption,
% 3.05/0.94                [status(thm)],
% 3.05/0.94                [c_6085,c_30,c_31,c_395]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_6091,plain,
% 3.05/0.94      ( r2_hidden(sK0(k4_tarski(sK7,sK8),u1_struct_0(sK5),u1_struct_0(sK5)),X0) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(sK7,sK8),k2_zfmisc_1(X0,u1_struct_0(sK5))) = iProver_top ),
% 3.05/0.94      inference(renaming,[status(thm)],[c_6090]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_6098,plain,
% 3.05/0.94      ( r2_hidden(k4_tarski(sK7,sK8),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))) = iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(sK7,sK8),u1_orders_2(sK5)) != iProver_top ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_3104,c_6091]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_6101,plain,
% 3.05/0.94      ( r2_hidden(k4_tarski(sK7,sK8),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))) = iProver_top ),
% 3.05/0.94      inference(global_propositional_subsumption,
% 3.05/0.94                [status(thm)],
% 3.05/0.94                [c_6098,c_30,c_31,c_395]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_6107,plain,
% 3.05/0.94      ( r2_hidden(sK7,u1_struct_0(sK5)) = iProver_top ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_6101,c_2226]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_1,plain,
% 3.05/0.94      ( r2_hidden(X0,X1)
% 3.05/0.94      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.05/0.94      inference(cnf_transformation,[],[f36]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_2227,plain,
% 3.05/0.94      ( r2_hidden(X0,X1) = iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_6106,plain,
% 3.05/0.94      ( r2_hidden(sK8,u1_struct_0(sK5)) = iProver_top ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_6101,c_2227]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_15,plain,
% 3.05/0.94      ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
% 3.05/0.94      | ~ l1_orders_2(X0)
% 3.05/0.94      | ~ v4_orders_2(X0) ),
% 3.05/0.94      inference(cnf_transformation,[],[f49]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_26,negated_conjecture,
% 3.05/0.94      ( v4_orders_2(sK5) ),
% 3.05/0.94      inference(cnf_transformation,[],[f54]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_293,plain,
% 3.05/0.94      ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
% 3.05/0.94      | ~ l1_orders_2(X0)
% 3.05/0.94      | sK5 != X0 ),
% 3.05/0.94      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_294,plain,
% 3.05/0.94      ( r8_relat_2(u1_orders_2(sK5),u1_struct_0(sK5))
% 3.05/0.94      | ~ l1_orders_2(sK5) ),
% 3.05/0.94      inference(unflattening,[status(thm)],[c_293]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_45,plain,
% 3.05/0.94      ( r8_relat_2(u1_orders_2(sK5),u1_struct_0(sK5))
% 3.05/0.94      | ~ l1_orders_2(sK5)
% 3.05/0.94      | ~ v4_orders_2(sK5) ),
% 3.05/0.94      inference(instantiation,[status(thm)],[c_15]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_296,plain,
% 3.05/0.94      ( r8_relat_2(u1_orders_2(sK5),u1_struct_0(sK5)) ),
% 3.05/0.94      inference(global_propositional_subsumption,
% 3.05/0.94                [status(thm)],
% 3.05/0.94                [c_294,c_26,c_25,c_45]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_2211,plain,
% 3.05/0.94      ( r8_relat_2(u1_orders_2(sK5),u1_struct_0(sK5)) = iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_296]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_13,plain,
% 3.05/0.94      ( ~ r8_relat_2(X0,X1)
% 3.05/0.94      | ~ r2_hidden(X2,X1)
% 3.05/0.94      | ~ r2_hidden(X3,X1)
% 3.05/0.94      | ~ r2_hidden(X4,X1)
% 3.05/0.94      | ~ r2_hidden(k4_tarski(X3,X2),X0)
% 3.05/0.94      | ~ r2_hidden(k4_tarski(X4,X3),X0)
% 3.05/0.94      | r2_hidden(k4_tarski(X4,X2),X0)
% 3.05/0.94      | ~ v1_relat_1(X0) ),
% 3.05/0.94      inference(cnf_transformation,[],[f42]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_2215,plain,
% 3.05/0.94      ( r8_relat_2(X0,X1) != iProver_top
% 3.05/0.94      | r2_hidden(X2,X1) != iProver_top
% 3.05/0.94      | r2_hidden(X3,X1) != iProver_top
% 3.05/0.94      | r2_hidden(X4,X1) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(X3,X2),X0) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(X4,X3),X0) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(X4,X2),X0) = iProver_top
% 3.05/0.94      | v1_relat_1(X0) != iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_3566,plain,
% 3.05/0.94      ( r8_relat_2(u1_orders_2(sK5),X0) != iProver_top
% 3.05/0.94      | r2_hidden(X1,X0) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(X1,sK7),u1_orders_2(sK5)) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(X1,sK8),u1_orders_2(sK5)) = iProver_top
% 3.05/0.94      | r2_hidden(sK7,X0) != iProver_top
% 3.05/0.94      | r2_hidden(sK8,X0) != iProver_top
% 3.05/0.94      | v1_relat_1(u1_orders_2(sK5)) != iProver_top ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_2208,c_2215]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_28,plain,
% 3.05/0.94      ( l1_orders_2(sK5) = iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_35,plain,
% 3.05/0.94      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
% 3.05/0.94      | l1_orders_2(X0) != iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_37,plain,
% 3.05/0.94      ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) = iProver_top
% 3.05/0.94      | l1_orders_2(sK5) != iProver_top ),
% 3.05/0.94      inference(instantiation,[status(thm)],[c_35]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_3,plain,
% 3.05/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.94      | v1_relat_1(X0) ),
% 3.05/0.94      inference(cnf_transformation,[],[f38]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_2388,plain,
% 3.05/0.94      ( ~ m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
% 3.05/0.94      | v1_relat_1(u1_orders_2(sK5)) ),
% 3.05/0.94      inference(instantiation,[status(thm)],[c_3]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_2389,plain,
% 3.05/0.94      ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) != iProver_top
% 3.05/0.94      | v1_relat_1(u1_orders_2(sK5)) = iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_2388]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_4652,plain,
% 3.05/0.94      ( r2_hidden(sK8,X0) != iProver_top
% 3.05/0.94      | r2_hidden(sK7,X0) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(X1,sK8),u1_orders_2(sK5)) = iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(X1,sK7),u1_orders_2(sK5)) != iProver_top
% 3.05/0.94      | r2_hidden(X1,X0) != iProver_top
% 3.05/0.94      | r8_relat_2(u1_orders_2(sK5),X0) != iProver_top ),
% 3.05/0.94      inference(global_propositional_subsumption,
% 3.05/0.94                [status(thm)],
% 3.05/0.94                [c_3566,c_28,c_37,c_2389]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_4653,plain,
% 3.05/0.94      ( r8_relat_2(u1_orders_2(sK5),X0) != iProver_top
% 3.05/0.94      | r2_hidden(X1,X0) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(X1,sK7),u1_orders_2(sK5)) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(X1,sK8),u1_orders_2(sK5)) = iProver_top
% 3.05/0.94      | r2_hidden(sK7,X0) != iProver_top
% 3.05/0.94      | r2_hidden(sK8,X0) != iProver_top ),
% 3.05/0.94      inference(renaming,[status(thm)],[c_4652]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_4664,plain,
% 3.05/0.94      ( r8_relat_2(u1_orders_2(sK5),X0) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(sK6,sK8),u1_orders_2(sK5)) = iProver_top
% 3.05/0.94      | r2_hidden(sK7,X0) != iProver_top
% 3.05/0.94      | r2_hidden(sK8,X0) != iProver_top
% 3.05/0.94      | r2_hidden(sK6,X0) != iProver_top ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_2207,c_4653]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_19,negated_conjecture,
% 3.05/0.94      ( ~ r1_orders_2(sK5,sK6,sK8) ),
% 3.05/0.94      inference(cnf_transformation,[],[f61]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_16,plain,
% 3.05/0.94      ( r1_orders_2(X0,X1,X2)
% 3.05/0.94      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.05/0.94      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.05/0.94      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 3.05/0.94      | ~ l1_orders_2(X0) ),
% 3.05/0.94      inference(cnf_transformation,[],[f52]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_331,plain,
% 3.05/0.94      ( r1_orders_2(X0,X1,X2)
% 3.05/0.94      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.05/0.94      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.05/0.94      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 3.05/0.94      | sK5 != X0 ),
% 3.05/0.94      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_332,plain,
% 3.05/0.94      ( r1_orders_2(sK5,X0,X1)
% 3.05/0.94      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.05/0.94      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.05/0.94      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK5)) ),
% 3.05/0.94      inference(unflattening,[status(thm)],[c_331]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_382,plain,
% 3.05/0.94      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.05/0.94      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.05/0.94      | ~ r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK5))
% 3.05/0.94      | sK8 != X0
% 3.05/0.94      | sK6 != X1
% 3.05/0.94      | sK5 != sK5 ),
% 3.05/0.94      inference(resolution_lifted,[status(thm)],[c_19,c_332]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_383,plain,
% 3.05/0.94      ( ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 3.05/0.94      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 3.05/0.94      | ~ r2_hidden(k4_tarski(sK6,sK8),u1_orders_2(sK5)) ),
% 3.05/0.94      inference(unflattening,[status(thm)],[c_382]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_384,plain,
% 3.05/0.94      ( m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
% 3.05/0.94      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 3.05/0.94      | r2_hidden(k4_tarski(sK6,sK8),u1_orders_2(sK5)) != iProver_top ),
% 3.05/0.94      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_4669,plain,
% 3.05/0.94      ( r8_relat_2(u1_orders_2(sK5),X0) != iProver_top
% 3.05/0.94      | r2_hidden(sK7,X0) != iProver_top
% 3.05/0.94      | r2_hidden(sK8,X0) != iProver_top
% 3.05/0.94      | r2_hidden(sK6,X0) != iProver_top ),
% 3.05/0.94      inference(global_propositional_subsumption,
% 3.05/0.94                [status(thm)],
% 3.05/0.94                [c_4664,c_29,c_31,c_384]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(c_4679,plain,
% 3.05/0.94      ( r2_hidden(sK7,u1_struct_0(sK5)) != iProver_top
% 3.05/0.94      | r2_hidden(sK8,u1_struct_0(sK5)) != iProver_top
% 3.05/0.94      | r2_hidden(sK6,u1_struct_0(sK5)) != iProver_top ),
% 3.05/0.94      inference(superposition,[status(thm)],[c_2211,c_4669]) ).
% 3.05/0.94  
% 3.05/0.94  cnf(contradiction,plain,
% 3.05/0.94      ( $false ),
% 3.05/0.94      inference(minisat,[status(thm)],[c_6169,c_6107,c_6106,c_4679]) ).
% 3.05/0.94  
% 3.05/0.94  
% 3.05/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 3.05/0.94  
% 3.05/0.94  ------                               Statistics
% 3.05/0.94  
% 3.05/0.94  ------ General
% 3.05/0.94  
% 3.05/0.94  abstr_ref_over_cycles:                  0
% 3.05/0.94  abstr_ref_under_cycles:                 0
% 3.05/0.94  gc_basic_clause_elim:                   0
% 3.05/0.94  forced_gc_time:                         0
% 3.05/0.94  parsing_time:                           0.011
% 3.05/0.94  unif_index_cands_time:                  0.
% 3.05/0.94  unif_index_add_time:                    0.
% 3.05/0.94  orderings_time:                         0.
% 3.05/0.94  out_proof_time:                         0.011
% 3.05/0.94  total_time:                             0.253
% 3.05/0.94  num_of_symbols:                         52
% 3.05/0.94  num_of_terms:                           6072
% 3.05/0.94  
% 3.05/0.94  ------ Preprocessing
% 3.05/0.94  
% 3.05/0.94  num_of_splits:                          0
% 3.05/0.94  num_of_split_atoms:                     0
% 3.05/0.94  num_of_reused_defs:                     0
% 3.05/0.94  num_eq_ax_congr_red:                    40
% 3.05/0.94  num_of_sem_filtered_clauses:            1
% 3.05/0.94  num_of_subtypes:                        0
% 3.05/0.94  monotx_restored_types:                  0
% 3.05/0.94  sat_num_of_epr_types:                   0
% 3.05/0.94  sat_num_of_non_cyclic_types:            0
% 3.05/0.94  sat_guarded_non_collapsed_types:        0
% 3.05/0.94  num_pure_diseq_elim:                    0
% 3.05/0.94  simp_replaced_by:                       0
% 3.05/0.94  res_preprocessed:                       120
% 3.05/0.94  prep_upred:                             0
% 3.05/0.94  prep_unflattend:                        46
% 3.05/0.94  smt_new_axioms:                         0
% 3.05/0.94  pred_elim_cands:                        4
% 3.05/0.94  pred_elim:                              3
% 3.05/0.94  pred_elim_cl:                           3
% 3.05/0.94  pred_elim_cycles:                       9
% 3.05/0.94  merged_defs:                            0
% 3.05/0.94  merged_defs_ncl:                        0
% 3.05/0.94  bin_hyper_res:                          0
% 3.05/0.94  prep_cycles:                            4
% 3.05/0.94  pred_elim_time:                         0.023
% 3.05/0.94  splitting_time:                         0.
% 3.05/0.94  sem_filter_time:                        0.
% 3.05/0.94  monotx_time:                            0.001
% 3.05/0.94  subtype_inf_time:                       0.
% 3.05/0.94  
% 3.05/0.94  ------ Problem properties
% 3.05/0.94  
% 3.05/0.94  clauses:                                24
% 3.05/0.94  conjectures:                            3
% 3.05/0.94  epr:                                    2
% 3.05/0.94  horn:                                   19
% 3.05/0.94  ground:                                 10
% 3.05/0.94  unary:                                  10
% 3.05/0.94  binary:                                 3
% 3.05/0.94  lits:                                   54
% 3.05/0.94  lits_eq:                                3
% 3.05/0.94  fd_pure:                                0
% 3.05/0.94  fd_pseudo:                              0
% 3.05/0.94  fd_cond:                                0
% 3.05/0.94  fd_pseudo_cond:                         0
% 3.05/0.94  ac_symbols:                             0
% 3.05/0.94  
% 3.05/0.94  ------ Propositional Solver
% 3.05/0.94  
% 3.05/0.94  prop_solver_calls:                      28
% 3.05/0.94  prop_fast_solver_calls:                 994
% 3.05/0.94  smt_solver_calls:                       0
% 3.05/0.94  smt_fast_solver_calls:                  0
% 3.05/0.94  prop_num_of_clauses:                    2330
% 3.05/0.94  prop_preprocess_simplified:             7299
% 3.05/0.94  prop_fo_subsumed:                       15
% 3.05/0.94  prop_solver_time:                       0.
% 3.05/0.94  smt_solver_time:                        0.
% 3.05/0.94  smt_fast_solver_time:                   0.
% 3.05/0.94  prop_fast_solver_time:                  0.
% 3.05/0.94  prop_unsat_core_time:                   0.
% 3.05/0.94  
% 3.05/0.94  ------ QBF
% 3.05/0.94  
% 3.05/0.94  qbf_q_res:                              0
% 3.05/0.94  qbf_num_tautologies:                    0
% 3.05/0.94  qbf_prep_cycles:                        0
% 3.05/0.94  
% 3.05/0.94  ------ BMC1
% 3.05/0.94  
% 3.05/0.94  bmc1_current_bound:                     -1
% 3.05/0.94  bmc1_last_solved_bound:                 -1
% 3.05/0.94  bmc1_unsat_core_size:                   -1
% 3.05/0.94  bmc1_unsat_core_parents_size:           -1
% 3.05/0.94  bmc1_merge_next_fun:                    0
% 3.05/0.94  bmc1_unsat_core_clauses_time:           0.
% 3.05/0.94  
% 3.05/0.94  ------ Instantiation
% 3.05/0.94  
% 3.05/0.94  inst_num_of_clauses:                    690
% 3.05/0.94  inst_num_in_passive:                    428
% 3.05/0.94  inst_num_in_active:                     215
% 3.05/0.94  inst_num_in_unprocessed:                47
% 3.05/0.94  inst_num_of_loops:                      230
% 3.05/0.94  inst_num_of_learning_restarts:          0
% 3.05/0.94  inst_num_moves_active_passive:          13
% 3.05/0.94  inst_lit_activity:                      0
% 3.05/0.94  inst_lit_activity_moves:                1
% 3.05/0.94  inst_num_tautologies:                   0
% 3.05/0.94  inst_num_prop_implied:                  0
% 3.05/0.94  inst_num_existing_simplified:           0
% 3.05/0.94  inst_num_eq_res_simplified:             0
% 3.05/0.94  inst_num_child_elim:                    0
% 3.05/0.94  inst_num_of_dismatching_blockings:      10
% 3.05/0.94  inst_num_of_non_proper_insts:           391
% 3.05/0.94  inst_num_of_duplicates:                 0
% 3.05/0.94  inst_inst_num_from_inst_to_res:         0
% 3.05/0.94  inst_dismatching_checking_time:         0.
% 3.05/0.94  
% 3.05/0.94  ------ Resolution
% 3.05/0.94  
% 3.05/0.94  res_num_of_clauses:                     0
% 3.05/0.94  res_num_in_passive:                     0
% 3.05/0.94  res_num_in_active:                      0
% 3.05/0.94  res_num_of_loops:                       124
% 3.05/0.94  res_forward_subset_subsumed:            67
% 3.05/0.94  res_backward_subset_subsumed:           0
% 3.05/0.94  res_forward_subsumed:                   0
% 3.05/0.94  res_backward_subsumed:                  0
% 3.05/0.94  res_forward_subsumption_resolution:     0
% 3.05/0.94  res_backward_subsumption_resolution:    0
% 3.05/0.94  res_clause_to_clause_subsumption:       103
% 3.05/0.94  res_orphan_elimination:                 0
% 3.05/0.94  res_tautology_del:                      20
% 3.05/0.94  res_num_eq_res_simplified:              2
% 3.05/0.94  res_num_sel_changes:                    0
% 3.05/0.94  res_moves_from_active_to_pass:          0
% 3.05/0.94  
% 3.05/0.94  ------ Superposition
% 3.05/0.94  
% 3.05/0.94  sup_time_total:                         0.
% 3.05/0.94  sup_time_generating:                    0.
% 3.05/0.94  sup_time_sim_full:                      0.
% 3.05/0.94  sup_time_sim_immed:                     0.
% 3.05/0.94  
% 3.05/0.94  sup_num_of_clauses:                     70
% 3.05/0.94  sup_num_in_active:                      45
% 3.05/0.94  sup_num_in_passive:                     25
% 3.05/0.94  sup_num_of_loops:                       44
% 3.05/0.94  sup_fw_superposition:                   24
% 3.05/0.94  sup_bw_superposition:                   28
% 3.05/0.94  sup_immediate_simplified:               0
% 3.05/0.94  sup_given_eliminated:                   0
% 3.05/0.94  comparisons_done:                       0
% 3.05/0.94  comparisons_avoided:                    0
% 3.05/0.94  
% 3.05/0.94  ------ Simplifications
% 3.05/0.94  
% 3.05/0.94  
% 3.05/0.94  sim_fw_subset_subsumed:                 0
% 3.05/0.94  sim_bw_subset_subsumed:                 0
% 3.05/0.94  sim_fw_subsumed:                        0
% 3.05/0.94  sim_bw_subsumed:                        0
% 3.05/0.94  sim_fw_subsumption_res:                 0
% 3.05/0.94  sim_bw_subsumption_res:                 0
% 3.05/0.94  sim_tautology_del:                      2
% 3.05/0.94  sim_eq_tautology_del:                   0
% 3.05/0.94  sim_eq_res_simp:                        0
% 3.05/0.94  sim_fw_demodulated:                     0
% 3.05/0.94  sim_bw_demodulated:                     0
% 3.05/0.94  sim_light_normalised:                   0
% 3.05/0.94  sim_joinable_taut:                      0
% 3.05/0.94  sim_joinable_simp:                      0
% 3.05/0.94  sim_ac_normalised:                      0
% 3.05/0.94  sim_smt_subsumption:                    0
% 3.05/0.94  
%------------------------------------------------------------------------------
