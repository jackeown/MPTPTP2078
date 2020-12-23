%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1138+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:59 EST 2020

% Result     : Theorem 1.44s
% Output     : CNFRefutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 238 expanded)
%              Number of clauses        :   53 (  67 expanded)
%              Number of leaves         :   15 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  451 (1446 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2,X3,X4] :
          ( ~ r2_hidden(k4_tarski(X2,X4),X0)
          & r2_hidden(k4_tarski(X3,X4),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X4,X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK2(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK2(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
              & r2_hidden(sK2(X0,X1),X1)
              & r2_hidden(sK1(X0,X1),X1)
              & r2_hidden(sK0(X0,X1),X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).

fof(f43,plain,(
    ! [X6,X0,X7,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X7),X0)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f33])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r1_orders_2(X0,X2,X3)
          & r1_orders_2(X0,X1,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK6)
        & r1_orders_2(X0,X2,sK6)
        & r1_orders_2(X0,X1,X2)
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
            & r1_orders_2(X0,sK5,X3)
            & r1_orders_2(X0,X1,sK5)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
                ( ~ r1_orders_2(X0,sK4,X3)
                & r1_orders_2(X0,X2,X3)
                & r1_orders_2(X0,sK4,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
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
                  ( ~ r1_orders_2(sK3,X1,X3)
                  & r1_orders_2(sK3,X2,X3)
                  & r1_orders_2(sK3,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK3)) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v4_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r1_orders_2(sK3,sK4,sK6)
    & r1_orders_2(sK3,sK5,sK6)
    & r1_orders_2(sK3,sK4,sK5)
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v4_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f26,f38,f37,f36,f35])).

fof(f65,plain,(
    r1_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    r1_orders_2(sK3,sK5,sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    ~ r1_orders_2(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v4_orders_2(X0)
          | ~ r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v4_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),X4)
    | ~ r2_hidden(k4_tarski(X3,X2),X4)
    | r2_hidden(k4_tarski(X3,X0),X4)
    | ~ r8_relat_2(X4,X1)
    | ~ v1_relat_1(X4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1360,plain,
    ( ~ r2_hidden(X0_48,X1_48)
    | ~ r2_hidden(X2_48,X1_48)
    | ~ r2_hidden(X3_48,X1_48)
    | ~ r2_hidden(k4_tarski(X2_48,X0_48),X4_48)
    | ~ r2_hidden(k4_tarski(X3_48,X2_48),X4_48)
    | r2_hidden(k4_tarski(X3_48,X0_48),X4_48)
    | ~ r8_relat_2(X4_48,X1_48)
    | ~ v1_relat_1(X4_48) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2449,plain,
    ( ~ r2_hidden(X0_48,X1_48)
    | ~ r2_hidden(X2_48,X1_48)
    | ~ r2_hidden(X3_48,X1_48)
    | ~ r2_hidden(k4_tarski(X2_48,X0_48),u1_orders_2(sK3))
    | ~ r2_hidden(k4_tarski(X3_48,X2_48),u1_orders_2(sK3))
    | r2_hidden(k4_tarski(X3_48,X0_48),u1_orders_2(sK3))
    | ~ r8_relat_2(u1_orders_2(sK3),X1_48)
    | ~ v1_relat_1(u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_1360])).

cnf(c_2886,plain,
    ( ~ r2_hidden(X0_48,u1_struct_0(sK3))
    | ~ r2_hidden(X1_48,u1_struct_0(sK3))
    | ~ r2_hidden(X2_48,u1_struct_0(sK3))
    | ~ r2_hidden(k4_tarski(X1_48,X0_48),u1_orders_2(sK3))
    | ~ r2_hidden(k4_tarski(X2_48,X1_48),u1_orders_2(sK3))
    | r2_hidden(k4_tarski(X2_48,X0_48),u1_orders_2(sK3))
    | ~ r8_relat_2(u1_orders_2(sK3),u1_struct_0(sK3))
    | ~ v1_relat_1(u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_2449])).

cnf(c_5759,plain,
    ( ~ r2_hidden(X0_48,u1_struct_0(sK3))
    | ~ r2_hidden(k4_tarski(X0_48,sK5),u1_orders_2(sK3))
    | r2_hidden(k4_tarski(X0_48,sK6),u1_orders_2(sK3))
    | ~ r2_hidden(k4_tarski(sK5,sK6),u1_orders_2(sK3))
    | ~ r2_hidden(sK5,u1_struct_0(sK3))
    | ~ r2_hidden(sK6,u1_struct_0(sK3))
    | ~ r8_relat_2(u1_orders_2(sK3),u1_struct_0(sK3))
    | ~ v1_relat_1(u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_2886])).

cnf(c_5761,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),u1_orders_2(sK3))
    | ~ r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3))
    | r2_hidden(k4_tarski(sK4,sK6),u1_orders_2(sK3))
    | ~ r2_hidden(sK5,u1_struct_0(sK3))
    | ~ r2_hidden(sK6,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ r8_relat_2(u1_orders_2(sK3),u1_struct_0(sK3))
    | ~ v1_relat_1(u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_5759])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1357,plain,
    ( r2_hidden(X0_48,X1_48)
    | ~ r2_hidden(k4_tarski(X0_48,X2_48),k2_zfmisc_1(X1_48,X3_48)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3551,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK5),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1357])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1358,plain,
    ( r2_hidden(X0_48,X1_48)
    | ~ r2_hidden(k4_tarski(X2_48,X0_48),k2_zfmisc_1(X3_48,X1_48)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1603,plain,
    ( ~ r2_hidden(k4_tarski(X0_48,sK6),k2_zfmisc_1(X1_48,X2_48))
    | r2_hidden(sK6,X2_48) ),
    inference(instantiation,[status(thm)],[c_1358])).

cnf(c_3457,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | r2_hidden(sK6,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1603])).

cnf(c_3453,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | r2_hidden(sK5,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1357])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1354,plain,
    ( ~ r2_hidden(X0_48,X1_48)
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(X2_48))
    | ~ v1_xboole_0(X2_48) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1456,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3))
    | ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(X0_48))
    | ~ v1_xboole_0(X0_48) ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_2821,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3))
    | ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1456])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1356,plain,
    ( r2_hidden(X0_48,X1_48)
    | ~ m1_subset_1(X0_48,X1_48)
    | v1_xboole_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1496,plain,
    ( r2_hidden(X0_48,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | ~ m1_subset_1(X0_48,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1356])).

cnf(c_2330,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | ~ m1_subset_1(k4_tarski(sK4,sK5),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_2326,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | ~ m1_subset_1(k4_tarski(sK5,sK6),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1355,plain,
    ( ~ r2_hidden(X0_48,X1_48)
    | m1_subset_1(X0_48,X2_48)
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(X2_48)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1543,plain,
    ( ~ r2_hidden(X0_48,X1_48)
    | m1_subset_1(X0_48,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_1355])).

cnf(c_1662,plain,
    ( ~ r2_hidden(X0_48,u1_orders_2(sK3))
    | m1_subset_1(X0_48,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_1866,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3))
    | m1_subset_1(k4_tarski(sK4,sK5),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_1662])).

cnf(c_1863,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),u1_orders_2(sK3))
    | m1_subset_1(k4_tarski(sK5,sK6),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_1662])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1367,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1533,plain,
    ( ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | v1_relat_1(u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_1367])).

cnf(c_1548,plain,
    ( ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | v1_relat_1(u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_1533])).

cnf(c_22,negated_conjecture,
    ( r1_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_11,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_26,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_342,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_11,c_26])).

cnf(c_409,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_22,c_342])).

cnf(c_21,negated_conjecture,
    ( r1_orders_2(sK3,sK5,sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_399,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),u1_orders_2(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_21,c_342])).

cnf(c_20,negated_conjecture,
    ( ~ r1_orders_2(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_359,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_10,c_26])).

cnf(c_389,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK6),u1_orders_2(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_20,c_359])).

cnf(c_2,plain,
    ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v4_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_82,plain,
    ( r8_relat_2(u1_orders_2(sK3),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ v4_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_54,plain,
    ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5761,c_3551,c_3457,c_3453,c_2821,c_2330,c_2326,c_1866,c_1863,c_1548,c_409,c_399,c_389,c_82,c_54,c_23,c_24,c_25,c_26,c_27])).


%------------------------------------------------------------------------------
