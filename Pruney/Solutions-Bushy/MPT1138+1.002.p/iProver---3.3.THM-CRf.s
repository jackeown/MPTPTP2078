%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1138+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 235 expanded)
%              Number of clauses        :   52 (  64 expanded)
%              Number of leaves         :   15 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  449 (1438 expanded)
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

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

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

cnf(c_1332,plain,
    ( ~ r2_hidden(X0_48,X1_48)
    | ~ r2_hidden(X2_48,X1_48)
    | ~ r2_hidden(X3_48,X1_48)
    | ~ r2_hidden(k4_tarski(X2_48,X0_48),X4_48)
    | ~ r2_hidden(k4_tarski(X3_48,X2_48),X4_48)
    | r2_hidden(k4_tarski(X3_48,X0_48),X4_48)
    | ~ r8_relat_2(X4_48,X1_48)
    | ~ v1_relat_1(X4_48) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2237,plain,
    ( ~ r2_hidden(X0_48,X1_48)
    | ~ r2_hidden(X2_48,X1_48)
    | ~ r2_hidden(X3_48,X1_48)
    | ~ r2_hidden(k4_tarski(X2_48,X0_48),u1_orders_2(sK3))
    | ~ r2_hidden(k4_tarski(X3_48,X2_48),u1_orders_2(sK3))
    | r2_hidden(k4_tarski(X3_48,X0_48),u1_orders_2(sK3))
    | ~ r8_relat_2(u1_orders_2(sK3),X1_48)
    | ~ v1_relat_1(u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_1332])).

cnf(c_2531,plain,
    ( ~ r2_hidden(X0_48,u1_struct_0(sK3))
    | ~ r2_hidden(X1_48,u1_struct_0(sK3))
    | ~ r2_hidden(X2_48,u1_struct_0(sK3))
    | ~ r2_hidden(k4_tarski(X1_48,X0_48),u1_orders_2(sK3))
    | ~ r2_hidden(k4_tarski(X2_48,X1_48),u1_orders_2(sK3))
    | r2_hidden(k4_tarski(X2_48,X0_48),u1_orders_2(sK3))
    | ~ r8_relat_2(u1_orders_2(sK3),u1_struct_0(sK3))
    | ~ v1_relat_1(u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_2237])).

cnf(c_7276,plain,
    ( ~ r2_hidden(X0_48,u1_struct_0(sK3))
    | ~ r2_hidden(k4_tarski(X0_48,sK5),u1_orders_2(sK3))
    | r2_hidden(k4_tarski(X0_48,sK6),u1_orders_2(sK3))
    | ~ r2_hidden(k4_tarski(sK5,sK6),u1_orders_2(sK3))
    | ~ r2_hidden(sK5,u1_struct_0(sK3))
    | ~ r2_hidden(sK6,u1_struct_0(sK3))
    | ~ r8_relat_2(u1_orders_2(sK3),u1_struct_0(sK3))
    | ~ v1_relat_1(u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_2531])).

cnf(c_7278,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),u1_orders_2(sK3))
    | ~ r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3))
    | r2_hidden(k4_tarski(sK4,sK6),u1_orders_2(sK3))
    | ~ r2_hidden(sK5,u1_struct_0(sK3))
    | ~ r2_hidden(sK6,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ r8_relat_2(u1_orders_2(sK3),u1_struct_0(sK3))
    | ~ v1_relat_1(u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_7276])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1329,plain,
    ( r2_hidden(X0_48,X1_48)
    | ~ r2_hidden(k4_tarski(X0_48,X2_48),k2_zfmisc_1(X1_48,X3_48)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3930,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK5),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1329])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1330,plain,
    ( r2_hidden(X0_48,X1_48)
    | ~ r2_hidden(k4_tarski(X2_48,X0_48),k2_zfmisc_1(X3_48,X1_48)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3832,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | r2_hidden(sK6,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_3829,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | r2_hidden(sK5,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1329])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1325,plain,
    ( ~ r2_hidden(X0_48,X1_48)
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(X2_48))
    | ~ v1_xboole_0(X2_48) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1426,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3))
    | ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(X0_48))
    | ~ v1_xboole_0(X0_48) ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_2488,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3))
    | ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1426])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1327,plain,
    ( r2_hidden(X0_48,X1_48)
    | ~ m1_subset_1(X0_48,X1_48)
    | v1_xboole_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1454,plain,
    ( r2_hidden(X0_48,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | ~ m1_subset_1(X0_48,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1327])).

cnf(c_2125,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | ~ m1_subset_1(k4_tarski(sK4,sK5),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_2121,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | ~ m1_subset_1(k4_tarski(sK5,sK6),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1326,plain,
    ( ~ r2_hidden(X0_48,X1_48)
    | m1_subset_1(X0_48,X2_48)
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(X2_48)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1670,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3))
    | m1_subset_1(k4_tarski(sK4,sK5),X0_48)
    | ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(X0_48)) ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_1853,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3))
    | m1_subset_1(k4_tarski(sK4,sK5),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_1670])).

cnf(c_1665,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),u1_orders_2(sK3))
    | m1_subset_1(k4_tarski(sK5,sK6),X0_48)
    | ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(X0_48)) ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_1850,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),u1_orders_2(sK3))
    | m1_subset_1(k4_tarski(sK5,sK6),k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_1665])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1339,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1494,plain,
    ( ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | v1_relat_1(u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_1339])).

cnf(c_1623,plain,
    ( ~ m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | v1_relat_1(u1_orders_2(sK3)) ),
    inference(instantiation,[status(thm)],[c_1494])).

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

cnf(c_329,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_11,c_26])).

cnf(c_396,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_22,c_329])).

cnf(c_21,negated_conjecture,
    ( r1_orders_2(sK3,sK5,sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_386,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),u1_orders_2(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_21,c_329])).

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

cnf(c_346,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_10,c_26])).

cnf(c_376,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK6),u1_orders_2(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_20,c_346])).

cnf(c_2,plain,
    ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v4_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_84,plain,
    ( r8_relat_2(u1_orders_2(sK3),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ v4_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_56,plain,
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
    inference(minisat,[status(thm)],[c_7278,c_3930,c_3832,c_3829,c_2488,c_2125,c_2121,c_1853,c_1850,c_1623,c_396,c_386,c_376,c_84,c_56,c_23,c_24,c_25,c_26,c_27])).


%------------------------------------------------------------------------------
