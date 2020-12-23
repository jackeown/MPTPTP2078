%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1581+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:57 EST 2020

% Result     : Theorem 0.79s
% Output     : CNFRefutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 379 expanded)
%              Number of clauses        :   58 (  88 expanded)
%              Number of leaves         :   14 ( 154 expanded)
%              Depth                    :   17
%              Number of atoms          :  388 (3230 expanded)
%              Number of equality atoms :   70 ( 723 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X4,X5)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X0,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_yellow_0(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( r1_orders_2(X1,X4,X5)
                                & X3 = X5
                                & X2 = X4 )
                             => r1_orders_2(X0,X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X1,X4,X5)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X1,X4,X5)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r1_orders_2(X1,X4,X5)
          & X3 = X5
          & X2 = X4
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X0,X2,X3)
        & r1_orders_2(X1,X4,sK5)
        & sK5 = X3
        & X2 = X4
        & m1_subset_1(sK5,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r1_orders_2(X0,X2,X3)
              & r1_orders_2(X1,X4,X5)
              & X3 = X5
              & X2 = X4
              & m1_subset_1(X5,u1_struct_0(X1)) )
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ? [X5] :
            ( ~ r1_orders_2(X0,X2,X3)
            & r1_orders_2(X1,sK4,X5)
            & X3 = X5
            & sK4 = X2
            & m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X1,X4,X5)
                  & X3 = X5
                  & X2 = X4
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r1_orders_2(X0,X2,sK3)
                & r1_orders_2(X1,X4,X5)
                & sK3 = X5
                & X2 = X4
                & m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X1,X4,X5)
                      & X3 = X5
                      & X2 = X4
                      & m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r1_orders_2(X0,sK2,X3)
                    & r1_orders_2(X1,X4,X5)
                    & X3 = X5
                    & sK2 = X4
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X1,X4,X5)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_yellow_0(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r1_orders_2(X0,X2,X3)
                        & r1_orders_2(sK1,X4,X5)
                        & X3 = X5
                        & X2 = X4
                        & m1_subset_1(X5,u1_struct_0(sK1)) )
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_yellow_0(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r1_orders_2(X0,X2,X3)
                            & r1_orders_2(X1,X4,X5)
                            & X3 = X5
                            & X2 = X4
                            & m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_yellow_0(X1,X0) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(sK0,X2,X3)
                          & r1_orders_2(X1,X4,X5)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_yellow_0(X1,sK0) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    & r1_orders_2(sK1,sK4,sK5)
    & sK3 = sK5
    & sK2 = sK4
    & m1_subset_1(sK5,u1_struct_0(sK1))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_yellow_0(sK1,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f19,f29,f28,f27,f26,f25,f24])).

fof(f43,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    r1_orders_2(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ~ r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_5,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_19,negated_conjecture,
    ( m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_450,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_19])).

cnf(c_451,plain,
    ( l1_orders_2(sK1)
    | ~ l1_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_453,plain,
    ( l1_orders_2(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_451,c_20])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_12,negated_conjecture,
    ( r1_orders_2(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_291,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(k4_tarski(X2,X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | sK5 != X0
    | sK4 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_12])).

cnf(c_292,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_294,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_16,c_15])).

cnf(c_466,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_453,c_294])).

cnf(c_1149,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK1)) ),
    inference(subtyping,[status(esa)],[c_466])).

cnf(c_1422,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1149])).

cnf(c_14,negated_conjecture,
    ( sK2 = sK4 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1156,negated_conjecture,
    ( sK2 = sK4 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_13,negated_conjecture,
    ( sK3 = sK5 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1157,negated_conjecture,
    ( sK3 = sK5 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1443,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1422,c_1156,c_1157])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_148,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_149,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_148])).

cnf(c_1,plain,
    ( r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_120,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1,c_5])).

cnf(c_121,plain,
    ( r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_120])).

cnf(c_428,plain,
    ( r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_121,c_19])).

cnf(c_429,plain,
    ( r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_431,plain,
    ( r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_20])).

cnf(c_483,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_orders_2(sK1) != X0
    | u1_orders_2(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_149,c_431])).

cnf(c_484,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(u1_orders_2(sK0))) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_1148,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(u1_orders_2(sK0))) ),
    inference(subtyping,[status(esa)],[c_484])).

cnf(c_1423,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(u1_orders_2(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1148])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1159,plain,
    ( m1_subset_1(X0_45,X1_45)
    | ~ m1_subset_1(X2_45,k1_zfmisc_1(X1_45))
    | ~ r2_hidden(X0_45,X2_45) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1415,plain,
    ( m1_subset_1(X0_45,X1_45) = iProver_top
    | m1_subset_1(X2_45,k1_zfmisc_1(X1_45)) != iProver_top
    | r2_hidden(X0_45,X2_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1159])).

cnf(c_1962,plain,
    ( m1_subset_1(X0_45,u1_orders_2(sK0)) = iProver_top
    | r2_hidden(X0_45,u1_orders_2(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_1415])).

cnf(c_2171,plain,
    ( m1_subset_1(k4_tarski(sK2,sK3),u1_orders_2(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1443,c_1962])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_189,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_149])).

cnf(c_497,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X2)
    | u1_orders_2(sK1) != X1
    | u1_orders_2(sK0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_189,c_431])).

cnf(c_498,plain,
    ( ~ r2_hidden(X0,u1_orders_2(sK1))
    | ~ v1_xboole_0(u1_orders_2(sK0)) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_693,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK0))
    | k4_tarski(sK4,sK5) != X0
    | u1_orders_2(sK1) != u1_orders_2(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_466,c_498])).

cnf(c_694,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK0)) ),
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_695,plain,
    ( v1_xboole_0(u1_orders_2(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_694])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_11,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | sK3 != X0
    | sK2 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_281,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_283,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_281,c_20,c_18,c_17])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k4_tarski(sK2,sK3) != X0
    | u1_orders_2(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_283])).

cnf(c_355,plain,
    ( ~ m1_subset_1(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | v1_xboole_0(u1_orders_2(sK0)) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_356,plain,
    ( m1_subset_1(k4_tarski(sK2,sK3),u1_orders_2(sK0)) != iProver_top
    | v1_xboole_0(u1_orders_2(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2171,c_695,c_356])).


%------------------------------------------------------------------------------
