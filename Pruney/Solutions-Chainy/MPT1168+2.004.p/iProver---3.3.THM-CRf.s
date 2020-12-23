%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:42 EST 2020

% Result     : Theorem 15.45s
% Output     : CNFRefutation 15.45s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 298 expanded)
%              Number of clauses        :   54 (  61 expanded)
%              Number of leaves         :   15 ( 104 expanded)
%              Depth                    :   13
%              Number of atoms          :  714 (2693 expanded)
%              Number of equality atoms :   52 ( 277 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( ( m1_orders_2(X4,X0,X3)
                          & r2_hidden(X2,X4)
                          & r2_hidden(X1,X3)
                          & r2_orders_2(X0,X1,X2) )
                       => r2_hidden(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_hidden(X1,X4)
                      | ~ m1_orders_2(X4,X0,X3)
                      | ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_hidden(X1,X4)
                      | ~ m1_orders_2(X4,X0,X3)
                      | ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X1,X4)
      | ~ m1_orders_2(X4,X0,X3)
      | ~ r2_hidden(X2,X4)
      | ~ r2_hidden(X1,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ r2_hidden(X1,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r1_tarski(X2,X3)
                   => r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
                  | ~ r1_tarski(X2,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
                  | ~ r1_tarski(X2,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
      | ~ r1_tarski(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
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

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_orders_2(X2,X0,X3)
                      & r2_hidden(X1,X2) )
                   => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_orders_2(X2,X0,X3)
                        & r2_hidden(X1,X2) )
                     => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1)
                  & m1_orders_2(X2,X0,X3)
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1)
                  & m1_orders_2(X2,X0,X3)
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1)
          & m1_orders_2(X2,X0,X3)
          & r2_hidden(X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k3_orders_2(X0,sK5,X1) != k3_orders_2(X0,X2,X1)
        & m1_orders_2(X2,X0,sK5)
        & r2_hidden(X1,X2)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1)
              & m1_orders_2(X2,X0,X3)
              & r2_hidden(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( k3_orders_2(X0,sK4,X1) != k3_orders_2(X0,X3,X1)
            & m1_orders_2(sK4,X0,X3)
            & r2_hidden(X1,sK4)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1)
                  & m1_orders_2(X2,X0,X3)
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k3_orders_2(X0,X2,sK3) != k3_orders_2(X0,X3,sK3)
                & m1_orders_2(X2,X0,X3)
                & r2_hidden(sK3,X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1)
                    & m1_orders_2(X2,X0,X3)
                    & r2_hidden(X1,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_orders_2(sK2,X2,X1) != k3_orders_2(sK2,X3,X1)
                  & m1_orders_2(X2,sK2,X3)
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k3_orders_2(sK2,sK4,sK3) != k3_orders_2(sK2,sK5,sK3)
    & m1_orders_2(sK4,sK2,sK5)
    & r2_hidden(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f39,f38,f37,f36])).

fof(f63,plain,(
    m1_orders_2(sK4,sK2,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    k3_orders_2(sK2,sK4,sK3) != k3_orders_2(sK2,sK5,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_12,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X0)
    | r2_hidden(X3,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3650,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ r2_orders_2(sK2,sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),X1)
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),X0)
    | ~ r2_hidden(sK3,X0)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_23317,plain,
    ( ~ m1_orders_2(sK4,sK2,X0)
    | ~ r2_orders_2(sK2,sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),X0)
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4)
    | ~ r2_hidden(sK3,sK4)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_3650])).

cnf(c_67885,plain,
    ( ~ m1_orders_2(sK4,sK2,sK5)
    | ~ r2_orders_2(sK2,sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK3)
    | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK5)
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4)
    | ~ r2_hidden(sK3,sK4)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_23317])).

cnf(c_7,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X1,k3_orders_2(X0,X3,X2))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3645,plain,
    ( ~ r2_orders_2(sK2,sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),X0)
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,X0,sK3))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_17750,plain,
    ( ~ r2_orders_2(sK2,sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK3)
    | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_3645])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | r1_tarski(k3_orders_2(X1,X3,X0),k3_orders_2(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1015,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k3_orders_2(sK2,X1,sK3),k3_orders_2(sK2,X0,sK3))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1215,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k3_orders_2(sK2,sK4,sK3),k3_orders_2(sK2,X0,sK3))
    | ~ r1_tarski(sK4,X0)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_1015])).

cnf(c_10534,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k3_orders_2(sK2,sK4,sK3),k3_orders_2(sK2,sK5,sK3))
    | ~ r1_tarski(sK4,sK5)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_1215])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1573,plain,
    ( ~ r2_hidden(sK1(X0,X1),X2)
    | r2_hidden(sK1(X0,X1),X0)
    | ~ r1_tarski(X2,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3847,plain,
    ( r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3))
    | ~ r1_tarski(k3_orders_2(sK2,sK4,sK3),k3_orders_2(sK2,sK5,sK3)) ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_14,negated_conjecture,
    ( m1_orders_2(sK4,sK2,sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_650,plain,
    ( m1_orders_2(sK4,sK2,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_648,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_652,plain,
    ( m1_orders_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1888,plain,
    ( m1_orders_2(X0,sK2,sK5) != iProver_top
    | r1_tarski(X0,sK5) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v3_orders_2(sK2) != iProver_top
    | v4_orders_2(sK2) != iProver_top
    | v5_orders_2(sK2) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_648,c_652])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_24,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,plain,
    ( v3_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_26,plain,
    ( v4_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_27,plain,
    ( v5_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2411,plain,
    ( r1_tarski(X0,sK5) = iProver_top
    | m1_orders_2(X0,sK2,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1888,c_24,c_25,c_26,c_27,c_28])).

cnf(c_2412,plain,
    ( m1_orders_2(X0,sK2,sK5) != iProver_top
    | r1_tarski(X0,sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_2411])).

cnf(c_2419,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_650,c_2412])).

cnf(c_2420,plain,
    ( r1_tarski(sK4,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2419])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1588,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_orders_2(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,k3_orders_2(sK2,sK5,sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2315,plain,
    ( ~ m1_subset_1(k3_orders_2(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3)) ),
    inference(instantiation,[status(thm)],[c_1588])).

cnf(c_9,plain,
    ( r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1812,plain,
    ( r2_orders_2(sK2,sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK3)
    | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1809,plain,
    ( ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK5)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1806,plain,
    ( ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3))
    | k3_orders_2(sK2,sK4,sK3) = k3_orders_2(sK2,sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1010,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k3_orders_2(sK2,X0,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1096,plain,
    ( m1_subset_1(k3_orders_2(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_1010])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_969,plain,
    ( r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3))
    | k3_orders_2(sK2,sK4,sK3) = k3_orders_2(sK2,sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_13,negated_conjecture,
    ( k3_orders_2(sK2,sK4,sK3) != k3_orders_2(sK2,sK5,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_67885,c_17750,c_10534,c_3847,c_2420,c_2315,c_1812,c_1809,c_1806,c_1096,c_969,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.45/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.45/2.49  
% 15.45/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.45/2.49  
% 15.45/2.49  ------  iProver source info
% 15.45/2.49  
% 15.45/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.45/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.45/2.49  git: non_committed_changes: false
% 15.45/2.49  git: last_make_outside_of_git: false
% 15.45/2.49  
% 15.45/2.49  ------ 
% 15.45/2.49  ------ Parsing...
% 15.45/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.45/2.49  
% 15.45/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.45/2.49  
% 15.45/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.45/2.49  
% 15.45/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.45/2.49  ------ Proving...
% 15.45/2.49  ------ Problem Properties 
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  clauses                                 24
% 15.45/2.49  conjectures                             11
% 15.45/2.49  EPR                                     8
% 15.45/2.49  Horn                                    15
% 15.45/2.49  unary                                   11
% 15.45/2.49  binary                                  2
% 15.45/2.49  lits                                    98
% 15.45/2.49  lits eq                                 3
% 15.45/2.49  fd_pure                                 0
% 15.45/2.49  fd_pseudo                               0
% 15.45/2.49  fd_cond                                 0
% 15.45/2.49  fd_pseudo_cond                          2
% 15.45/2.49  AC symbols                              0
% 15.45/2.49  
% 15.45/2.49  ------ Input Options Time Limit: Unbounded
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  ------ 
% 15.45/2.49  Current options:
% 15.45/2.49  ------ 
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  ------ Proving...
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  % SZS status Theorem for theBenchmark.p
% 15.45/2.49  
% 15.45/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.45/2.49  
% 15.45/2.49  fof(f8,axiom,(
% 15.45/2.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f23,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X1,X4) | (~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 15.45/2.49    inference(ennf_transformation,[],[f8])).
% 15.45/2.49  
% 15.45/2.49  fof(f24,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_hidden(X1,X4) | ~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 15.45/2.49    inference(flattening,[],[f23])).
% 15.45/2.49  
% 15.45/2.49  fof(f53,plain,(
% 15.45/2.49    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X1,X4) | ~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f24])).
% 15.45/2.49  
% 15.45/2.49  fof(f5,axiom,(
% 15.45/2.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f17,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 15.45/2.49    inference(ennf_transformation,[],[f5])).
% 15.45/2.49  
% 15.45/2.49  fof(f18,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 15.45/2.49    inference(flattening,[],[f17])).
% 15.45/2.49  
% 15.45/2.49  fof(f34,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 15.45/2.49    inference(nnf_transformation,[],[f18])).
% 15.45/2.49  
% 15.45/2.49  fof(f35,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 15.45/2.49    inference(flattening,[],[f34])).
% 15.45/2.49  
% 15.45/2.49  fof(f50,plain,(
% 15.45/2.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f35])).
% 15.45/2.49  
% 15.45/2.49  fof(f6,axiom,(
% 15.45/2.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X3) => r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)))))))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f19,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) | ~r1_tarski(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 15.45/2.49    inference(ennf_transformation,[],[f6])).
% 15.45/2.49  
% 15.45/2.49  fof(f20,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) | ~r1_tarski(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 15.45/2.49    inference(flattening,[],[f19])).
% 15.45/2.49  
% 15.45/2.49  fof(f51,plain,(
% 15.45/2.49    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) | ~r1_tarski(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f20])).
% 15.45/2.49  
% 15.45/2.49  fof(f1,axiom,(
% 15.45/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f11,plain,(
% 15.45/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.45/2.49    inference(ennf_transformation,[],[f1])).
% 15.45/2.49  
% 15.45/2.49  fof(f27,plain,(
% 15.45/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.45/2.49    inference(nnf_transformation,[],[f11])).
% 15.45/2.49  
% 15.45/2.49  fof(f28,plain,(
% 15.45/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.45/2.49    inference(rectify,[],[f27])).
% 15.45/2.49  
% 15.45/2.49  fof(f29,plain,(
% 15.45/2.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.45/2.49    introduced(choice_axiom,[])).
% 15.45/2.49  
% 15.45/2.49  fof(f30,plain,(
% 15.45/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.45/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 15.45/2.49  
% 15.45/2.49  fof(f41,plain,(
% 15.45/2.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f30])).
% 15.45/2.49  
% 15.45/2.49  fof(f9,conjecture,(
% 15.45/2.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2)) => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1))))))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f10,negated_conjecture,(
% 15.45/2.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2)) => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1))))))),
% 15.45/2.49    inference(negated_conjecture,[],[f9])).
% 15.45/2.49  
% 15.45/2.49  fof(f25,plain,(
% 15.45/2.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & (m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 15.45/2.49    inference(ennf_transformation,[],[f10])).
% 15.45/2.49  
% 15.45/2.49  fof(f26,plain,(
% 15.45/2.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 15.45/2.49    inference(flattening,[],[f25])).
% 15.45/2.49  
% 15.45/2.49  fof(f39,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k3_orders_2(X0,sK5,X1) != k3_orders_2(X0,X2,X1) & m1_orders_2(X2,X0,sK5) & r2_hidden(X1,X2) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.45/2.49    introduced(choice_axiom,[])).
% 15.45/2.49  
% 15.45/2.49  fof(f38,plain,(
% 15.45/2.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (k3_orders_2(X0,sK4,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(sK4,X0,X3) & r2_hidden(X1,sK4) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.45/2.49    introduced(choice_axiom,[])).
% 15.45/2.49  
% 15.45/2.49  fof(f37,plain,(
% 15.45/2.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k3_orders_2(X0,X2,sK3) != k3_orders_2(X0,X3,sK3) & m1_orders_2(X2,X0,X3) & r2_hidden(sK3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 15.45/2.49    introduced(choice_axiom,[])).
% 15.45/2.49  
% 15.45/2.49  fof(f36,plain,(
% 15.45/2.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(sK2,X2,X1) != k3_orders_2(sK2,X3,X1) & m1_orders_2(X2,sK2,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 15.45/2.49    introduced(choice_axiom,[])).
% 15.45/2.49  
% 15.45/2.49  fof(f40,plain,(
% 15.45/2.49    (((k3_orders_2(sK2,sK4,sK3) != k3_orders_2(sK2,sK5,sK3) & m1_orders_2(sK4,sK2,sK5) & r2_hidden(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 15.45/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f39,f38,f37,f36])).
% 15.45/2.49  
% 15.45/2.49  fof(f63,plain,(
% 15.45/2.49    m1_orders_2(sK4,sK2,sK5)),
% 15.45/2.49    inference(cnf_transformation,[],[f40])).
% 15.45/2.49  
% 15.45/2.49  fof(f61,plain,(
% 15.45/2.49    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))),
% 15.45/2.49    inference(cnf_transformation,[],[f40])).
% 15.45/2.49  
% 15.45/2.49  fof(f7,axiom,(
% 15.45/2.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f21,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 15.45/2.49    inference(ennf_transformation,[],[f7])).
% 15.45/2.49  
% 15.45/2.49  fof(f22,plain,(
% 15.45/2.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 15.45/2.49    inference(flattening,[],[f21])).
% 15.45/2.49  
% 15.45/2.49  fof(f52,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f22])).
% 15.45/2.49  
% 15.45/2.49  fof(f54,plain,(
% 15.45/2.49    ~v2_struct_0(sK2)),
% 15.45/2.49    inference(cnf_transformation,[],[f40])).
% 15.45/2.49  
% 15.45/2.49  fof(f55,plain,(
% 15.45/2.49    v3_orders_2(sK2)),
% 15.45/2.49    inference(cnf_transformation,[],[f40])).
% 15.45/2.49  
% 15.45/2.49  fof(f56,plain,(
% 15.45/2.49    v4_orders_2(sK2)),
% 15.45/2.49    inference(cnf_transformation,[],[f40])).
% 15.45/2.49  
% 15.45/2.49  fof(f57,plain,(
% 15.45/2.49    v5_orders_2(sK2)),
% 15.45/2.49    inference(cnf_transformation,[],[f40])).
% 15.45/2.49  
% 15.45/2.49  fof(f58,plain,(
% 15.45/2.49    l1_orders_2(sK2)),
% 15.45/2.49    inference(cnf_transformation,[],[f40])).
% 15.45/2.49  
% 15.45/2.49  fof(f3,axiom,(
% 15.45/2.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f13,plain,(
% 15.45/2.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 15.45/2.49    inference(ennf_transformation,[],[f3])).
% 15.45/2.49  
% 15.45/2.49  fof(f14,plain,(
% 15.45/2.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 15.45/2.49    inference(flattening,[],[f13])).
% 15.45/2.49  
% 15.45/2.49  fof(f46,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f14])).
% 15.45/2.49  
% 15.45/2.49  fof(f48,plain,(
% 15.45/2.49    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f35])).
% 15.45/2.49  
% 15.45/2.49  fof(f49,plain,(
% 15.45/2.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f35])).
% 15.45/2.49  
% 15.45/2.49  fof(f2,axiom,(
% 15.45/2.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f12,plain,(
% 15.45/2.49    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 15.45/2.49    inference(ennf_transformation,[],[f2])).
% 15.45/2.49  
% 15.45/2.49  fof(f31,plain,(
% 15.45/2.49    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 15.45/2.49    inference(nnf_transformation,[],[f12])).
% 15.45/2.49  
% 15.45/2.49  fof(f32,plain,(
% 15.45/2.49    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 15.45/2.49    introduced(choice_axiom,[])).
% 15.45/2.49  
% 15.45/2.49  fof(f33,plain,(
% 15.45/2.49    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 15.45/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 15.45/2.49  
% 15.45/2.49  fof(f45,plain,(
% 15.45/2.49    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f33])).
% 15.45/2.49  
% 15.45/2.49  fof(f4,axiom,(
% 15.45/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 15.45/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.45/2.49  
% 15.45/2.49  fof(f15,plain,(
% 15.45/2.49    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 15.45/2.49    inference(ennf_transformation,[],[f4])).
% 15.45/2.49  
% 15.45/2.49  fof(f16,plain,(
% 15.45/2.49    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 15.45/2.49    inference(flattening,[],[f15])).
% 15.45/2.49  
% 15.45/2.49  fof(f47,plain,(
% 15.45/2.49    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f16])).
% 15.45/2.49  
% 15.45/2.49  fof(f44,plain,(
% 15.45/2.49    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 15.45/2.49    inference(cnf_transformation,[],[f33])).
% 15.45/2.49  
% 15.45/2.49  fof(f64,plain,(
% 15.45/2.49    k3_orders_2(sK2,sK4,sK3) != k3_orders_2(sK2,sK5,sK3)),
% 15.45/2.49    inference(cnf_transformation,[],[f40])).
% 15.45/2.49  
% 15.45/2.49  fof(f62,plain,(
% 15.45/2.49    r2_hidden(sK3,sK4)),
% 15.45/2.49    inference(cnf_transformation,[],[f40])).
% 15.45/2.49  
% 15.45/2.49  fof(f60,plain,(
% 15.45/2.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 15.45/2.49    inference(cnf_transformation,[],[f40])).
% 15.45/2.49  
% 15.45/2.49  fof(f59,plain,(
% 15.45/2.49    m1_subset_1(sK3,u1_struct_0(sK2))),
% 15.45/2.49    inference(cnf_transformation,[],[f40])).
% 15.45/2.49  
% 15.45/2.49  cnf(c_12,plain,
% 15.45/2.49      ( ~ m1_orders_2(X0,X1,X2)
% 15.45/2.49      | ~ r2_orders_2(X1,X3,X4)
% 15.45/2.49      | ~ m1_subset_1(X4,u1_struct_0(X1))
% 15.45/2.49      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 15.45/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.45/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.45/2.49      | ~ r2_hidden(X3,X2)
% 15.45/2.49      | ~ r2_hidden(X4,X0)
% 15.45/2.49      | r2_hidden(X3,X0)
% 15.45/2.49      | v2_struct_0(X1)
% 15.45/2.49      | ~ v3_orders_2(X1)
% 15.45/2.49      | ~ v4_orders_2(X1)
% 15.45/2.49      | ~ v5_orders_2(X1)
% 15.45/2.49      | ~ l1_orders_2(X1) ),
% 15.45/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_3650,plain,
% 15.45/2.49      ( ~ m1_orders_2(X0,sK2,X1)
% 15.45/2.49      | ~ r2_orders_2(sK2,sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK3)
% 15.45/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
% 15.45/2.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.45/2.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),X1)
% 15.45/2.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),X0)
% 15.45/2.49      | ~ r2_hidden(sK3,X0)
% 15.45/2.49      | v2_struct_0(sK2)
% 15.45/2.49      | ~ v3_orders_2(sK2)
% 15.45/2.49      | ~ v4_orders_2(sK2)
% 15.45/2.49      | ~ v5_orders_2(sK2)
% 15.45/2.49      | ~ l1_orders_2(sK2) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_12]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_23317,plain,
% 15.45/2.49      ( ~ m1_orders_2(sK4,sK2,X0)
% 15.45/2.49      | ~ r2_orders_2(sK2,sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK3)
% 15.45/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
% 15.45/2.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.45/2.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),X0)
% 15.45/2.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4)
% 15.45/2.49      | ~ r2_hidden(sK3,sK4)
% 15.45/2.49      | v2_struct_0(sK2)
% 15.45/2.49      | ~ v3_orders_2(sK2)
% 15.45/2.49      | ~ v4_orders_2(sK2)
% 15.45/2.49      | ~ v5_orders_2(sK2)
% 15.45/2.49      | ~ l1_orders_2(sK2) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_3650]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_67885,plain,
% 15.45/2.49      ( ~ m1_orders_2(sK4,sK2,sK5)
% 15.45/2.49      | ~ r2_orders_2(sK2,sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK3)
% 15.45/2.49      | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
% 15.45/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.45/2.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK5)
% 15.45/2.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4)
% 15.45/2.49      | ~ r2_hidden(sK3,sK4)
% 15.45/2.49      | v2_struct_0(sK2)
% 15.45/2.49      | ~ v3_orders_2(sK2)
% 15.45/2.49      | ~ v4_orders_2(sK2)
% 15.45/2.49      | ~ v5_orders_2(sK2)
% 15.45/2.49      | ~ l1_orders_2(sK2) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_23317]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_7,plain,
% 15.45/2.49      ( ~ r2_orders_2(X0,X1,X2)
% 15.45/2.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.45/2.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.45/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 15.45/2.49      | ~ r2_hidden(X1,X3)
% 15.45/2.49      | r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 15.45/2.49      | v2_struct_0(X0)
% 15.45/2.49      | ~ v3_orders_2(X0)
% 15.45/2.49      | ~ v4_orders_2(X0)
% 15.45/2.49      | ~ v5_orders_2(X0)
% 15.45/2.49      | ~ l1_orders_2(X0) ),
% 15.45/2.49      inference(cnf_transformation,[],[f50]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_3645,plain,
% 15.45/2.49      ( ~ r2_orders_2(sK2,sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK3)
% 15.45/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
% 15.45/2.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.45/2.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),X0)
% 15.45/2.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,X0,sK3))
% 15.45/2.49      | v2_struct_0(sK2)
% 15.45/2.49      | ~ v3_orders_2(sK2)
% 15.45/2.49      | ~ v4_orders_2(sK2)
% 15.45/2.49      | ~ v5_orders_2(sK2)
% 15.45/2.49      | ~ l1_orders_2(sK2) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_7]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_17750,plain,
% 15.45/2.49      ( ~ r2_orders_2(sK2,sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK3)
% 15.45/2.49      | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
% 15.45/2.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.45/2.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3))
% 15.45/2.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4)
% 15.45/2.49      | v2_struct_0(sK2)
% 15.45/2.49      | ~ v3_orders_2(sK2)
% 15.45/2.49      | ~ v4_orders_2(sK2)
% 15.45/2.49      | ~ v5_orders_2(sK2)
% 15.45/2.49      | ~ l1_orders_2(sK2) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_3645]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_10,plain,
% 15.45/2.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.45/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.45/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 15.45/2.49      | ~ r1_tarski(X3,X2)
% 15.45/2.49      | r1_tarski(k3_orders_2(X1,X3,X0),k3_orders_2(X1,X2,X0))
% 15.45/2.49      | v2_struct_0(X1)
% 15.45/2.49      | ~ v3_orders_2(X1)
% 15.45/2.49      | ~ v4_orders_2(X1)
% 15.45/2.49      | ~ v5_orders_2(X1)
% 15.45/2.49      | ~ l1_orders_2(X1) ),
% 15.45/2.49      inference(cnf_transformation,[],[f51]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1015,plain,
% 15.45/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.45/2.49      | ~ r1_tarski(X1,X0)
% 15.45/2.49      | r1_tarski(k3_orders_2(sK2,X1,sK3),k3_orders_2(sK2,X0,sK3))
% 15.45/2.49      | v2_struct_0(sK2)
% 15.45/2.49      | ~ v3_orders_2(sK2)
% 15.45/2.49      | ~ v4_orders_2(sK2)
% 15.45/2.49      | ~ v5_orders_2(sK2)
% 15.45/2.49      | ~ l1_orders_2(sK2) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_10]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1215,plain,
% 15.45/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.45/2.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | r1_tarski(k3_orders_2(sK2,sK4,sK3),k3_orders_2(sK2,X0,sK3))
% 15.45/2.49      | ~ r1_tarski(sK4,X0)
% 15.45/2.49      | v2_struct_0(sK2)
% 15.45/2.49      | ~ v3_orders_2(sK2)
% 15.45/2.49      | ~ v4_orders_2(sK2)
% 15.45/2.49      | ~ v5_orders_2(sK2)
% 15.45/2.49      | ~ l1_orders_2(sK2) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_1015]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_10534,plain,
% 15.45/2.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.45/2.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | r1_tarski(k3_orders_2(sK2,sK4,sK3),k3_orders_2(sK2,sK5,sK3))
% 15.45/2.49      | ~ r1_tarski(sK4,sK5)
% 15.45/2.49      | v2_struct_0(sK2)
% 15.45/2.49      | ~ v3_orders_2(sK2)
% 15.45/2.49      | ~ v4_orders_2(sK2)
% 15.45/2.49      | ~ v5_orders_2(sK2)
% 15.45/2.49      | ~ l1_orders_2(sK2) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_1215]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_2,plain,
% 15.45/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.45/2.49      inference(cnf_transformation,[],[f41]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1573,plain,
% 15.45/2.49      ( ~ r2_hidden(sK1(X0,X1),X2)
% 15.45/2.49      | r2_hidden(sK1(X0,X1),X0)
% 15.45/2.49      | ~ r1_tarski(X2,X0) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_2]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_3847,plain,
% 15.45/2.49      ( r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
% 15.45/2.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3))
% 15.45/2.49      | ~ r1_tarski(k3_orders_2(sK2,sK4,sK3),k3_orders_2(sK2,sK5,sK3)) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_1573]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_14,negated_conjecture,
% 15.45/2.49      ( m1_orders_2(sK4,sK2,sK5) ),
% 15.45/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_650,plain,
% 15.45/2.49      ( m1_orders_2(sK4,sK2,sK5) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_16,negated_conjecture,
% 15.45/2.49      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 15.45/2.49      inference(cnf_transformation,[],[f61]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_648,plain,
% 15.45/2.49      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_11,plain,
% 15.45/2.49      ( ~ m1_orders_2(X0,X1,X2)
% 15.45/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.45/2.49      | r1_tarski(X0,X2)
% 15.45/2.49      | v2_struct_0(X1)
% 15.45/2.49      | ~ v3_orders_2(X1)
% 15.45/2.49      | ~ v4_orders_2(X1)
% 15.45/2.49      | ~ v5_orders_2(X1)
% 15.45/2.49      | ~ l1_orders_2(X1) ),
% 15.45/2.49      inference(cnf_transformation,[],[f52]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_652,plain,
% 15.45/2.49      ( m1_orders_2(X0,X1,X2) != iProver_top
% 15.45/2.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.45/2.49      | r1_tarski(X0,X2) = iProver_top
% 15.45/2.49      | v2_struct_0(X1) = iProver_top
% 15.45/2.49      | v3_orders_2(X1) != iProver_top
% 15.45/2.49      | v4_orders_2(X1) != iProver_top
% 15.45/2.49      | v5_orders_2(X1) != iProver_top
% 15.45/2.49      | l1_orders_2(X1) != iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1888,plain,
% 15.45/2.49      ( m1_orders_2(X0,sK2,sK5) != iProver_top
% 15.45/2.49      | r1_tarski(X0,sK5) = iProver_top
% 15.45/2.49      | v2_struct_0(sK2) = iProver_top
% 15.45/2.49      | v3_orders_2(sK2) != iProver_top
% 15.45/2.49      | v4_orders_2(sK2) != iProver_top
% 15.45/2.49      | v5_orders_2(sK2) != iProver_top
% 15.45/2.49      | l1_orders_2(sK2) != iProver_top ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_648,c_652]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_23,negated_conjecture,
% 15.45/2.49      ( ~ v2_struct_0(sK2) ),
% 15.45/2.49      inference(cnf_transformation,[],[f54]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_24,plain,
% 15.45/2.49      ( v2_struct_0(sK2) != iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_22,negated_conjecture,
% 15.45/2.49      ( v3_orders_2(sK2) ),
% 15.45/2.49      inference(cnf_transformation,[],[f55]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_25,plain,
% 15.45/2.49      ( v3_orders_2(sK2) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_21,negated_conjecture,
% 15.45/2.49      ( v4_orders_2(sK2) ),
% 15.45/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_26,plain,
% 15.45/2.49      ( v4_orders_2(sK2) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_20,negated_conjecture,
% 15.45/2.49      ( v5_orders_2(sK2) ),
% 15.45/2.49      inference(cnf_transformation,[],[f57]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_27,plain,
% 15.45/2.49      ( v5_orders_2(sK2) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_19,negated_conjecture,
% 15.45/2.49      ( l1_orders_2(sK2) ),
% 15.45/2.49      inference(cnf_transformation,[],[f58]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_28,plain,
% 15.45/2.49      ( l1_orders_2(sK2) = iProver_top ),
% 15.45/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_2411,plain,
% 15.45/2.49      ( r1_tarski(X0,sK5) = iProver_top
% 15.45/2.49      | m1_orders_2(X0,sK2,sK5) != iProver_top ),
% 15.45/2.49      inference(global_propositional_subsumption,
% 15.45/2.49                [status(thm)],
% 15.45/2.49                [c_1888,c_24,c_25,c_26,c_27,c_28]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_2412,plain,
% 15.45/2.49      ( m1_orders_2(X0,sK2,sK5) != iProver_top
% 15.45/2.49      | r1_tarski(X0,sK5) = iProver_top ),
% 15.45/2.49      inference(renaming,[status(thm)],[c_2411]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_2419,plain,
% 15.45/2.49      ( r1_tarski(sK4,sK5) = iProver_top ),
% 15.45/2.49      inference(superposition,[status(thm)],[c_650,c_2412]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_2420,plain,
% 15.45/2.49      ( r1_tarski(sK4,sK5) ),
% 15.45/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_2419]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_5,plain,
% 15.45/2.49      ( m1_subset_1(X0,X1)
% 15.45/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.45/2.49      | ~ r2_hidden(X0,X2) ),
% 15.45/2.49      inference(cnf_transformation,[],[f46]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1588,plain,
% 15.45/2.49      ( m1_subset_1(X0,u1_struct_0(sK2))
% 15.45/2.49      | ~ m1_subset_1(k3_orders_2(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ r2_hidden(X0,k3_orders_2(sK2,sK5,sK3)) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_5]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_2315,plain,
% 15.45/2.49      ( ~ m1_subset_1(k3_orders_2(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
% 15.45/2.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3)) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_1588]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_9,plain,
% 15.45/2.49      ( r2_orders_2(X0,X1,X2)
% 15.45/2.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.45/2.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.45/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 15.45/2.49      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 15.45/2.49      | v2_struct_0(X0)
% 15.45/2.49      | ~ v3_orders_2(X0)
% 15.45/2.49      | ~ v4_orders_2(X0)
% 15.45/2.49      | ~ v5_orders_2(X0)
% 15.45/2.49      | ~ l1_orders_2(X0) ),
% 15.45/2.49      inference(cnf_transformation,[],[f48]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1812,plain,
% 15.45/2.49      ( r2_orders_2(sK2,sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK3)
% 15.45/2.49      | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
% 15.45/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.45/2.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
% 15.45/2.49      | v2_struct_0(sK2)
% 15.45/2.49      | ~ v3_orders_2(sK2)
% 15.45/2.49      | ~ v4_orders_2(sK2)
% 15.45/2.49      | ~ v5_orders_2(sK2)
% 15.45/2.49      | ~ l1_orders_2(sK2) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_9]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_8,plain,
% 15.45/2.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.45/2.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.45/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 15.45/2.49      | r2_hidden(X2,X3)
% 15.45/2.49      | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
% 15.45/2.49      | v2_struct_0(X1)
% 15.45/2.49      | ~ v3_orders_2(X1)
% 15.45/2.49      | ~ v4_orders_2(X1)
% 15.45/2.49      | ~ v5_orders_2(X1)
% 15.45/2.49      | ~ l1_orders_2(X1) ),
% 15.45/2.49      inference(cnf_transformation,[],[f49]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1809,plain,
% 15.45/2.49      ( ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
% 15.45/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.45/2.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
% 15.45/2.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK5)
% 15.45/2.49      | v2_struct_0(sK2)
% 15.45/2.49      | ~ v3_orders_2(sK2)
% 15.45/2.49      | ~ v4_orders_2(sK2)
% 15.45/2.49      | ~ v5_orders_2(sK2)
% 15.45/2.49      | ~ l1_orders_2(sK2) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_8]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_3,plain,
% 15.45/2.49      ( ~ r2_hidden(sK1(X0,X1),X1)
% 15.45/2.49      | ~ r2_hidden(sK1(X0,X1),X0)
% 15.45/2.49      | X1 = X0 ),
% 15.45/2.49      inference(cnf_transformation,[],[f45]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1806,plain,
% 15.45/2.49      ( ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
% 15.45/2.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3))
% 15.45/2.49      | k3_orders_2(sK2,sK4,sK3) = k3_orders_2(sK2,sK5,sK3) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_3]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_6,plain,
% 15.45/2.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 15.45/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.45/2.49      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.45/2.49      | v2_struct_0(X1)
% 15.45/2.49      | ~ v3_orders_2(X1)
% 15.45/2.49      | ~ v4_orders_2(X1)
% 15.45/2.49      | ~ v5_orders_2(X1)
% 15.45/2.49      | ~ l1_orders_2(X1) ),
% 15.45/2.49      inference(cnf_transformation,[],[f47]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1010,plain,
% 15.45/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | m1_subset_1(k3_orders_2(sK2,X0,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.45/2.49      | v2_struct_0(sK2)
% 15.45/2.49      | ~ v3_orders_2(sK2)
% 15.45/2.49      | ~ v4_orders_2(sK2)
% 15.45/2.49      | ~ v5_orders_2(sK2)
% 15.45/2.49      | ~ l1_orders_2(sK2) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_6]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_1096,plain,
% 15.45/2.49      ( m1_subset_1(k3_orders_2(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.45/2.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.45/2.49      | v2_struct_0(sK2)
% 15.45/2.49      | ~ v3_orders_2(sK2)
% 15.45/2.49      | ~ v4_orders_2(sK2)
% 15.45/2.49      | ~ v5_orders_2(sK2)
% 15.45/2.49      | ~ l1_orders_2(sK2) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_1010]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_4,plain,
% 15.45/2.49      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 15.45/2.49      inference(cnf_transformation,[],[f44]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_969,plain,
% 15.45/2.49      ( r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
% 15.45/2.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3))
% 15.45/2.49      | k3_orders_2(sK2,sK4,sK3) = k3_orders_2(sK2,sK5,sK3) ),
% 15.45/2.49      inference(instantiation,[status(thm)],[c_4]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_13,negated_conjecture,
% 15.45/2.49      ( k3_orders_2(sK2,sK4,sK3) != k3_orders_2(sK2,sK5,sK3) ),
% 15.45/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_15,negated_conjecture,
% 15.45/2.49      ( r2_hidden(sK3,sK4) ),
% 15.45/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_17,negated_conjecture,
% 15.45/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 15.45/2.49      inference(cnf_transformation,[],[f60]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(c_18,negated_conjecture,
% 15.45/2.49      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 15.45/2.49      inference(cnf_transformation,[],[f59]) ).
% 15.45/2.49  
% 15.45/2.49  cnf(contradiction,plain,
% 15.45/2.49      ( $false ),
% 15.45/2.49      inference(minisat,
% 15.45/2.49                [status(thm)],
% 15.45/2.49                [c_67885,c_17750,c_10534,c_3847,c_2420,c_2315,c_1812,
% 15.45/2.49                 c_1809,c_1806,c_1096,c_969,c_13,c_14,c_15,c_16,c_17,
% 15.45/2.49                 c_18,c_19,c_20,c_21,c_22,c_23]) ).
% 15.45/2.49  
% 15.45/2.49  
% 15.45/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.45/2.49  
% 15.45/2.49  ------                               Statistics
% 15.45/2.49  
% 15.45/2.49  ------ Selected
% 15.45/2.49  
% 15.45/2.49  total_time:                             1.986
% 15.45/2.49  
%------------------------------------------------------------------------------
