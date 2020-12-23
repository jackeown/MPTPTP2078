%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:42 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  176 (3241 expanded)
%              Number of clauses        :  118 ( 625 expanded)
%              Number of leaves         :   15 (1188 expanded)
%              Depth                    :   29
%              Number of atoms          :  955 (29054 expanded)
%              Number of equality atoms :  250 (3403 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1)
          & m1_orders_2(X2,X0,X3)
          & r2_hidden(X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k3_orders_2(X0,sK4,X1) != k3_orders_2(X0,X2,X1)
        & m1_orders_2(X2,X0,sK4)
        & r2_hidden(X1,X2)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1)
              & m1_orders_2(X2,X0,X3)
              & r2_hidden(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( k3_orders_2(X0,sK3,X1) != k3_orders_2(X0,X3,X1)
            & m1_orders_2(sK3,X0,X3)
            & r2_hidden(X1,sK3)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
                ( k3_orders_2(X0,X2,sK2) != k3_orders_2(X0,X3,sK2)
                & m1_orders_2(X2,X0,X3)
                & r2_hidden(sK2,X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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
                  ( k3_orders_2(sK1,X2,X1) != k3_orders_2(sK1,X3,X1)
                  & m1_orders_2(X2,sK1,X3)
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k3_orders_2(sK1,sK3,sK2) != k3_orders_2(sK1,sK4,sK2)
    & m1_orders_2(sK3,sK1,sK4)
    & r2_hidden(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f22,f34,f33,f32,f31])).

fof(f57,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f50,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f13,plain,(
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

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    m1_orders_2(sK3,sK1,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    k3_orders_2(sK1,sK3,sK2) != k3_orders_2(sK1,sK4,sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_847,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_852,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f45])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_22,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_21,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_23,c_22,c_21,c_20])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(sK1,X2,X0)) ),
    inference(renaming,[status(thm)],[c_390])).

cnf(c_840,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | r2_hidden(X1,k3_orders_2(sK1,X2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_1275,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(k3_orders_2(sK1,X1,X0),X2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X2),X1) = iProver_top
    | r1_tarski(k3_orders_2(sK1,X1,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_852,c_840])).

cnf(c_1168,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(k3_orders_2(sK1,X1,X0),X2),u1_struct_0(sK1))
    | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X2),X1)
    | r1_tarski(k3_orders_2(sK1,X1,X0),X2) ),
    inference(resolution,[status(thm)],[c_391,c_1])).

cnf(c_1169,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(k3_orders_2(sK1,X1,X0),X2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X2),X1) = iProver_top
    | r1_tarski(k3_orders_2(sK1,X1,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1168])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_23,c_22,c_21,c_20])).

cnf(c_839,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_848,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1481,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1,k3_orders_2(sK1,X2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_848])).

cnf(c_2146,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(k3_orders_2(sK1,X1,X0),X2),u1_struct_0(sK1)) = iProver_top
    | r1_tarski(k3_orders_2(sK1,X1,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_852,c_1481])).

cnf(c_2258,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X2),X1) = iProver_top
    | r1_tarski(k3_orders_2(sK1,X1,X0),X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1275,c_1169,c_2146])).

cnf(c_2259,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X2),X1) = iProver_top
    | r1_tarski(k3_orders_2(sK1,X1,X0),X2) = iProver_top ),
    inference(renaming,[status(thm)],[c_2258])).

cnf(c_10,plain,
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
    inference(cnf_transformation,[],[f44])).

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
    inference(cnf_transformation,[],[f48])).

cnf(c_14,negated_conjecture,
    ( m1_orders_2(sK3,sK1,sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_236,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,X4)
    | r2_hidden(X1,X4)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X3
    | sK3 != X4
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_237,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X1,sK3)
    | r2_hidden(X0,sK3)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_239,plain,
    ( r2_hidden(X0,sK3)
    | ~ r2_hidden(X1,sK3)
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_orders_2(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_237,c_23,c_22,c_21,c_20,c_19,c_17,c_16])).

cnf(c_240,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X1,sK3)
    | r2_hidden(X0,sK3) ),
    inference(renaming,[status(thm)],[c_239])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X4,u1_struct_0(sK1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,k3_orders_2(X1,X5,X2))
    | ~ r2_hidden(X4,sK4)
    | ~ r2_hidden(X3,sK3)
    | r2_hidden(X4,sK3)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X4 != X0
    | X3 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_240])).

cnf(c_322,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k3_orders_2(sK1,X2,X0))
    | ~ r2_hidden(X1,sK4)
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(X1,sK3)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_324,plain,
    ( r2_hidden(X1,sK3)
    | ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X1,sK4)
    | ~ r2_hidden(X1,k3_orders_2(sK1,X2,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_322,c_23,c_22,c_21,c_20,c_19])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X1,sK3)
    | r2_hidden(X0,sK3) ),
    inference(renaming,[status(thm)],[c_324])).

cnf(c_842,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0,k3_orders_2(sK1,X2,X1)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_326,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0,k3_orders_2(sK1,X2,X1)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_846,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1479,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_846,c_848])).

cnf(c_1616,plain,
    ( m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0,k3_orders_2(sK1,X2,X1)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_842,c_326,c_1479])).

cnf(c_1617,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X2,k3_orders_2(sK1,X1,X0)) != iProver_top
    | r2_hidden(X2,sK4) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X2,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_1616])).

cnf(c_845,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1480,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_845,c_848])).

cnf(c_1482,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1479])).

cnf(c_1490,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X1,sK3)
    | r2_hidden(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_1482])).

cnf(c_1491,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X2,k3_orders_2(sK1,X1,X0))
    | ~ r2_hidden(X2,sK4)
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(X2,sK3) ),
    inference(renaming,[status(thm)],[c_1490])).

cnf(c_1492,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X2,k3_orders_2(sK1,X1,X0)) != iProver_top
    | r2_hidden(X2,sK4) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1491])).

cnf(c_1620,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X2,k3_orders_2(sK1,X1,X0)) != iProver_top
    | r2_hidden(X2,sK4) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1617,c_1480,c_1492])).

cnf(c_1621,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1,k3_orders_2(sK1,X0,X2)) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(X2,sK3) != iProver_top
    | r2_hidden(X1,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_1620])).

cnf(c_1624,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X0,X1),X2),sK4) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X0,X1),X2),sK3) = iProver_top
    | r1_tarski(k3_orders_2(sK1,X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_852,c_1621])).

cnf(c_2935,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,sK4,X0),X1),sK3) = iProver_top
    | r1_tarski(k3_orders_2(sK1,sK4,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2259,c_1624])).

cnf(c_31,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2065,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k3_orders_2(sK1,X2,X0)) ),
    inference(resolution,[status(thm)],[c_6,c_417])).

cnf(c_2555,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k3_orders_2(sK1,X1,X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2065,c_391])).

cnf(c_2576,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X2),X1)
    | r1_tarski(k3_orders_2(sK1,X1,X0),X2) ),
    inference(resolution,[status(thm)],[c_2555,c_1])).

cnf(c_1485,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1480])).

cnf(c_1494,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X2,k3_orders_2(sK1,X1,X0))
    | ~ r2_hidden(X2,sK4)
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1491,c_1485])).

cnf(c_1495,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k3_orders_2(sK1,X0,X2))
    | ~ r2_hidden(X1,sK4)
    | ~ r2_hidden(X2,sK3)
    | r2_hidden(X1,sK3) ),
    inference(renaming,[status(thm)],[c_1494])).

cnf(c_1522,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,sK3)
    | ~ r2_hidden(sK0(k3_orders_2(sK1,X0,X1),X2),sK4)
    | r2_hidden(sK0(k3_orders_2(sK1,X0,X1),X2),sK3)
    | r1_tarski(k3_orders_2(sK1,X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_1495,c_1])).

cnf(c_2752,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(sK0(k3_orders_2(sK1,sK4,X0),X1),sK3)
    | r1_tarski(k3_orders_2(sK1,sK4,X0),X1) ),
    inference(resolution,[status(thm)],[c_2576,c_1522])).

cnf(c_2753,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,sK4,X0),X1),sK3) = iProver_top
    | r1_tarski(k3_orders_2(sK1,sK4,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2752])).

cnf(c_5295,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,sK4,X0),X1),sK3) = iProver_top
    | r1_tarski(k3_orders_2(sK1,sK4,X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2935,c_31,c_1480,c_2753])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_849,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_851,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1472,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_852,c_851])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f46])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
    | r2_hidden(X2,k3_orders_2(X1,X4,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(resolution,[status(thm)],[c_10,c_8])).

cnf(c_308,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X4,k3_orders_2(X1,X2,X0))
    | r2_hidden(X4,k3_orders_2(X1,X3,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_282,c_6])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X4,k3_orders_2(X1,X2,X0))
    | r2_hidden(X4,k3_orders_2(X1,X3,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_308,c_19])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,k3_orders_2(sK1,X1,X0))
    | r2_hidden(X3,k3_orders_2(sK1,X2,X0))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,k3_orders_2(sK1,X1,X0))
    | r2_hidden(X3,k3_orders_2(sK1,X2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_23,c_22,c_21,c_20])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X3,k3_orders_2(sK1,X2,X0))
    | r2_hidden(X3,k3_orders_2(sK1,X1,X0)) ),
    inference(renaming,[status(thm)],[c_362])).

cnf(c_841,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(X3,k3_orders_2(sK1,X1,X0)) != iProver_top
    | r2_hidden(X3,k3_orders_2(sK1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_1850,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK0(X3,X4),X2) != iProver_top
    | r2_hidden(sK0(X3,X4),k3_orders_2(sK1,X2,X0)) = iProver_top
    | r1_tarski(X3,X4) = iProver_top
    | r1_tarski(X3,k3_orders_2(sK1,X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1472,c_841])).

cnf(c_3577,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X2,X0),X3),X1) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X2,X0),X3),k3_orders_2(sK1,X1,X0)) = iProver_top
    | r1_tarski(k3_orders_2(sK1,X2,X0),X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_849,c_1850])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_853,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3586,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),k3_orders_2(sK1,X2,X0)),X2) != iProver_top
    | r1_tarski(k3_orders_2(sK1,X1,X0),k3_orders_2(sK1,X2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3577,c_853])).

cnf(c_5305,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(k3_orders_2(sK1,sK4,X0),k3_orders_2(sK1,sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5295,c_3586])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11624,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(k3_orders_2(sK1,sK4,X0),k3_orders_2(sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5305,c_30,c_31,c_1480])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_850,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11630,plain,
    ( k3_orders_2(sK1,sK3,X0) = k3_orders_2(sK1,sK4,X0)
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(k3_orders_2(sK1,sK3,X0),k3_orders_2(sK1,sK4,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11624,c_850])).

cnf(c_24,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_25,plain,
    ( v3_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_26,plain,
    ( v4_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_27,plain,
    ( v5_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_28,plain,
    ( l1_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_262,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X0
    | sK3 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_263,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,sK4)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_264,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v3_orders_2(sK1) != iProver_top
    | v4_orders_2(sK1) != iProver_top
    | v5_orders_2(sK1) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_263])).

cnf(c_2265,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X2),X3) = iProver_top
    | r1_tarski(X1,X3) != iProver_top
    | r1_tarski(k3_orders_2(sK1,X1,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2259,c_851])).

cnf(c_1360,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X3),X2) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X3),k3_orders_2(sK1,X2,X0)) = iProver_top
    | r1_tarski(k3_orders_2(sK1,X1,X0),X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_852,c_841])).

cnf(c_2715,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X2,X0),k3_orders_2(sK1,X1,X0)),X1) != iProver_top
    | r1_tarski(k3_orders_2(sK1,X2,X0),k3_orders_2(sK1,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1360,c_853])).

cnf(c_3099,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_orders_2(sK1,X2,X0),k3_orders_2(sK1,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2265,c_2715])).

cnf(c_11240,plain,
    ( k3_orders_2(sK1,X0,X1) = k3_orders_2(sK1,X2,X1)
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(k3_orders_2(sK1,X0,X1),k3_orders_2(sK1,X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_850])).

cnf(c_11647,plain,
    ( k3_orders_2(sK1,sK3,X0) = k3_orders_2(sK1,sK4,X0)
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_11624,c_11240])).

cnf(c_11893,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | k3_orders_2(sK1,sK3,X0) = k3_orders_2(sK1,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11630,c_24,c_25,c_26,c_27,c_28,c_30,c_31,c_264,c_1480,c_11647])).

cnf(c_11894,plain,
    ( k3_orders_2(sK1,sK3,X0) = k3_orders_2(sK1,sK4,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_11893])).

cnf(c_11900,plain,
    ( k3_orders_2(sK1,sK4,sK2) = k3_orders_2(sK1,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_847,c_11894])).

cnf(c_552,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1049,plain,
    ( k3_orders_2(sK1,sK3,sK2) = k3_orders_2(sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_552])).

cnf(c_553,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_928,plain,
    ( k3_orders_2(sK1,sK4,sK2) != X0
    | k3_orders_2(sK1,sK3,sK2) != X0
    | k3_orders_2(sK1,sK3,sK2) = k3_orders_2(sK1,sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(c_1048,plain,
    ( k3_orders_2(sK1,sK4,sK2) != k3_orders_2(sK1,sK3,sK2)
    | k3_orders_2(sK1,sK3,sK2) = k3_orders_2(sK1,sK4,sK2)
    | k3_orders_2(sK1,sK3,sK2) != k3_orders_2(sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_928])).

cnf(c_13,negated_conjecture,
    ( k3_orders_2(sK1,sK3,sK2) != k3_orders_2(sK1,sK4,sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11900,c_1049,c_1048,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.78/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.00  
% 3.78/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/1.00  
% 3.78/1.00  ------  iProver source info
% 3.78/1.00  
% 3.78/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.78/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/1.00  git: non_committed_changes: false
% 3.78/1.00  git: last_make_outside_of_git: false
% 3.78/1.00  
% 3.78/1.00  ------ 
% 3.78/1.00  ------ Parsing...
% 3.78/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/1.00  
% 3.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.78/1.00  
% 3.78/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/1.00  
% 3.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/1.00  ------ Proving...
% 3.78/1.00  ------ Problem Properties 
% 3.78/1.00  
% 3.78/1.00  
% 3.78/1.00  clauses                                 16
% 3.78/1.00  conjectures                             5
% 3.78/1.00  EPR                                     5
% 3.78/1.00  Horn                                    15
% 3.78/1.00  unary                                   7
% 3.78/1.00  binary                                  2
% 3.78/1.00  lits                                    41
% 3.78/1.00  lits eq                                 2
% 3.78/1.00  fd_pure                                 0
% 3.78/1.00  fd_pseudo                               0
% 3.78/1.00  fd_cond                                 0
% 3.78/1.00  fd_pseudo_cond                          1
% 3.78/1.00  AC symbols                              0
% 3.78/1.00  
% 3.78/1.00  ------ Input Options Time Limit: Unbounded
% 3.78/1.00  
% 3.78/1.00  
% 3.78/1.00  ------ 
% 3.78/1.00  Current options:
% 3.78/1.00  ------ 
% 3.78/1.00  
% 3.78/1.00  
% 3.78/1.00  
% 3.78/1.00  
% 3.78/1.00  ------ Proving...
% 3.78/1.00  
% 3.78/1.00  
% 3.78/1.00  % SZS status Theorem for theBenchmark.p
% 3.78/1.00  
% 3.78/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/1.00  
% 3.78/1.00  fof(f8,conjecture,(
% 3.78/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2)) => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1))))))),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f9,negated_conjecture,(
% 3.78/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2)) => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1))))))),
% 3.78/1.00    inference(negated_conjecture,[],[f8])).
% 3.78/1.00  
% 3.78/1.00  fof(f21,plain,(
% 3.78/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & (m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.78/1.00    inference(ennf_transformation,[],[f9])).
% 3.78/1.00  
% 3.78/1.00  fof(f22,plain,(
% 3.78/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.78/1.00    inference(flattening,[],[f21])).
% 3.78/1.00  
% 3.78/1.00  fof(f34,plain,(
% 3.78/1.00    ( ! [X2,X0,X1] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k3_orders_2(X0,sK4,X1) != k3_orders_2(X0,X2,X1) & m1_orders_2(X2,X0,sK4) & r2_hidden(X1,X2) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.78/1.00    introduced(choice_axiom,[])).
% 3.78/1.00  
% 3.78/1.00  fof(f33,plain,(
% 3.78/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (k3_orders_2(X0,sK3,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(sK3,X0,X3) & r2_hidden(X1,sK3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.78/1.00    introduced(choice_axiom,[])).
% 3.78/1.00  
% 3.78/1.00  fof(f32,plain,(
% 3.78/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k3_orders_2(X0,X2,sK2) != k3_orders_2(X0,X3,sK2) & m1_orders_2(X2,X0,X3) & r2_hidden(sK2,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 3.78/1.00    introduced(choice_axiom,[])).
% 3.78/1.00  
% 3.78/1.00  fof(f31,plain,(
% 3.78/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(sK1,X2,X1) != k3_orders_2(sK1,X3,X1) & m1_orders_2(X2,sK1,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 3.78/1.00    introduced(choice_axiom,[])).
% 3.78/1.00  
% 3.78/1.00  fof(f35,plain,(
% 3.78/1.00    (((k3_orders_2(sK1,sK3,sK2) != k3_orders_2(sK1,sK4,sK2) & m1_orders_2(sK3,sK1,sK4) & r2_hidden(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 3.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f22,f34,f33,f32,f31])).
% 3.78/1.00  
% 3.78/1.00  fof(f57,plain,(
% 3.78/1.00    r2_hidden(sK2,sK3)),
% 3.78/1.00    inference(cnf_transformation,[],[f35])).
% 3.78/1.00  
% 3.78/1.00  fof(f1,axiom,(
% 3.78/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f10,plain,(
% 3.78/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.78/1.00    inference(ennf_transformation,[],[f1])).
% 3.78/1.00  
% 3.78/1.00  fof(f23,plain,(
% 3.78/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.78/1.00    inference(nnf_transformation,[],[f10])).
% 3.78/1.00  
% 3.78/1.00  fof(f24,plain,(
% 3.78/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.78/1.00    inference(rectify,[],[f23])).
% 3.78/1.00  
% 3.78/1.00  fof(f25,plain,(
% 3.78/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.78/1.00    introduced(choice_axiom,[])).
% 3.78/1.00  
% 3.78/1.00  fof(f26,plain,(
% 3.78/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 3.78/1.00  
% 3.78/1.00  fof(f37,plain,(
% 3.78/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f26])).
% 3.78/1.00  
% 3.78/1.00  fof(f5,axiom,(
% 3.78/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f15,plain,(
% 3.78/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.78/1.00    inference(ennf_transformation,[],[f5])).
% 3.78/1.00  
% 3.78/1.00  fof(f16,plain,(
% 3.78/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.78/1.00    inference(flattening,[],[f15])).
% 3.78/1.00  
% 3.78/1.00  fof(f29,plain,(
% 3.78/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.78/1.00    inference(nnf_transformation,[],[f16])).
% 3.78/1.00  
% 3.78/1.00  fof(f30,plain,(
% 3.78/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.78/1.00    inference(flattening,[],[f29])).
% 3.78/1.00  
% 3.78/1.00  fof(f45,plain,(
% 3.78/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f30])).
% 3.78/1.00  
% 3.78/1.00  fof(f53,plain,(
% 3.78/1.00    l1_orders_2(sK1)),
% 3.78/1.00    inference(cnf_transformation,[],[f35])).
% 3.78/1.00  
% 3.78/1.00  fof(f49,plain,(
% 3.78/1.00    ~v2_struct_0(sK1)),
% 3.78/1.00    inference(cnf_transformation,[],[f35])).
% 3.78/1.00  
% 3.78/1.00  fof(f50,plain,(
% 3.78/1.00    v3_orders_2(sK1)),
% 3.78/1.00    inference(cnf_transformation,[],[f35])).
% 3.78/1.00  
% 3.78/1.00  fof(f51,plain,(
% 3.78/1.00    v4_orders_2(sK1)),
% 3.78/1.00    inference(cnf_transformation,[],[f35])).
% 3.78/1.00  
% 3.78/1.00  fof(f52,plain,(
% 3.78/1.00    v5_orders_2(sK1)),
% 3.78/1.00    inference(cnf_transformation,[],[f35])).
% 3.78/1.00  
% 3.78/1.00  fof(f4,axiom,(
% 3.78/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f13,plain,(
% 3.78/1.00    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.78/1.00    inference(ennf_transformation,[],[f4])).
% 3.78/1.00  
% 3.78/1.00  fof(f14,plain,(
% 3.78/1.00    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.78/1.00    inference(flattening,[],[f13])).
% 3.78/1.00  
% 3.78/1.00  fof(f43,plain,(
% 3.78/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f14])).
% 3.78/1.00  
% 3.78/1.00  fof(f3,axiom,(
% 3.78/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f11,plain,(
% 3.78/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.78/1.00    inference(ennf_transformation,[],[f3])).
% 3.78/1.00  
% 3.78/1.00  fof(f12,plain,(
% 3.78/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.78/1.00    inference(flattening,[],[f11])).
% 3.78/1.00  
% 3.78/1.00  fof(f42,plain,(
% 3.78/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f12])).
% 3.78/1.00  
% 3.78/1.00  fof(f44,plain,(
% 3.78/1.00    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f30])).
% 3.78/1.00  
% 3.78/1.00  fof(f7,axiom,(
% 3.78/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f19,plain,(
% 3.78/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X1,X4) | (~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.78/1.00    inference(ennf_transformation,[],[f7])).
% 3.78/1.00  
% 3.78/1.00  fof(f20,plain,(
% 3.78/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_hidden(X1,X4) | ~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.78/1.00    inference(flattening,[],[f19])).
% 3.78/1.00  
% 3.78/1.00  fof(f48,plain,(
% 3.78/1.00    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X1,X4) | ~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f20])).
% 3.78/1.00  
% 3.78/1.00  fof(f58,plain,(
% 3.78/1.00    m1_orders_2(sK3,sK1,sK4)),
% 3.78/1.00    inference(cnf_transformation,[],[f35])).
% 3.78/1.00  
% 3.78/1.00  fof(f55,plain,(
% 3.78/1.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.78/1.00    inference(cnf_transformation,[],[f35])).
% 3.78/1.00  
% 3.78/1.00  fof(f56,plain,(
% 3.78/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.78/1.00    inference(cnf_transformation,[],[f35])).
% 3.78/1.00  
% 3.78/1.00  fof(f2,axiom,(
% 3.78/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f27,plain,(
% 3.78/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.78/1.00    inference(nnf_transformation,[],[f2])).
% 3.78/1.00  
% 3.78/1.00  fof(f28,plain,(
% 3.78/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.78/1.00    inference(flattening,[],[f27])).
% 3.78/1.00  
% 3.78/1.00  fof(f40,plain,(
% 3.78/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.78/1.00    inference(cnf_transformation,[],[f28])).
% 3.78/1.00  
% 3.78/1.00  fof(f60,plain,(
% 3.78/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.78/1.00    inference(equality_resolution,[],[f40])).
% 3.78/1.00  
% 3.78/1.00  fof(f36,plain,(
% 3.78/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f26])).
% 3.78/1.00  
% 3.78/1.00  fof(f46,plain,(
% 3.78/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f30])).
% 3.78/1.00  
% 3.78/1.00  fof(f38,plain,(
% 3.78/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f26])).
% 3.78/1.00  
% 3.78/1.00  fof(f41,plain,(
% 3.78/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f28])).
% 3.78/1.00  
% 3.78/1.00  fof(f6,axiom,(
% 3.78/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 3.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/1.00  
% 3.78/1.00  fof(f17,plain,(
% 3.78/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.78/1.00    inference(ennf_transformation,[],[f6])).
% 3.78/1.00  
% 3.78/1.00  fof(f18,plain,(
% 3.78/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.78/1.00    inference(flattening,[],[f17])).
% 3.78/1.00  
% 3.78/1.00  fof(f47,plain,(
% 3.78/1.00    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.78/1.00    inference(cnf_transformation,[],[f18])).
% 3.78/1.00  
% 3.78/1.00  fof(f59,plain,(
% 3.78/1.00    k3_orders_2(sK1,sK3,sK2) != k3_orders_2(sK1,sK4,sK2)),
% 3.78/1.00    inference(cnf_transformation,[],[f35])).
% 3.78/1.00  
% 3.78/1.00  cnf(c_15,negated_conjecture,
% 3.78/1.00      ( r2_hidden(sK2,sK3) ),
% 3.78/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_847,plain,
% 3.78/1.00      ( r2_hidden(sK2,sK3) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1,plain,
% 3.78/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_852,plain,
% 3.78/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.78/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_9,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.78/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.78/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | r2_hidden(X2,X3)
% 3.78/1.00      | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
% 3.78/1.00      | v2_struct_0(X1)
% 3.78/1.00      | ~ v3_orders_2(X1)
% 3.78/1.00      | ~ v4_orders_2(X1)
% 3.78/1.00      | ~ v5_orders_2(X1)
% 3.78/1.00      | ~ l1_orders_2(X1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_19,negated_conjecture,
% 3.78/1.00      ( l1_orders_2(sK1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_385,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.78/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.78/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | r2_hidden(X2,X3)
% 3.78/1.00      | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
% 3.78/1.00      | v2_struct_0(X1)
% 3.78/1.00      | ~ v3_orders_2(X1)
% 3.78/1.00      | ~ v4_orders_2(X1)
% 3.78/1.00      | ~ v5_orders_2(X1)
% 3.78/1.00      | sK1 != X1 ),
% 3.78/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_386,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | r2_hidden(X0,X2)
% 3.78/1.00      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 3.78/1.00      | v2_struct_0(sK1)
% 3.78/1.00      | ~ v3_orders_2(sK1)
% 3.78/1.00      | ~ v4_orders_2(sK1)
% 3.78/1.00      | ~ v5_orders_2(sK1) ),
% 3.78/1.00      inference(unflattening,[status(thm)],[c_385]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_23,negated_conjecture,
% 3.78/1.00      ( ~ v2_struct_0(sK1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_22,negated_conjecture,
% 3.78/1.00      ( v3_orders_2(sK1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_21,negated_conjecture,
% 3.78/1.00      ( v4_orders_2(sK1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_20,negated_conjecture,
% 3.78/1.00      ( v5_orders_2(sK1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_390,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | r2_hidden(X0,X2)
% 3.78/1.00      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1)) ),
% 3.78/1.00      inference(global_propositional_subsumption,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_386,c_23,c_22,c_21,c_20]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_391,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | r2_hidden(X1,X2)
% 3.78/1.00      | ~ r2_hidden(X1,k3_orders_2(sK1,X2,X0)) ),
% 3.78/1.00      inference(renaming,[status(thm)],[c_390]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_840,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(X1,X2) = iProver_top
% 3.78/1.00      | r2_hidden(X1,k3_orders_2(sK1,X2,X0)) != iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1275,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | m1_subset_1(sK0(k3_orders_2(sK1,X1,X0),X2),u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X2),X1) = iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,X1,X0),X2) = iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_852,c_840]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1168,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ m1_subset_1(sK0(k3_orders_2(sK1,X1,X0),X2),u1_struct_0(sK1))
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X2),X1)
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,X1,X0),X2) ),
% 3.78/1.00      inference(resolution,[status(thm)],[c_391,c_1]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1169,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | m1_subset_1(sK0(k3_orders_2(sK1,X1,X0),X2),u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X2),X1) = iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,X1,X0),X2) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_1168]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_7,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | v2_struct_0(X1)
% 3.78/1.00      | ~ v3_orders_2(X1)
% 3.78/1.00      | ~ v4_orders_2(X1)
% 3.78/1.00      | ~ v5_orders_2(X1)
% 3.78/1.00      | ~ l1_orders_2(X1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_412,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | v2_struct_0(X1)
% 3.78/1.00      | ~ v3_orders_2(X1)
% 3.78/1.00      | ~ v4_orders_2(X1)
% 3.78/1.00      | ~ v5_orders_2(X1)
% 3.78/1.00      | sK1 != X1 ),
% 3.78/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_413,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | v2_struct_0(sK1)
% 3.78/1.00      | ~ v3_orders_2(sK1)
% 3.78/1.00      | ~ v4_orders_2(sK1)
% 3.78/1.00      | ~ v5_orders_2(sK1) ),
% 3.78/1.00      inference(unflattening,[status(thm)],[c_412]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_417,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.78/1.00      inference(global_propositional_subsumption,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_413,c_23,c_22,c_21,c_20]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_839,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_6,plain,
% 3.78/1.00      ( m1_subset_1(X0,X1)
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.78/1.00      | ~ r2_hidden(X0,X2) ),
% 3.78/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_848,plain,
% 3.78/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.78/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.78/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1481,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,u1_struct_0(sK1)) = iProver_top
% 3.78/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(X1,k3_orders_2(sK1,X2,X0)) != iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_839,c_848]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_2146,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | m1_subset_1(sK0(k3_orders_2(sK1,X1,X0),X2),u1_struct_0(sK1)) = iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,X1,X0),X2) = iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_852,c_1481]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_2258,plain,
% 3.78/1.00      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X2),X1) = iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,X1,X0),X2) = iProver_top ),
% 3.78/1.00      inference(global_propositional_subsumption,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_1275,c_1169,c_2146]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_2259,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X2),X1) = iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,X1,X0),X2) = iProver_top ),
% 3.78/1.00      inference(renaming,[status(thm)],[c_2258]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_10,plain,
% 3.78/1.00      ( r2_orders_2(X0,X1,X2)
% 3.78/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.78/1.00      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 3.78/1.00      | v2_struct_0(X0)
% 3.78/1.00      | ~ v3_orders_2(X0)
% 3.78/1.00      | ~ v4_orders_2(X0)
% 3.78/1.00      | ~ v5_orders_2(X0)
% 3.78/1.00      | ~ l1_orders_2(X0) ),
% 3.78/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_12,plain,
% 3.78/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 3.78/1.00      | ~ r2_orders_2(X1,X3,X4)
% 3.78/1.00      | ~ m1_subset_1(X4,u1_struct_0(X1))
% 3.78/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | ~ r2_hidden(X3,X2)
% 3.78/1.00      | ~ r2_hidden(X4,X0)
% 3.78/1.00      | r2_hidden(X3,X0)
% 3.78/1.00      | v2_struct_0(X1)
% 3.78/1.00      | ~ v3_orders_2(X1)
% 3.78/1.00      | ~ v4_orders_2(X1)
% 3.78/1.00      | ~ v5_orders_2(X1)
% 3.78/1.00      | ~ l1_orders_2(X1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_14,negated_conjecture,
% 3.78/1.00      ( m1_orders_2(sK3,sK1,sK4) ),
% 3.78/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_236,plain,
% 3.78/1.00      ( ~ r2_orders_2(X0,X1,X2)
% 3.78/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.78/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
% 3.78/1.00      | ~ r2_hidden(X1,X3)
% 3.78/1.00      | ~ r2_hidden(X2,X4)
% 3.78/1.00      | r2_hidden(X1,X4)
% 3.78/1.00      | v2_struct_0(X0)
% 3.78/1.00      | ~ v3_orders_2(X0)
% 3.78/1.00      | ~ v4_orders_2(X0)
% 3.78/1.00      | ~ v5_orders_2(X0)
% 3.78/1.00      | ~ l1_orders_2(X0)
% 3.78/1.00      | sK4 != X3
% 3.78/1.00      | sK3 != X4
% 3.78/1.00      | sK1 != X0 ),
% 3.78/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_237,plain,
% 3.78/1.00      ( ~ r2_orders_2(sK1,X0,X1)
% 3.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ r2_hidden(X0,sK4)
% 3.78/1.00      | ~ r2_hidden(X1,sK3)
% 3.78/1.00      | r2_hidden(X0,sK3)
% 3.78/1.00      | v2_struct_0(sK1)
% 3.78/1.00      | ~ v3_orders_2(sK1)
% 3.78/1.00      | ~ v4_orders_2(sK1)
% 3.78/1.00      | ~ v5_orders_2(sK1)
% 3.78/1.00      | ~ l1_orders_2(sK1) ),
% 3.78/1.00      inference(unflattening,[status(thm)],[c_236]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_17,negated_conjecture,
% 3.78/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.78/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_16,negated_conjecture,
% 3.78/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.78/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_239,plain,
% 3.78/1.00      ( r2_hidden(X0,sK3)
% 3.78/1.00      | ~ r2_hidden(X1,sK3)
% 3.78/1.00      | ~ r2_hidden(X0,sK4)
% 3.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ r2_orders_2(sK1,X0,X1) ),
% 3.78/1.00      inference(global_propositional_subsumption,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_237,c_23,c_22,c_21,c_20,c_19,c_17,c_16]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_240,plain,
% 3.78/1.00      ( ~ r2_orders_2(sK1,X0,X1)
% 3.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ r2_hidden(X0,sK4)
% 3.78/1.00      | ~ r2_hidden(X1,sK3)
% 3.78/1.00      | r2_hidden(X0,sK3) ),
% 3.78/1.00      inference(renaming,[status(thm)],[c_239]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_321,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.78/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.78/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X4,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | ~ r2_hidden(X0,k3_orders_2(X1,X5,X2))
% 3.78/1.00      | ~ r2_hidden(X4,sK4)
% 3.78/1.00      | ~ r2_hidden(X3,sK3)
% 3.78/1.00      | r2_hidden(X4,sK3)
% 3.78/1.00      | v2_struct_0(X1)
% 3.78/1.00      | ~ v3_orders_2(X1)
% 3.78/1.00      | ~ v4_orders_2(X1)
% 3.78/1.00      | ~ v5_orders_2(X1)
% 3.78/1.00      | ~ l1_orders_2(X1)
% 3.78/1.00      | X4 != X0
% 3.78/1.00      | X3 != X2
% 3.78/1.00      | sK1 != X1 ),
% 3.78/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_240]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_322,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ r2_hidden(X1,k3_orders_2(sK1,X2,X0))
% 3.78/1.00      | ~ r2_hidden(X1,sK4)
% 3.78/1.00      | ~ r2_hidden(X0,sK3)
% 3.78/1.00      | r2_hidden(X1,sK3)
% 3.78/1.00      | v2_struct_0(sK1)
% 3.78/1.00      | ~ v3_orders_2(sK1)
% 3.78/1.00      | ~ v4_orders_2(sK1)
% 3.78/1.00      | ~ v5_orders_2(sK1)
% 3.78/1.00      | ~ l1_orders_2(sK1) ),
% 3.78/1.00      inference(unflattening,[status(thm)],[c_321]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_324,plain,
% 3.78/1.00      ( r2_hidden(X1,sK3)
% 3.78/1.00      | ~ r2_hidden(X0,sK3)
% 3.78/1.00      | ~ r2_hidden(X1,sK4)
% 3.78/1.00      | ~ r2_hidden(X1,k3_orders_2(sK1,X2,X0))
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 3.78/1.00      inference(global_propositional_subsumption,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_322,c_23,c_22,c_21,c_20,c_19]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_325,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 3.78/1.00      | ~ r2_hidden(X0,sK4)
% 3.78/1.00      | ~ r2_hidden(X1,sK3)
% 3.78/1.00      | r2_hidden(X0,sK3) ),
% 3.78/1.00      inference(renaming,[status(thm)],[c_324]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_842,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(X0,k3_orders_2(sK1,X2,X1)) != iProver_top
% 3.78/1.00      | r2_hidden(X0,sK4) != iProver_top
% 3.78/1.00      | r2_hidden(X1,sK3) != iProver_top
% 3.78/1.00      | r2_hidden(X0,sK3) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_326,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(X0,k3_orders_2(sK1,X2,X1)) != iProver_top
% 3.78/1.00      | r2_hidden(X0,sK4) != iProver_top
% 3.78/1.00      | r2_hidden(X1,sK3) != iProver_top
% 3.78/1.00      | r2_hidden(X0,sK3) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_846,plain,
% 3.78/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1479,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
% 3.78/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_846,c_848]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1616,plain,
% 3.78/1.00      ( m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(X0,k3_orders_2(sK1,X2,X1)) != iProver_top
% 3.78/1.00      | r2_hidden(X0,sK4) != iProver_top
% 3.78/1.00      | r2_hidden(X1,sK3) != iProver_top
% 3.78/1.00      | r2_hidden(X0,sK3) = iProver_top ),
% 3.78/1.00      inference(global_propositional_subsumption,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_842,c_326,c_1479]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1617,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(X2,k3_orders_2(sK1,X1,X0)) != iProver_top
% 3.78/1.00      | r2_hidden(X2,sK4) != iProver_top
% 3.78/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.78/1.00      | r2_hidden(X2,sK3) = iProver_top ),
% 3.78/1.00      inference(renaming,[status(thm)],[c_1616]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_845,plain,
% 3.78/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1480,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
% 3.78/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_845,c_848]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1482,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) | ~ r2_hidden(X0,sK4) ),
% 3.78/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1479]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1490,plain,
% 3.78/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 3.78/1.00      | ~ r2_hidden(X0,sK4)
% 3.78/1.00      | ~ r2_hidden(X1,sK3)
% 3.78/1.00      | r2_hidden(X0,sK3) ),
% 3.78/1.00      inference(global_propositional_subsumption,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_325,c_1482]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1491,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ r2_hidden(X2,k3_orders_2(sK1,X1,X0))
% 3.78/1.00      | ~ r2_hidden(X2,sK4)
% 3.78/1.00      | ~ r2_hidden(X0,sK3)
% 3.78/1.00      | r2_hidden(X2,sK3) ),
% 3.78/1.00      inference(renaming,[status(thm)],[c_1490]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1492,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(X2,k3_orders_2(sK1,X1,X0)) != iProver_top
% 3.78/1.00      | r2_hidden(X2,sK4) != iProver_top
% 3.78/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.78/1.00      | r2_hidden(X2,sK3) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_1491]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1620,plain,
% 3.78/1.00      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(X2,k3_orders_2(sK1,X1,X0)) != iProver_top
% 3.78/1.00      | r2_hidden(X2,sK4) != iProver_top
% 3.78/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.78/1.00      | r2_hidden(X2,sK3) = iProver_top ),
% 3.78/1.00      inference(global_propositional_subsumption,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_1617,c_1480,c_1492]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1621,plain,
% 3.78/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(X1,k3_orders_2(sK1,X0,X2)) != iProver_top
% 3.78/1.00      | r2_hidden(X1,sK4) != iProver_top
% 3.78/1.00      | r2_hidden(X2,sK3) != iProver_top
% 3.78/1.00      | r2_hidden(X1,sK3) = iProver_top ),
% 3.78/1.00      inference(renaming,[status(thm)],[c_1620]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1624,plain,
% 3.78/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(X1,sK3) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X0,X1),X2),sK4) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X0,X1),X2),sK3) = iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,X0,X1),X2) = iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_852,c_1621]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_2935,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,sK4,X0),X1),sK3) = iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,sK4,X0),X1) = iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_2259,c_1624]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_31,plain,
% 3.78/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_2065,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | m1_subset_1(X1,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ r2_hidden(X1,k3_orders_2(sK1,X2,X0)) ),
% 3.78/1.00      inference(resolution,[status(thm)],[c_6,c_417]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_2555,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | r2_hidden(X2,X1)
% 3.78/1.00      | ~ r2_hidden(X2,k3_orders_2(sK1,X1,X0)) ),
% 3.78/1.00      inference(backward_subsumption_resolution,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_2065,c_391]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_2576,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X2),X1)
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,X1,X0),X2) ),
% 3.78/1.00      inference(resolution,[status(thm)],[c_2555,c_1]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1485,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) | ~ r2_hidden(X0,sK3) ),
% 3.78/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1480]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1494,plain,
% 3.78/1.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ r2_hidden(X2,k3_orders_2(sK1,X1,X0))
% 3.78/1.00      | ~ r2_hidden(X2,sK4)
% 3.78/1.00      | ~ r2_hidden(X0,sK3)
% 3.78/1.00      | r2_hidden(X2,sK3) ),
% 3.78/1.00      inference(global_propositional_subsumption,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_1491,c_1485]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1495,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ r2_hidden(X1,k3_orders_2(sK1,X0,X2))
% 3.78/1.00      | ~ r2_hidden(X1,sK4)
% 3.78/1.00      | ~ r2_hidden(X2,sK3)
% 3.78/1.00      | r2_hidden(X1,sK3) ),
% 3.78/1.00      inference(renaming,[status(thm)],[c_1494]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1522,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ r2_hidden(X1,sK3)
% 3.78/1.00      | ~ r2_hidden(sK0(k3_orders_2(sK1,X0,X1),X2),sK4)
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X0,X1),X2),sK3)
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,X0,X1),X2) ),
% 3.78/1.00      inference(resolution,[status(thm)],[c_1495,c_1]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_2752,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ r2_hidden(X0,sK3)
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,sK4,X0),X1),sK3)
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,sK4,X0),X1) ),
% 3.78/1.00      inference(resolution,[status(thm)],[c_2576,c_1522]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_2753,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,sK4,X0),X1),sK3) = iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,sK4,X0),X1) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_2752]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_5295,plain,
% 3.78/1.00      ( r2_hidden(X0,sK3) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,sK4,X0),X1),sK3) = iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,sK4,X0),X1) = iProver_top ),
% 3.78/1.00      inference(global_propositional_subsumption,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_2935,c_31,c_1480,c_2753]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_4,plain,
% 3.78/1.00      ( r1_tarski(X0,X0) ),
% 3.78/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_849,plain,
% 3.78/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_2,plain,
% 3.78/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.78/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_851,plain,
% 3.78/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.78/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.78/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1472,plain,
% 3.78/1.00      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 3.78/1.00      | r1_tarski(X0,X2) != iProver_top
% 3.78/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_852,c_851]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_8,plain,
% 3.78/1.00      ( ~ r2_orders_2(X0,X1,X2)
% 3.78/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.78/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.78/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.78/1.00      | ~ r2_hidden(X1,X3)
% 3.78/1.00      | r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 3.78/1.00      | v2_struct_0(X0)
% 3.78/1.00      | ~ v3_orders_2(X0)
% 3.78/1.00      | ~ v4_orders_2(X0)
% 3.78/1.00      | ~ v5_orders_2(X0)
% 3.78/1.00      | ~ l1_orders_2(X0) ),
% 3.78/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_282,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.78/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.78/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | ~ r2_hidden(X2,X4)
% 3.78/1.00      | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
% 3.78/1.00      | r2_hidden(X2,k3_orders_2(X1,X4,X0))
% 3.78/1.00      | v2_struct_0(X1)
% 3.78/1.00      | ~ v3_orders_2(X1)
% 3.78/1.00      | ~ v4_orders_2(X1)
% 3.78/1.00      | ~ v5_orders_2(X1)
% 3.78/1.00      | ~ l1_orders_2(X1) ),
% 3.78/1.00      inference(resolution,[status(thm)],[c_10,c_8]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_308,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | ~ r2_hidden(X4,X3)
% 3.78/1.00      | ~ r2_hidden(X4,k3_orders_2(X1,X2,X0))
% 3.78/1.00      | r2_hidden(X4,k3_orders_2(X1,X3,X0))
% 3.78/1.00      | v2_struct_0(X1)
% 3.78/1.00      | ~ v3_orders_2(X1)
% 3.78/1.00      | ~ v4_orders_2(X1)
% 3.78/1.00      | ~ v5_orders_2(X1)
% 3.78/1.00      | ~ l1_orders_2(X1) ),
% 3.78/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_282,c_6]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_359,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | ~ r2_hidden(X4,X3)
% 3.78/1.00      | ~ r2_hidden(X4,k3_orders_2(X1,X2,X0))
% 3.78/1.00      | r2_hidden(X4,k3_orders_2(X1,X3,X0))
% 3.78/1.00      | v2_struct_0(X1)
% 3.78/1.00      | ~ v3_orders_2(X1)
% 3.78/1.00      | ~ v4_orders_2(X1)
% 3.78/1.00      | ~ v5_orders_2(X1)
% 3.78/1.00      | sK1 != X1 ),
% 3.78/1.00      inference(resolution_lifted,[status(thm)],[c_308,c_19]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_360,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ r2_hidden(X3,X2)
% 3.78/1.00      | ~ r2_hidden(X3,k3_orders_2(sK1,X1,X0))
% 3.78/1.00      | r2_hidden(X3,k3_orders_2(sK1,X2,X0))
% 3.78/1.00      | v2_struct_0(sK1)
% 3.78/1.00      | ~ v3_orders_2(sK1)
% 3.78/1.00      | ~ v4_orders_2(sK1)
% 3.78/1.00      | ~ v5_orders_2(sK1) ),
% 3.78/1.00      inference(unflattening,[status(thm)],[c_359]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_362,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ r2_hidden(X3,X2)
% 3.78/1.00      | ~ r2_hidden(X3,k3_orders_2(sK1,X1,X0))
% 3.78/1.00      | r2_hidden(X3,k3_orders_2(sK1,X2,X0)) ),
% 3.78/1.00      inference(global_propositional_subsumption,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_360,c_23,c_22,c_21,c_20]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_363,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.78/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | ~ r2_hidden(X3,X1)
% 3.78/1.00      | ~ r2_hidden(X3,k3_orders_2(sK1,X2,X0))
% 3.78/1.00      | r2_hidden(X3,k3_orders_2(sK1,X1,X0)) ),
% 3.78/1.00      inference(renaming,[status(thm)],[c_362]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_841,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(X3,X2) != iProver_top
% 3.78/1.00      | r2_hidden(X3,k3_orders_2(sK1,X1,X0)) != iProver_top
% 3.78/1.00      | r2_hidden(X3,k3_orders_2(sK1,X2,X0)) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1850,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(X3,X4),X2) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(X3,X4),k3_orders_2(sK1,X2,X0)) = iProver_top
% 3.78/1.00      | r1_tarski(X3,X4) = iProver_top
% 3.78/1.00      | r1_tarski(X3,k3_orders_2(sK1,X1,X0)) != iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_1472,c_841]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_3577,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X2,X0),X3),X1) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X2,X0),X3),k3_orders_2(sK1,X1,X0)) = iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,X2,X0),X3) = iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_849,c_1850]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_0,plain,
% 3.78/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_853,plain,
% 3.78/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.78/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_3586,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),k3_orders_2(sK1,X2,X0)),X2) != iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,X1,X0),k3_orders_2(sK1,X2,X0)) = iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_3577,c_853]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_5305,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,sK4,X0),k3_orders_2(sK1,sK3,X0)) = iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_5295,c_3586]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_30,plain,
% 3.78/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_11624,plain,
% 3.78/1.00      ( r2_hidden(X0,sK3) != iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,sK4,X0),k3_orders_2(sK1,sK3,X0)) = iProver_top ),
% 3.78/1.00      inference(global_propositional_subsumption,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_5305,c_30,c_31,c_1480]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_3,plain,
% 3.78/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.78/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_850,plain,
% 3.78/1.00      ( X0 = X1
% 3.78/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.78/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_11630,plain,
% 3.78/1.00      ( k3_orders_2(sK1,sK3,X0) = k3_orders_2(sK1,sK4,X0)
% 3.78/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,sK3,X0),k3_orders_2(sK1,sK4,X0)) != iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_11624,c_850]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_24,plain,
% 3.78/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_25,plain,
% 3.78/1.00      ( v3_orders_2(sK1) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_26,plain,
% 3.78/1.00      ( v4_orders_2(sK1) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_27,plain,
% 3.78/1.00      ( v5_orders_2(sK1) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_28,plain,
% 3.78/1.00      ( l1_orders_2(sK1) = iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_11,plain,
% 3.78/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 3.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | r1_tarski(X0,X2)
% 3.78/1.00      | v2_struct_0(X1)
% 3.78/1.00      | ~ v3_orders_2(X1)
% 3.78/1.00      | ~ v4_orders_2(X1)
% 3.78/1.00      | ~ v5_orders_2(X1)
% 3.78/1.00      | ~ l1_orders_2(X1) ),
% 3.78/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_262,plain,
% 3.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.78/1.00      | r1_tarski(X2,X0)
% 3.78/1.00      | v2_struct_0(X1)
% 3.78/1.00      | ~ v3_orders_2(X1)
% 3.78/1.00      | ~ v4_orders_2(X1)
% 3.78/1.00      | ~ v5_orders_2(X1)
% 3.78/1.00      | ~ l1_orders_2(X1)
% 3.78/1.00      | sK4 != X0
% 3.78/1.00      | sK3 != X2
% 3.78/1.00      | sK1 != X1 ),
% 3.78/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_263,plain,
% 3.78/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.78/1.00      | r1_tarski(sK3,sK4)
% 3.78/1.00      | v2_struct_0(sK1)
% 3.78/1.00      | ~ v3_orders_2(sK1)
% 3.78/1.00      | ~ v4_orders_2(sK1)
% 3.78/1.00      | ~ v5_orders_2(sK1)
% 3.78/1.00      | ~ l1_orders_2(sK1) ),
% 3.78/1.00      inference(unflattening,[status(thm)],[c_262]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_264,plain,
% 3.78/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r1_tarski(sK3,sK4) = iProver_top
% 3.78/1.00      | v2_struct_0(sK1) = iProver_top
% 3.78/1.00      | v3_orders_2(sK1) != iProver_top
% 3.78/1.00      | v4_orders_2(sK1) != iProver_top
% 3.78/1.00      | v5_orders_2(sK1) != iProver_top
% 3.78/1.00      | l1_orders_2(sK1) != iProver_top ),
% 3.78/1.00      inference(predicate_to_equality,[status(thm)],[c_263]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_2265,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X2),X3) = iProver_top
% 3.78/1.00      | r1_tarski(X1,X3) != iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,X1,X0),X2) = iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_2259,c_851]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1360,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X3),X2) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X1,X0),X3),k3_orders_2(sK1,X2,X0)) = iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,X1,X0),X3) = iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_852,c_841]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_2715,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X2,X0),k3_orders_2(sK1,X1,X0)),X1) != iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,X2,X0),k3_orders_2(sK1,X1,X0)) = iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_1360,c_853]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_3099,plain,
% 3.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r1_tarski(X2,X1) != iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,X2,X0),k3_orders_2(sK1,X1,X0)) = iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_2265,c_2715]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_11240,plain,
% 3.78/1.00      ( k3_orders_2(sK1,X0,X1) = k3_orders_2(sK1,X2,X1)
% 3.78/1.00      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r1_tarski(X2,X0) != iProver_top
% 3.78/1.00      | r1_tarski(k3_orders_2(sK1,X0,X1),k3_orders_2(sK1,X2,X1)) != iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_3099,c_850]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_11647,plain,
% 3.78/1.00      ( k3_orders_2(sK1,sK3,X0) = k3_orders_2(sK1,sK4,X0)
% 3.78/1.00      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 3.78/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.78/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.78/1.00      | r1_tarski(sK3,sK4) != iProver_top ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_11624,c_11240]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_11893,plain,
% 3.78/1.00      ( r2_hidden(X0,sK3) != iProver_top
% 3.78/1.00      | k3_orders_2(sK1,sK3,X0) = k3_orders_2(sK1,sK4,X0) ),
% 3.78/1.00      inference(global_propositional_subsumption,
% 3.78/1.00                [status(thm)],
% 3.78/1.00                [c_11630,c_24,c_25,c_26,c_27,c_28,c_30,c_31,c_264,c_1480,
% 3.78/1.00                 c_11647]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_11894,plain,
% 3.78/1.00      ( k3_orders_2(sK1,sK3,X0) = k3_orders_2(sK1,sK4,X0)
% 3.78/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 3.78/1.00      inference(renaming,[status(thm)],[c_11893]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_11900,plain,
% 3.78/1.00      ( k3_orders_2(sK1,sK4,sK2) = k3_orders_2(sK1,sK3,sK2) ),
% 3.78/1.00      inference(superposition,[status(thm)],[c_847,c_11894]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_552,plain,( X0 = X0 ),theory(equality) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1049,plain,
% 3.78/1.00      ( k3_orders_2(sK1,sK3,sK2) = k3_orders_2(sK1,sK3,sK2) ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_552]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_553,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_928,plain,
% 3.78/1.00      ( k3_orders_2(sK1,sK4,sK2) != X0
% 3.78/1.00      | k3_orders_2(sK1,sK3,sK2) != X0
% 3.78/1.00      | k3_orders_2(sK1,sK3,sK2) = k3_orders_2(sK1,sK4,sK2) ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_553]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_1048,plain,
% 3.78/1.00      ( k3_orders_2(sK1,sK4,sK2) != k3_orders_2(sK1,sK3,sK2)
% 3.78/1.00      | k3_orders_2(sK1,sK3,sK2) = k3_orders_2(sK1,sK4,sK2)
% 3.78/1.00      | k3_orders_2(sK1,sK3,sK2) != k3_orders_2(sK1,sK3,sK2) ),
% 3.78/1.00      inference(instantiation,[status(thm)],[c_928]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(c_13,negated_conjecture,
% 3.78/1.00      ( k3_orders_2(sK1,sK3,sK2) != k3_orders_2(sK1,sK4,sK2) ),
% 3.78/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.78/1.00  
% 3.78/1.00  cnf(contradiction,plain,
% 3.78/1.00      ( $false ),
% 3.78/1.00      inference(minisat,[status(thm)],[c_11900,c_1049,c_1048,c_13]) ).
% 3.78/1.00  
% 3.78/1.00  
% 3.78/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/1.00  
% 3.78/1.00  ------                               Statistics
% 3.78/1.00  
% 3.78/1.00  ------ Selected
% 3.78/1.00  
% 3.78/1.00  total_time:                             0.444
% 3.78/1.00  
%------------------------------------------------------------------------------
