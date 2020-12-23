%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:42 EST 2020

% Result     : Theorem 22.61s
% Output     : CNFRefutation 22.61s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 856 expanded)
%              Number of clauses        :   74 ( 157 expanded)
%              Number of leaves         :   14 ( 319 expanded)
%              Depth                    :   18
%              Number of atoms          :  827 (8049 expanded)
%              Number of equality atoms :   37 ( 799 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   22 (   6 average)
%              Maximal term depth       :    3 (   1 average)

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
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f43,f42,f41,f40])).

fof(f70,plain,(
    m1_orders_2(sK4,sK2,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f35,plain,(
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

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    k3_orders_2(sK2,sK4,sK3) != k3_orders_2(sK2,sK5,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f56])).

cnf(c_15,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ m1_orders_2(X3,X0,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X3)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_17,negated_conjecture,
    ( m1_orders_2(sK4,sK2,sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_360,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X3)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK5 != X4
    | sK4 != X3
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_361,plain,
    ( ~ r2_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X1,sK4)
    | r2_hidden(X0,sK4)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_363,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(X1,sK4)
    | ~ r2_hidden(X0,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_orders_2(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_361,c_26,c_25,c_24,c_23,c_22,c_20,c_19])).

cnf(c_364,plain,
    ( ~ r2_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X1,sK4)
    | r2_hidden(X0,sK4) ),
    inference(renaming,[status(thm)],[c_363])).

cnf(c_531,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(X4,u1_struct_0(sK2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,k3_orders_2(X1,X5,X2))
    | ~ r2_hidden(X4,sK5)
    | ~ r2_hidden(X3,sK4)
    | r2_hidden(X4,sK4)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X4 != X0
    | X3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_364])).

cnf(c_532,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k3_orders_2(sK2,X2,X0))
    | ~ r2_hidden(X1,sK5)
    | ~ r2_hidden(X0,sK4)
    | r2_hidden(X1,sK4)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_534,plain,
    ( r2_hidden(X1,sK4)
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X1,sK5)
    | ~ r2_hidden(X1,k3_orders_2(sK2,X2,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_532,c_26,c_25,c_24,c_23,c_22])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,k3_orders_2(sK2,X2,X1))
    | ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X1,sK4)
    | r2_hidden(X0,sK4) ),
    inference(renaming,[status(thm)],[c_534])).

cnf(c_10194,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,X1,X0))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK5)
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4) ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_74868,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,X0,sK3))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK5)
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4)
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_10194])).

cnf(c_83558,plain,
    ( ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK5)
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4)
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_74868])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f58])).

cnf(c_492,plain,
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
    inference(resolution,[status(thm)],[c_13,c_11])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_518,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_492,c_8])).

cnf(c_569,plain,
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
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_518,c_22])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,k3_orders_2(sK2,X1,X0))
    | r2_hidden(X3,k3_orders_2(sK2,X2,X0))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_572,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,k3_orders_2(sK2,X1,X0))
    | r2_hidden(X3,k3_orders_2(sK2,X2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_570,c_26,c_25,c_24,c_23])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X3,k3_orders_2(sK2,X2,X0))
    | r2_hidden(X3,k3_orders_2(sK2,X1,X0)) ),
    inference(renaming,[status(thm)],[c_572])).

cnf(c_1516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k3_orders_2(sK2,X0,sK3))
    | r2_hidden(X2,k3_orders_2(sK2,X1,sK3)) ),
    inference(instantiation,[status(thm)],[c_573])).

cnf(c_1729,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k3_orders_2(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X1,k3_orders_2(sK2,X0,sK3))
    | ~ r2_hidden(X1,k3_orders_2(sK2,k3_orders_2(sK2,sK4,sK3),sK3)) ),
    inference(instantiation,[status(thm)],[c_1516])).

cnf(c_9195,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k3_orders_2(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),X0)
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,X0,sK3))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,k3_orders_2(sK2,sK4,sK3),sK3)) ),
    inference(instantiation,[status(thm)],[c_1729])).

cnf(c_24506,plain,
    ( ~ m1_subset_1(k3_orders_2(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,k3_orders_2(sK2,sK4,sK3),sK3))
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK5) ),
    inference(instantiation,[status(thm)],[c_9195])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2111,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,sK5)
    | ~ r1_tarski(X1,sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5071,plain,
    ( r2_hidden(X0,sK5)
    | ~ r2_hidden(X0,sK4)
    | ~ r1_tarski(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2111])).

cnf(c_10204,plain,
    ( r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK5)
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4)
    | ~ r1_tarski(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_5071])).

cnf(c_1714,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X1,k3_orders_2(sK2,X0,sK3))
    | ~ r2_hidden(X1,k3_orders_2(sK2,sK5,sK3)) ),
    inference(instantiation,[status(thm)],[c_1516])).

cnf(c_1914,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,k3_orders_2(sK2,sK5,sK3))
    | r2_hidden(X0,k3_orders_2(sK2,sK4,sK3))
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_1714])).

cnf(c_10205,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4) ),
    inference(instantiation,[status(thm)],[c_1914])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f57])).

cnf(c_595,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_596,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_orders_2(sK2,X2,X1))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_600,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_orders_2(sK2,X2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_596,c_26,c_25,c_24,c_23])).

cnf(c_601,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(sK2,X2,X0)) ),
    inference(renaming,[status(thm)],[c_600])).

cnf(c_1511,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK2,X1,sK3)) ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_3101,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),X0)
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_10203,plain,
    ( ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3))
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4) ),
    inference(instantiation,[status(thm)],[c_3101])).

cnf(c_10192,plain,
    ( ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK5) ),
    inference(instantiation,[status(thm)],[c_3101])).

cnf(c_1747,plain,
    ( ~ m1_subset_1(k3_orders_2(sK2,sK4,sK3),k1_zfmisc_1(X0))
    | m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),X0)
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3571,plain,
    ( ~ m1_subset_1(k3_orders_2(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_1747])).

cnf(c_1719,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X1,k3_orders_2(sK2,X0,sK3))
    | ~ r2_hidden(X1,k3_orders_2(sK2,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_1516])).

cnf(c_1941,plain,
    ( ~ m1_subset_1(k3_orders_2(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,k3_orders_2(sK2,k3_orders_2(sK2,sK4,sK3),sK3))
    | ~ r2_hidden(X0,k3_orders_2(sK2,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_1719])).

cnf(c_3282,plain,
    ( ~ m1_subset_1(k3_orders_2(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,k3_orders_2(sK2,sK4,sK3),sK3))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_1941])).

cnf(c_1587,plain,
    ( ~ m1_subset_1(k3_orders_2(sK2,sK5,sK3),k1_zfmisc_1(X0))
    | m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),X0)
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2163,plain,
    ( ~ m1_subset_1(k3_orders_2(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3)) ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_622,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_623,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k3_orders_2(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k3_orders_2(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_623,c_26,c_25,c_24,c_23])).

cnf(c_1506,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k3_orders_2(sK2,X0,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_627])).

cnf(c_1608,plain,
    ( m1_subset_1(k3_orders_2(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_1605,plain,
    ( m1_subset_1(k3_orders_2(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1544,plain,
    ( r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
    | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3))
    | k3_orders_2(sK2,sK4,sK3) = k3_orders_2(sK2,sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1541,plain,
    ( ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
    | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3))
    | k3_orders_2(sK2,sK4,sK3) = k3_orders_2(sK2,sK5,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_14,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK5 != X0
    | sK4 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_348,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK4,sK5)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_16,negated_conjecture,
    ( k3_orders_2(sK2,sK4,sK3) != k3_orders_2(sK2,sK5,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_83558,c_24506,c_10204,c_10205,c_10203,c_10192,c_3571,c_3282,c_2163,c_1608,c_1605,c_1544,c_1541,c_348,c_16,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:07:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 22.61/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.61/3.49  
% 22.61/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 22.61/3.49  
% 22.61/3.49  ------  iProver source info
% 22.61/3.49  
% 22.61/3.49  git: date: 2020-06-30 10:37:57 +0100
% 22.61/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 22.61/3.49  git: non_committed_changes: false
% 22.61/3.49  git: last_make_outside_of_git: false
% 22.61/3.49  
% 22.61/3.49  ------ 
% 22.61/3.49  
% 22.61/3.49  ------ Input Options
% 22.61/3.49  
% 22.61/3.49  --out_options                           all
% 22.61/3.49  --tptp_safe_out                         true
% 22.61/3.49  --problem_path                          ""
% 22.61/3.49  --include_path                          ""
% 22.61/3.49  --clausifier                            res/vclausify_rel
% 22.61/3.49  --clausifier_options                    --mode clausify
% 22.61/3.49  --stdin                                 false
% 22.61/3.49  --stats_out                             all
% 22.61/3.49  
% 22.61/3.49  ------ General Options
% 22.61/3.49  
% 22.61/3.49  --fof                                   false
% 22.61/3.49  --time_out_real                         305.
% 22.61/3.49  --time_out_virtual                      -1.
% 22.61/3.49  --symbol_type_check                     false
% 22.61/3.49  --clausify_out                          false
% 22.61/3.49  --sig_cnt_out                           false
% 22.61/3.49  --trig_cnt_out                          false
% 22.61/3.49  --trig_cnt_out_tolerance                1.
% 22.61/3.49  --trig_cnt_out_sk_spl                   false
% 22.61/3.49  --abstr_cl_out                          false
% 22.61/3.49  
% 22.61/3.49  ------ Global Options
% 22.61/3.49  
% 22.61/3.49  --schedule                              default
% 22.61/3.49  --add_important_lit                     false
% 22.61/3.49  --prop_solver_per_cl                    1000
% 22.61/3.49  --min_unsat_core                        false
% 22.61/3.49  --soft_assumptions                      false
% 22.61/3.49  --soft_lemma_size                       3
% 22.61/3.49  --prop_impl_unit_size                   0
% 22.61/3.49  --prop_impl_unit                        []
% 22.61/3.49  --share_sel_clauses                     true
% 22.61/3.49  --reset_solvers                         false
% 22.61/3.49  --bc_imp_inh                            [conj_cone]
% 22.61/3.49  --conj_cone_tolerance                   3.
% 22.61/3.49  --extra_neg_conj                        none
% 22.61/3.49  --large_theory_mode                     true
% 22.61/3.49  --prolific_symb_bound                   200
% 22.61/3.49  --lt_threshold                          2000
% 22.61/3.49  --clause_weak_htbl                      true
% 22.61/3.49  --gc_record_bc_elim                     false
% 22.61/3.49  
% 22.61/3.49  ------ Preprocessing Options
% 22.61/3.49  
% 22.61/3.49  --preprocessing_flag                    true
% 22.61/3.49  --time_out_prep_mult                    0.1
% 22.61/3.49  --splitting_mode                        input
% 22.61/3.49  --splitting_grd                         true
% 22.61/3.49  --splitting_cvd                         false
% 22.61/3.49  --splitting_cvd_svl                     false
% 22.61/3.49  --splitting_nvd                         32
% 22.61/3.49  --sub_typing                            true
% 22.61/3.49  --prep_gs_sim                           true
% 22.61/3.49  --prep_unflatten                        true
% 22.61/3.49  --prep_res_sim                          true
% 22.61/3.49  --prep_upred                            true
% 22.61/3.49  --prep_sem_filter                       exhaustive
% 22.61/3.49  --prep_sem_filter_out                   false
% 22.61/3.49  --pred_elim                             true
% 22.61/3.49  --res_sim_input                         true
% 22.61/3.49  --eq_ax_congr_red                       true
% 22.61/3.49  --pure_diseq_elim                       true
% 22.61/3.49  --brand_transform                       false
% 22.61/3.49  --non_eq_to_eq                          false
% 22.61/3.49  --prep_def_merge                        true
% 22.61/3.49  --prep_def_merge_prop_impl              false
% 22.61/3.49  --prep_def_merge_mbd                    true
% 22.61/3.49  --prep_def_merge_tr_red                 false
% 22.61/3.49  --prep_def_merge_tr_cl                  false
% 22.61/3.49  --smt_preprocessing                     true
% 22.61/3.49  --smt_ac_axioms                         fast
% 22.61/3.49  --preprocessed_out                      false
% 22.61/3.49  --preprocessed_stats                    false
% 22.61/3.49  
% 22.61/3.49  ------ Abstraction refinement Options
% 22.61/3.49  
% 22.61/3.49  --abstr_ref                             []
% 22.61/3.49  --abstr_ref_prep                        false
% 22.61/3.49  --abstr_ref_until_sat                   false
% 22.61/3.49  --abstr_ref_sig_restrict                funpre
% 22.61/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 22.61/3.49  --abstr_ref_under                       []
% 22.61/3.49  
% 22.61/3.49  ------ SAT Options
% 22.61/3.49  
% 22.61/3.49  --sat_mode                              false
% 22.61/3.49  --sat_fm_restart_options                ""
% 22.61/3.49  --sat_gr_def                            false
% 22.61/3.49  --sat_epr_types                         true
% 22.61/3.49  --sat_non_cyclic_types                  false
% 22.61/3.49  --sat_finite_models                     false
% 22.61/3.49  --sat_fm_lemmas                         false
% 22.61/3.49  --sat_fm_prep                           false
% 22.61/3.49  --sat_fm_uc_incr                        true
% 22.61/3.49  --sat_out_model                         small
% 22.61/3.49  --sat_out_clauses                       false
% 22.61/3.49  
% 22.61/3.49  ------ QBF Options
% 22.61/3.49  
% 22.61/3.49  --qbf_mode                              false
% 22.61/3.49  --qbf_elim_univ                         false
% 22.61/3.49  --qbf_dom_inst                          none
% 22.61/3.49  --qbf_dom_pre_inst                      false
% 22.61/3.49  --qbf_sk_in                             false
% 22.61/3.49  --qbf_pred_elim                         true
% 22.61/3.49  --qbf_split                             512
% 22.61/3.49  
% 22.61/3.49  ------ BMC1 Options
% 22.61/3.49  
% 22.61/3.49  --bmc1_incremental                      false
% 22.61/3.49  --bmc1_axioms                           reachable_all
% 22.61/3.49  --bmc1_min_bound                        0
% 22.61/3.49  --bmc1_max_bound                        -1
% 22.61/3.49  --bmc1_max_bound_default                -1
% 22.61/3.49  --bmc1_symbol_reachability              true
% 22.61/3.49  --bmc1_property_lemmas                  false
% 22.61/3.49  --bmc1_k_induction                      false
% 22.61/3.49  --bmc1_non_equiv_states                 false
% 22.61/3.49  --bmc1_deadlock                         false
% 22.61/3.49  --bmc1_ucm                              false
% 22.61/3.49  --bmc1_add_unsat_core                   none
% 22.61/3.49  --bmc1_unsat_core_children              false
% 22.61/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 22.61/3.49  --bmc1_out_stat                         full
% 22.61/3.49  --bmc1_ground_init                      false
% 22.61/3.49  --bmc1_pre_inst_next_state              false
% 22.61/3.49  --bmc1_pre_inst_state                   false
% 22.61/3.49  --bmc1_pre_inst_reach_state             false
% 22.61/3.49  --bmc1_out_unsat_core                   false
% 22.61/3.49  --bmc1_aig_witness_out                  false
% 22.61/3.49  --bmc1_verbose                          false
% 22.61/3.49  --bmc1_dump_clauses_tptp                false
% 22.61/3.49  --bmc1_dump_unsat_core_tptp             false
% 22.61/3.49  --bmc1_dump_file                        -
% 22.61/3.49  --bmc1_ucm_expand_uc_limit              128
% 22.61/3.49  --bmc1_ucm_n_expand_iterations          6
% 22.61/3.49  --bmc1_ucm_extend_mode                  1
% 22.61/3.49  --bmc1_ucm_init_mode                    2
% 22.61/3.49  --bmc1_ucm_cone_mode                    none
% 22.61/3.49  --bmc1_ucm_reduced_relation_type        0
% 22.61/3.49  --bmc1_ucm_relax_model                  4
% 22.61/3.49  --bmc1_ucm_full_tr_after_sat            true
% 22.61/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 22.61/3.49  --bmc1_ucm_layered_model                none
% 22.61/3.49  --bmc1_ucm_max_lemma_size               10
% 22.61/3.49  
% 22.61/3.49  ------ AIG Options
% 22.61/3.49  
% 22.61/3.49  --aig_mode                              false
% 22.61/3.49  
% 22.61/3.49  ------ Instantiation Options
% 22.61/3.49  
% 22.61/3.49  --instantiation_flag                    true
% 22.61/3.49  --inst_sos_flag                         false
% 22.61/3.49  --inst_sos_phase                        true
% 22.61/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 22.61/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 22.61/3.49  --inst_lit_sel_side                     num_symb
% 22.61/3.49  --inst_solver_per_active                1400
% 22.61/3.49  --inst_solver_calls_frac                1.
% 22.61/3.49  --inst_passive_queue_type               priority_queues
% 22.61/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 22.61/3.49  --inst_passive_queues_freq              [25;2]
% 22.61/3.49  --inst_dismatching                      true
% 22.61/3.49  --inst_eager_unprocessed_to_passive     true
% 22.61/3.49  --inst_prop_sim_given                   true
% 22.61/3.49  --inst_prop_sim_new                     false
% 22.61/3.49  --inst_subs_new                         false
% 22.61/3.49  --inst_eq_res_simp                      false
% 22.61/3.49  --inst_subs_given                       false
% 22.61/3.49  --inst_orphan_elimination               true
% 22.61/3.49  --inst_learning_loop_flag               true
% 22.61/3.49  --inst_learning_start                   3000
% 22.61/3.49  --inst_learning_factor                  2
% 22.61/3.49  --inst_start_prop_sim_after_learn       3
% 22.61/3.49  --inst_sel_renew                        solver
% 22.61/3.49  --inst_lit_activity_flag                true
% 22.61/3.49  --inst_restr_to_given                   false
% 22.61/3.49  --inst_activity_threshold               500
% 22.61/3.49  --inst_out_proof                        true
% 22.61/3.49  
% 22.61/3.49  ------ Resolution Options
% 22.61/3.49  
% 22.61/3.49  --resolution_flag                       true
% 22.61/3.49  --res_lit_sel                           adaptive
% 22.61/3.49  --res_lit_sel_side                      none
% 22.61/3.49  --res_ordering                          kbo
% 22.61/3.49  --res_to_prop_solver                    active
% 22.61/3.49  --res_prop_simpl_new                    false
% 22.61/3.49  --res_prop_simpl_given                  true
% 22.61/3.49  --res_passive_queue_type                priority_queues
% 22.61/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 22.61/3.49  --res_passive_queues_freq               [15;5]
% 22.61/3.49  --res_forward_subs                      full
% 22.61/3.49  --res_backward_subs                     full
% 22.61/3.49  --res_forward_subs_resolution           true
% 22.61/3.49  --res_backward_subs_resolution          true
% 22.61/3.49  --res_orphan_elimination                true
% 22.61/3.49  --res_time_limit                        2.
% 22.61/3.49  --res_out_proof                         true
% 22.61/3.49  
% 22.61/3.49  ------ Superposition Options
% 22.61/3.49  
% 22.61/3.49  --superposition_flag                    true
% 22.61/3.49  --sup_passive_queue_type                priority_queues
% 22.61/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 22.61/3.49  --sup_passive_queues_freq               [8;1;4]
% 22.61/3.49  --demod_completeness_check              fast
% 22.61/3.49  --demod_use_ground                      true
% 22.61/3.49  --sup_to_prop_solver                    passive
% 22.61/3.49  --sup_prop_simpl_new                    true
% 22.61/3.49  --sup_prop_simpl_given                  true
% 22.61/3.49  --sup_fun_splitting                     false
% 22.61/3.49  --sup_smt_interval                      50000
% 22.61/3.49  
% 22.61/3.49  ------ Superposition Simplification Setup
% 22.61/3.49  
% 22.61/3.49  --sup_indices_passive                   []
% 22.61/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 22.61/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 22.61/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 22.61/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 22.61/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 22.61/3.49  --sup_full_bw                           [BwDemod]
% 22.61/3.49  --sup_immed_triv                        [TrivRules]
% 22.61/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 22.61/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 22.61/3.49  --sup_immed_bw_main                     []
% 22.61/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 22.61/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 22.61/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 22.61/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 22.61/3.49  
% 22.61/3.49  ------ Combination Options
% 22.61/3.49  
% 22.61/3.49  --comb_res_mult                         3
% 22.61/3.49  --comb_sup_mult                         2
% 22.61/3.49  --comb_inst_mult                        10
% 22.61/3.49  
% 22.61/3.49  ------ Debug Options
% 22.61/3.49  
% 22.61/3.49  --dbg_backtrace                         false
% 22.61/3.49  --dbg_dump_prop_clauses                 false
% 22.61/3.49  --dbg_dump_prop_clauses_file            -
% 22.61/3.49  --dbg_out_stat                          false
% 22.61/3.49  ------ Parsing...
% 22.61/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 22.61/3.49  
% 22.61/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 22.61/3.49  
% 22.61/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 22.61/3.49  
% 22.61/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 22.61/3.49  ------ Proving...
% 22.61/3.49  ------ Problem Properties 
% 22.61/3.49  
% 22.61/3.49  
% 22.61/3.49  clauses                                 19
% 22.61/3.49  conjectures                             5
% 22.61/3.49  EPR                                     4
% 22.61/3.49  Horn                                    17
% 22.61/3.49  unary                                   6
% 22.61/3.49  binary                                  5
% 22.61/3.49  lits                                    49
% 22.61/3.49  lits eq                                 3
% 22.61/3.49  fd_pure                                 0
% 22.61/3.49  fd_pseudo                               0
% 22.61/3.49  fd_cond                                 0
% 22.61/3.49  fd_pseudo_cond                          2
% 22.61/3.49  AC symbols                              0
% 22.61/3.49  
% 22.61/3.49  ------ Schedule dynamic 5 is on 
% 22.61/3.49  
% 22.61/3.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 22.61/3.49  
% 22.61/3.49  
% 22.61/3.49  ------ 
% 22.61/3.49  Current options:
% 22.61/3.49  ------ 
% 22.61/3.49  
% 22.61/3.49  ------ Input Options
% 22.61/3.49  
% 22.61/3.49  --out_options                           all
% 22.61/3.49  --tptp_safe_out                         true
% 22.61/3.49  --problem_path                          ""
% 22.61/3.49  --include_path                          ""
% 22.61/3.49  --clausifier                            res/vclausify_rel
% 22.61/3.49  --clausifier_options                    --mode clausify
% 22.61/3.49  --stdin                                 false
% 22.61/3.49  --stats_out                             all
% 22.61/3.49  
% 22.61/3.49  ------ General Options
% 22.61/3.49  
% 22.61/3.49  --fof                                   false
% 22.61/3.49  --time_out_real                         305.
% 22.61/3.49  --time_out_virtual                      -1.
% 22.61/3.49  --symbol_type_check                     false
% 22.61/3.49  --clausify_out                          false
% 22.61/3.49  --sig_cnt_out                           false
% 22.61/3.49  --trig_cnt_out                          false
% 22.61/3.49  --trig_cnt_out_tolerance                1.
% 22.61/3.49  --trig_cnt_out_sk_spl                   false
% 22.61/3.49  --abstr_cl_out                          false
% 22.61/3.49  
% 22.61/3.49  ------ Global Options
% 22.61/3.49  
% 22.61/3.49  --schedule                              default
% 22.61/3.49  --add_important_lit                     false
% 22.61/3.49  --prop_solver_per_cl                    1000
% 22.61/3.49  --min_unsat_core                        false
% 22.61/3.49  --soft_assumptions                      false
% 22.61/3.49  --soft_lemma_size                       3
% 22.61/3.49  --prop_impl_unit_size                   0
% 22.61/3.49  --prop_impl_unit                        []
% 22.61/3.49  --share_sel_clauses                     true
% 22.61/3.49  --reset_solvers                         false
% 22.61/3.49  --bc_imp_inh                            [conj_cone]
% 22.61/3.49  --conj_cone_tolerance                   3.
% 22.61/3.49  --extra_neg_conj                        none
% 22.61/3.49  --large_theory_mode                     true
% 22.61/3.49  --prolific_symb_bound                   200
% 22.61/3.49  --lt_threshold                          2000
% 22.61/3.49  --clause_weak_htbl                      true
% 22.61/3.49  --gc_record_bc_elim                     false
% 22.61/3.49  
% 22.61/3.49  ------ Preprocessing Options
% 22.61/3.49  
% 22.61/3.49  --preprocessing_flag                    true
% 22.61/3.49  --time_out_prep_mult                    0.1
% 22.61/3.49  --splitting_mode                        input
% 22.61/3.49  --splitting_grd                         true
% 22.61/3.49  --splitting_cvd                         false
% 22.61/3.49  --splitting_cvd_svl                     false
% 22.61/3.49  --splitting_nvd                         32
% 22.61/3.49  --sub_typing                            true
% 22.61/3.49  --prep_gs_sim                           true
% 22.61/3.49  --prep_unflatten                        true
% 22.61/3.49  --prep_res_sim                          true
% 22.61/3.49  --prep_upred                            true
% 22.61/3.49  --prep_sem_filter                       exhaustive
% 22.61/3.49  --prep_sem_filter_out                   false
% 22.61/3.49  --pred_elim                             true
% 22.61/3.49  --res_sim_input                         true
% 22.61/3.49  --eq_ax_congr_red                       true
% 22.61/3.49  --pure_diseq_elim                       true
% 22.61/3.49  --brand_transform                       false
% 22.61/3.49  --non_eq_to_eq                          false
% 22.61/3.49  --prep_def_merge                        true
% 22.61/3.49  --prep_def_merge_prop_impl              false
% 22.61/3.49  --prep_def_merge_mbd                    true
% 22.61/3.49  --prep_def_merge_tr_red                 false
% 22.61/3.49  --prep_def_merge_tr_cl                  false
% 22.61/3.49  --smt_preprocessing                     true
% 22.61/3.49  --smt_ac_axioms                         fast
% 22.61/3.49  --preprocessed_out                      false
% 22.61/3.49  --preprocessed_stats                    false
% 22.61/3.49  
% 22.61/3.49  ------ Abstraction refinement Options
% 22.61/3.49  
% 22.61/3.49  --abstr_ref                             []
% 22.61/3.49  --abstr_ref_prep                        false
% 22.61/3.49  --abstr_ref_until_sat                   false
% 22.61/3.49  --abstr_ref_sig_restrict                funpre
% 22.61/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 22.61/3.49  --abstr_ref_under                       []
% 22.61/3.49  
% 22.61/3.49  ------ SAT Options
% 22.61/3.49  
% 22.61/3.49  --sat_mode                              false
% 22.61/3.49  --sat_fm_restart_options                ""
% 22.61/3.49  --sat_gr_def                            false
% 22.61/3.49  --sat_epr_types                         true
% 22.61/3.49  --sat_non_cyclic_types                  false
% 22.61/3.49  --sat_finite_models                     false
% 22.61/3.49  --sat_fm_lemmas                         false
% 22.61/3.49  --sat_fm_prep                           false
% 22.61/3.49  --sat_fm_uc_incr                        true
% 22.61/3.49  --sat_out_model                         small
% 22.61/3.49  --sat_out_clauses                       false
% 22.61/3.49  
% 22.61/3.49  ------ QBF Options
% 22.61/3.49  
% 22.61/3.49  --qbf_mode                              false
% 22.61/3.49  --qbf_elim_univ                         false
% 22.61/3.49  --qbf_dom_inst                          none
% 22.61/3.49  --qbf_dom_pre_inst                      false
% 22.61/3.49  --qbf_sk_in                             false
% 22.61/3.49  --qbf_pred_elim                         true
% 22.61/3.49  --qbf_split                             512
% 22.61/3.49  
% 22.61/3.49  ------ BMC1 Options
% 22.61/3.49  
% 22.61/3.49  --bmc1_incremental                      false
% 22.61/3.49  --bmc1_axioms                           reachable_all
% 22.61/3.49  --bmc1_min_bound                        0
% 22.61/3.49  --bmc1_max_bound                        -1
% 22.61/3.49  --bmc1_max_bound_default                -1
% 22.61/3.49  --bmc1_symbol_reachability              true
% 22.61/3.49  --bmc1_property_lemmas                  false
% 22.61/3.49  --bmc1_k_induction                      false
% 22.61/3.49  --bmc1_non_equiv_states                 false
% 22.61/3.49  --bmc1_deadlock                         false
% 22.61/3.49  --bmc1_ucm                              false
% 22.61/3.49  --bmc1_add_unsat_core                   none
% 22.61/3.49  --bmc1_unsat_core_children              false
% 22.61/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 22.61/3.49  --bmc1_out_stat                         full
% 22.61/3.49  --bmc1_ground_init                      false
% 22.61/3.49  --bmc1_pre_inst_next_state              false
% 22.61/3.49  --bmc1_pre_inst_state                   false
% 22.61/3.49  --bmc1_pre_inst_reach_state             false
% 22.61/3.49  --bmc1_out_unsat_core                   false
% 22.61/3.49  --bmc1_aig_witness_out                  false
% 22.61/3.49  --bmc1_verbose                          false
% 22.61/3.49  --bmc1_dump_clauses_tptp                false
% 22.61/3.49  --bmc1_dump_unsat_core_tptp             false
% 22.61/3.49  --bmc1_dump_file                        -
% 22.61/3.49  --bmc1_ucm_expand_uc_limit              128
% 22.61/3.49  --bmc1_ucm_n_expand_iterations          6
% 22.61/3.49  --bmc1_ucm_extend_mode                  1
% 22.61/3.49  --bmc1_ucm_init_mode                    2
% 22.61/3.49  --bmc1_ucm_cone_mode                    none
% 22.61/3.49  --bmc1_ucm_reduced_relation_type        0
% 22.61/3.49  --bmc1_ucm_relax_model                  4
% 22.61/3.49  --bmc1_ucm_full_tr_after_sat            true
% 22.61/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 22.61/3.49  --bmc1_ucm_layered_model                none
% 22.61/3.49  --bmc1_ucm_max_lemma_size               10
% 22.61/3.49  
% 22.61/3.49  ------ AIG Options
% 22.61/3.49  
% 22.61/3.49  --aig_mode                              false
% 22.61/3.49  
% 22.61/3.49  ------ Instantiation Options
% 22.61/3.49  
% 22.61/3.49  --instantiation_flag                    true
% 22.61/3.49  --inst_sos_flag                         false
% 22.61/3.49  --inst_sos_phase                        true
% 22.61/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 22.61/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 22.61/3.49  --inst_lit_sel_side                     none
% 22.61/3.49  --inst_solver_per_active                1400
% 22.61/3.49  --inst_solver_calls_frac                1.
% 22.61/3.49  --inst_passive_queue_type               priority_queues
% 22.61/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 22.61/3.49  --inst_passive_queues_freq              [25;2]
% 22.61/3.49  --inst_dismatching                      true
% 22.61/3.49  --inst_eager_unprocessed_to_passive     true
% 22.61/3.49  --inst_prop_sim_given                   true
% 22.61/3.49  --inst_prop_sim_new                     false
% 22.61/3.49  --inst_subs_new                         false
% 22.61/3.49  --inst_eq_res_simp                      false
% 22.61/3.49  --inst_subs_given                       false
% 22.61/3.49  --inst_orphan_elimination               true
% 22.61/3.49  --inst_learning_loop_flag               true
% 22.61/3.49  --inst_learning_start                   3000
% 22.61/3.49  --inst_learning_factor                  2
% 22.61/3.49  --inst_start_prop_sim_after_learn       3
% 22.61/3.49  --inst_sel_renew                        solver
% 22.61/3.49  --inst_lit_activity_flag                true
% 22.61/3.49  --inst_restr_to_given                   false
% 22.61/3.49  --inst_activity_threshold               500
% 22.61/3.49  --inst_out_proof                        true
% 22.61/3.49  
% 22.61/3.49  ------ Resolution Options
% 22.61/3.49  
% 22.61/3.49  --resolution_flag                       false
% 22.61/3.49  --res_lit_sel                           adaptive
% 22.61/3.49  --res_lit_sel_side                      none
% 22.61/3.49  --res_ordering                          kbo
% 22.61/3.49  --res_to_prop_solver                    active
% 22.61/3.49  --res_prop_simpl_new                    false
% 22.61/3.49  --res_prop_simpl_given                  true
% 22.61/3.49  --res_passive_queue_type                priority_queues
% 22.61/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 22.61/3.49  --res_passive_queues_freq               [15;5]
% 22.61/3.49  --res_forward_subs                      full
% 22.61/3.49  --res_backward_subs                     full
% 22.61/3.49  --res_forward_subs_resolution           true
% 22.61/3.49  --res_backward_subs_resolution          true
% 22.61/3.49  --res_orphan_elimination                true
% 22.61/3.49  --res_time_limit                        2.
% 22.61/3.49  --res_out_proof                         true
% 22.61/3.49  
% 22.61/3.49  ------ Superposition Options
% 22.61/3.49  
% 22.61/3.49  --superposition_flag                    true
% 22.61/3.49  --sup_passive_queue_type                priority_queues
% 22.61/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 22.61/3.49  --sup_passive_queues_freq               [8;1;4]
% 22.61/3.49  --demod_completeness_check              fast
% 22.61/3.49  --demod_use_ground                      true
% 22.61/3.49  --sup_to_prop_solver                    passive
% 22.61/3.49  --sup_prop_simpl_new                    true
% 22.61/3.49  --sup_prop_simpl_given                  true
% 22.61/3.49  --sup_fun_splitting                     false
% 22.61/3.49  --sup_smt_interval                      50000
% 22.61/3.49  
% 22.61/3.49  ------ Superposition Simplification Setup
% 22.61/3.49  
% 22.61/3.49  --sup_indices_passive                   []
% 22.61/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 22.61/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 22.61/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 22.61/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 22.61/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 22.61/3.49  --sup_full_bw                           [BwDemod]
% 22.61/3.49  --sup_immed_triv                        [TrivRules]
% 22.61/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 22.61/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 22.61/3.49  --sup_immed_bw_main                     []
% 22.61/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 22.61/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 22.61/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 22.61/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 22.61/3.49  
% 22.61/3.49  ------ Combination Options
% 22.61/3.49  
% 22.61/3.49  --comb_res_mult                         3
% 22.61/3.49  --comb_sup_mult                         2
% 22.61/3.49  --comb_inst_mult                        10
% 22.61/3.49  
% 22.61/3.49  ------ Debug Options
% 22.61/3.49  
% 22.61/3.49  --dbg_backtrace                         false
% 22.61/3.49  --dbg_dump_prop_clauses                 false
% 22.61/3.49  --dbg_dump_prop_clauses_file            -
% 22.61/3.49  --dbg_out_stat                          false
% 22.61/3.49  
% 22.61/3.49  
% 22.61/3.49  
% 22.61/3.49  
% 22.61/3.49  ------ Proving...
% 22.61/3.49  
% 22.61/3.49  
% 22.61/3.49  % SZS status Theorem for theBenchmark.p
% 22.61/3.49  
% 22.61/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 22.61/3.49  
% 22.61/3.49  fof(f8,axiom,(
% 22.61/3.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 22.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.61/3.49  
% 22.61/3.49  fof(f22,plain,(
% 22.61/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 22.61/3.49    inference(ennf_transformation,[],[f8])).
% 22.61/3.49  
% 22.61/3.49  fof(f23,plain,(
% 22.61/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 22.61/3.49    inference(flattening,[],[f22])).
% 22.61/3.49  
% 22.61/3.49  fof(f38,plain,(
% 22.61/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 22.61/3.49    inference(nnf_transformation,[],[f23])).
% 22.61/3.49  
% 22.61/3.49  fof(f39,plain,(
% 22.61/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 22.61/3.49    inference(flattening,[],[f38])).
% 22.61/3.49  
% 22.61/3.49  fof(f56,plain,(
% 22.61/3.49    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 22.61/3.49    inference(cnf_transformation,[],[f39])).
% 22.61/3.49  
% 22.61/3.49  fof(f10,axiom,(
% 22.61/3.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 22.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.61/3.49  
% 22.61/3.49  fof(f26,plain,(
% 22.61/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X1,X4) | (~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 22.61/3.49    inference(ennf_transformation,[],[f10])).
% 22.61/3.49  
% 22.61/3.49  fof(f27,plain,(
% 22.61/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_hidden(X1,X4) | ~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 22.61/3.49    inference(flattening,[],[f26])).
% 22.61/3.49  
% 22.61/3.49  fof(f60,plain,(
% 22.61/3.49    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X1,X4) | ~m1_orders_2(X4,X0,X3) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 22.61/3.49    inference(cnf_transformation,[],[f27])).
% 22.61/3.49  
% 22.61/3.49  fof(f11,conjecture,(
% 22.61/3.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2)) => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1))))))),
% 22.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.61/3.49  
% 22.61/3.49  fof(f12,negated_conjecture,(
% 22.61/3.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2)) => k3_orders_2(X0,X2,X1) = k3_orders_2(X0,X3,X1))))))),
% 22.61/3.49    inference(negated_conjecture,[],[f11])).
% 22.61/3.49  
% 22.61/3.49  fof(f28,plain,(
% 22.61/3.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & (m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 22.61/3.49    inference(ennf_transformation,[],[f12])).
% 22.61/3.49  
% 22.61/3.49  fof(f29,plain,(
% 22.61/3.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 22.61/3.49    inference(flattening,[],[f28])).
% 22.61/3.49  
% 22.61/3.49  fof(f43,plain,(
% 22.61/3.49    ( ! [X2,X0,X1] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k3_orders_2(X0,sK5,X1) != k3_orders_2(X0,X2,X1) & m1_orders_2(X2,X0,sK5) & r2_hidden(X1,X2) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 22.61/3.49    introduced(choice_axiom,[])).
% 22.61/3.49  
% 22.61/3.49  fof(f42,plain,(
% 22.61/3.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (k3_orders_2(X0,sK4,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(sK4,X0,X3) & r2_hidden(X1,sK4) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 22.61/3.49    introduced(choice_axiom,[])).
% 22.61/3.49  
% 22.61/3.49  fof(f41,plain,(
% 22.61/3.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k3_orders_2(X0,X2,sK3) != k3_orders_2(X0,X3,sK3) & m1_orders_2(X2,X0,X3) & r2_hidden(sK3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 22.61/3.49    introduced(choice_axiom,[])).
% 22.61/3.49  
% 22.61/3.49  fof(f40,plain,(
% 22.61/3.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(X0,X2,X1) != k3_orders_2(X0,X3,X1) & m1_orders_2(X2,X0,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k3_orders_2(sK2,X2,X1) != k3_orders_2(sK2,X3,X1) & m1_orders_2(X2,sK2,X3) & r2_hidden(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 22.61/3.49    introduced(choice_axiom,[])).
% 22.61/3.49  
% 22.61/3.49  fof(f44,plain,(
% 22.61/3.49    (((k3_orders_2(sK2,sK4,sK3) != k3_orders_2(sK2,sK5,sK3) & m1_orders_2(sK4,sK2,sK5) & r2_hidden(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 22.61/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f43,f42,f41,f40])).
% 22.61/3.49  
% 22.61/3.49  fof(f70,plain,(
% 22.61/3.49    m1_orders_2(sK4,sK2,sK5)),
% 22.61/3.49    inference(cnf_transformation,[],[f44])).
% 22.61/3.49  
% 22.61/3.49  fof(f61,plain,(
% 22.61/3.49    ~v2_struct_0(sK2)),
% 22.61/3.49    inference(cnf_transformation,[],[f44])).
% 22.61/3.49  
% 22.61/3.49  fof(f62,plain,(
% 22.61/3.49    v3_orders_2(sK2)),
% 22.61/3.49    inference(cnf_transformation,[],[f44])).
% 22.61/3.49  
% 22.61/3.49  fof(f63,plain,(
% 22.61/3.49    v4_orders_2(sK2)),
% 22.61/3.49    inference(cnf_transformation,[],[f44])).
% 22.61/3.49  
% 22.61/3.49  fof(f64,plain,(
% 22.61/3.49    v5_orders_2(sK2)),
% 22.61/3.49    inference(cnf_transformation,[],[f44])).
% 22.61/3.49  
% 22.61/3.49  fof(f65,plain,(
% 22.61/3.49    l1_orders_2(sK2)),
% 22.61/3.49    inference(cnf_transformation,[],[f44])).
% 22.61/3.49  
% 22.61/3.49  fof(f67,plain,(
% 22.61/3.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 22.61/3.49    inference(cnf_transformation,[],[f44])).
% 22.61/3.49  
% 22.61/3.49  fof(f68,plain,(
% 22.61/3.49    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))),
% 22.61/3.49    inference(cnf_transformation,[],[f44])).
% 22.61/3.49  
% 22.61/3.49  fof(f58,plain,(
% 22.61/3.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 22.61/3.49    inference(cnf_transformation,[],[f39])).
% 22.61/3.49  
% 22.61/3.49  fof(f5,axiom,(
% 22.61/3.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 22.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.61/3.49  
% 22.61/3.49  fof(f16,plain,(
% 22.61/3.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 22.61/3.49    inference(ennf_transformation,[],[f5])).
% 22.61/3.49  
% 22.61/3.49  fof(f17,plain,(
% 22.61/3.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 22.61/3.49    inference(flattening,[],[f16])).
% 22.61/3.49  
% 22.61/3.49  fof(f53,plain,(
% 22.61/3.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 22.61/3.49    inference(cnf_transformation,[],[f17])).
% 22.61/3.49  
% 22.61/3.49  fof(f1,axiom,(
% 22.61/3.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 22.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.61/3.49  
% 22.61/3.49  fof(f13,plain,(
% 22.61/3.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 22.61/3.49    inference(ennf_transformation,[],[f1])).
% 22.61/3.49  
% 22.61/3.49  fof(f30,plain,(
% 22.61/3.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 22.61/3.49    inference(nnf_transformation,[],[f13])).
% 22.61/3.49  
% 22.61/3.49  fof(f31,plain,(
% 22.61/3.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 22.61/3.49    inference(rectify,[],[f30])).
% 22.61/3.49  
% 22.61/3.49  fof(f32,plain,(
% 22.61/3.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 22.61/3.49    introduced(choice_axiom,[])).
% 22.61/3.49  
% 22.61/3.49  fof(f33,plain,(
% 22.61/3.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 22.61/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 22.61/3.49  
% 22.61/3.49  fof(f45,plain,(
% 22.61/3.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 22.61/3.49    inference(cnf_transformation,[],[f33])).
% 22.61/3.49  
% 22.61/3.49  fof(f57,plain,(
% 22.61/3.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 22.61/3.49    inference(cnf_transformation,[],[f39])).
% 22.61/3.49  
% 22.61/3.49  fof(f6,axiom,(
% 22.61/3.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 22.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.61/3.49  
% 22.61/3.49  fof(f18,plain,(
% 22.61/3.49    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 22.61/3.49    inference(ennf_transformation,[],[f6])).
% 22.61/3.49  
% 22.61/3.49  fof(f19,plain,(
% 22.61/3.49    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 22.61/3.49    inference(flattening,[],[f18])).
% 22.61/3.49  
% 22.61/3.49  fof(f54,plain,(
% 22.61/3.49    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 22.61/3.49    inference(cnf_transformation,[],[f19])).
% 22.61/3.49  
% 22.61/3.49  fof(f2,axiom,(
% 22.61/3.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 22.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.61/3.49  
% 22.61/3.49  fof(f14,plain,(
% 22.61/3.49    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 22.61/3.49    inference(ennf_transformation,[],[f2])).
% 22.61/3.49  
% 22.61/3.49  fof(f34,plain,(
% 22.61/3.49    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 22.61/3.49    inference(nnf_transformation,[],[f14])).
% 22.61/3.49  
% 22.61/3.49  fof(f35,plain,(
% 22.61/3.49    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 22.61/3.49    introduced(choice_axiom,[])).
% 22.61/3.49  
% 22.61/3.49  fof(f36,plain,(
% 22.61/3.49    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 22.61/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 22.61/3.49  
% 22.61/3.49  fof(f48,plain,(
% 22.61/3.49    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 22.61/3.49    inference(cnf_transformation,[],[f36])).
% 22.61/3.49  
% 22.61/3.49  fof(f49,plain,(
% 22.61/3.49    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) )),
% 22.61/3.49    inference(cnf_transformation,[],[f36])).
% 22.61/3.49  
% 22.61/3.49  fof(f9,axiom,(
% 22.61/3.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 22.61/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.61/3.49  
% 22.61/3.49  fof(f24,plain,(
% 22.61/3.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 22.61/3.49    inference(ennf_transformation,[],[f9])).
% 22.61/3.49  
% 22.61/3.49  fof(f25,plain,(
% 22.61/3.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 22.61/3.49    inference(flattening,[],[f24])).
% 22.61/3.49  
% 22.61/3.49  fof(f59,plain,(
% 22.61/3.49    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 22.61/3.49    inference(cnf_transformation,[],[f25])).
% 22.61/3.49  
% 22.61/3.49  fof(f71,plain,(
% 22.61/3.49    k3_orders_2(sK2,sK4,sK3) != k3_orders_2(sK2,sK5,sK3)),
% 22.61/3.49    inference(cnf_transformation,[],[f44])).
% 22.61/3.49  
% 22.61/3.49  fof(f69,plain,(
% 22.61/3.49    r2_hidden(sK3,sK4)),
% 22.61/3.49    inference(cnf_transformation,[],[f44])).
% 22.61/3.49  
% 22.61/3.49  fof(f66,plain,(
% 22.61/3.49    m1_subset_1(sK3,u1_struct_0(sK2))),
% 22.61/3.49    inference(cnf_transformation,[],[f44])).
% 22.61/3.49  
% 22.61/3.49  cnf(c_13,plain,
% 22.61/3.49      ( r2_orders_2(X0,X1,X2)
% 22.61/3.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 22.61/3.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 22.61/3.49      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 22.61/3.49      | v2_struct_0(X0)
% 22.61/3.49      | ~ v3_orders_2(X0)
% 22.61/3.49      | ~ v4_orders_2(X0)
% 22.61/3.49      | ~ v5_orders_2(X0)
% 22.61/3.49      | ~ l1_orders_2(X0) ),
% 22.61/3.49      inference(cnf_transformation,[],[f56]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_15,plain,
% 22.61/3.49      ( ~ r2_orders_2(X0,X1,X2)
% 22.61/3.49      | ~ m1_orders_2(X3,X0,X4)
% 22.61/3.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 22.61/3.49      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
% 22.61/3.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 22.61/3.49      | ~ r2_hidden(X1,X4)
% 22.61/3.49      | ~ r2_hidden(X2,X3)
% 22.61/3.49      | r2_hidden(X1,X3)
% 22.61/3.49      | v2_struct_0(X0)
% 22.61/3.49      | ~ v3_orders_2(X0)
% 22.61/3.49      | ~ v4_orders_2(X0)
% 22.61/3.49      | ~ v5_orders_2(X0)
% 22.61/3.49      | ~ l1_orders_2(X0) ),
% 22.61/3.49      inference(cnf_transformation,[],[f60]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_17,negated_conjecture,
% 22.61/3.49      ( m1_orders_2(sK4,sK2,sK5) ),
% 22.61/3.49      inference(cnf_transformation,[],[f70]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_360,plain,
% 22.61/3.49      ( ~ r2_orders_2(X0,X1,X2)
% 22.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 22.61/3.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.61/3.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 22.61/3.49      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
% 22.61/3.49      | ~ r2_hidden(X1,X4)
% 22.61/3.49      | ~ r2_hidden(X2,X3)
% 22.61/3.49      | r2_hidden(X1,X3)
% 22.61/3.49      | v2_struct_0(X0)
% 22.61/3.49      | ~ v3_orders_2(X0)
% 22.61/3.49      | ~ v4_orders_2(X0)
% 22.61/3.49      | ~ v5_orders_2(X0)
% 22.61/3.49      | ~ l1_orders_2(X0)
% 22.61/3.49      | sK5 != X4
% 22.61/3.49      | sK4 != X3
% 22.61/3.49      | sK2 != X0 ),
% 22.61/3.49      inference(resolution_lifted,[status(thm)],[c_15,c_17]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_361,plain,
% 22.61/3.49      ( ~ r2_orders_2(sK2,X0,X1)
% 22.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ r2_hidden(X0,sK5)
% 22.61/3.49      | ~ r2_hidden(X1,sK4)
% 22.61/3.49      | r2_hidden(X0,sK4)
% 22.61/3.49      | v2_struct_0(sK2)
% 22.61/3.49      | ~ v3_orders_2(sK2)
% 22.61/3.49      | ~ v4_orders_2(sK2)
% 22.61/3.49      | ~ v5_orders_2(sK2)
% 22.61/3.49      | ~ l1_orders_2(sK2) ),
% 22.61/3.49      inference(unflattening,[status(thm)],[c_360]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_26,negated_conjecture,
% 22.61/3.49      ( ~ v2_struct_0(sK2) ),
% 22.61/3.49      inference(cnf_transformation,[],[f61]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_25,negated_conjecture,
% 22.61/3.49      ( v3_orders_2(sK2) ),
% 22.61/3.49      inference(cnf_transformation,[],[f62]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_24,negated_conjecture,
% 22.61/3.49      ( v4_orders_2(sK2) ),
% 22.61/3.49      inference(cnf_transformation,[],[f63]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_23,negated_conjecture,
% 22.61/3.49      ( v5_orders_2(sK2) ),
% 22.61/3.49      inference(cnf_transformation,[],[f64]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_22,negated_conjecture,
% 22.61/3.49      ( l1_orders_2(sK2) ),
% 22.61/3.49      inference(cnf_transformation,[],[f65]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_20,negated_conjecture,
% 22.61/3.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 22.61/3.49      inference(cnf_transformation,[],[f67]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_19,negated_conjecture,
% 22.61/3.49      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 22.61/3.49      inference(cnf_transformation,[],[f68]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_363,plain,
% 22.61/3.49      ( r2_hidden(X0,sK4)
% 22.61/3.49      | ~ r2_hidden(X1,sK4)
% 22.61/3.49      | ~ r2_hidden(X0,sK5)
% 22.61/3.49      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 22.61/3.49      | ~ r2_orders_2(sK2,X0,X1) ),
% 22.61/3.49      inference(global_propositional_subsumption,
% 22.61/3.49                [status(thm)],
% 22.61/3.49                [c_361,c_26,c_25,c_24,c_23,c_22,c_20,c_19]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_364,plain,
% 22.61/3.49      ( ~ r2_orders_2(sK2,X0,X1)
% 22.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.61/3.49      | ~ r2_hidden(X0,sK5)
% 22.61/3.49      | ~ r2_hidden(X1,sK4)
% 22.61/3.49      | r2_hidden(X0,sK4) ),
% 22.61/3.49      inference(renaming,[status(thm)],[c_363]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_531,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 22.61/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 22.61/3.49      | ~ m1_subset_1(X3,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X4,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
% 22.61/3.49      | ~ r2_hidden(X0,k3_orders_2(X1,X5,X2))
% 22.61/3.49      | ~ r2_hidden(X4,sK5)
% 22.61/3.49      | ~ r2_hidden(X3,sK4)
% 22.61/3.49      | r2_hidden(X4,sK4)
% 22.61/3.49      | v2_struct_0(X1)
% 22.61/3.49      | ~ v3_orders_2(X1)
% 22.61/3.49      | ~ v4_orders_2(X1)
% 22.61/3.49      | ~ v5_orders_2(X1)
% 22.61/3.49      | ~ l1_orders_2(X1)
% 22.61/3.49      | X4 != X0
% 22.61/3.49      | X3 != X2
% 22.61/3.49      | sK2 != X1 ),
% 22.61/3.49      inference(resolution_lifted,[status(thm)],[c_13,c_364]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_532,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ r2_hidden(X1,k3_orders_2(sK2,X2,X0))
% 22.61/3.49      | ~ r2_hidden(X1,sK5)
% 22.61/3.49      | ~ r2_hidden(X0,sK4)
% 22.61/3.49      | r2_hidden(X1,sK4)
% 22.61/3.49      | v2_struct_0(sK2)
% 22.61/3.49      | ~ v3_orders_2(sK2)
% 22.61/3.49      | ~ v4_orders_2(sK2)
% 22.61/3.49      | ~ v5_orders_2(sK2)
% 22.61/3.49      | ~ l1_orders_2(sK2) ),
% 22.61/3.49      inference(unflattening,[status(thm)],[c_531]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_534,plain,
% 22.61/3.49      ( r2_hidden(X1,sK4)
% 22.61/3.49      | ~ r2_hidden(X0,sK4)
% 22.61/3.49      | ~ r2_hidden(X1,sK5)
% 22.61/3.49      | ~ r2_hidden(X1,k3_orders_2(sK2,X2,X0))
% 22.61/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 22.61/3.49      inference(global_propositional_subsumption,
% 22.61/3.49                [status(thm)],
% 22.61/3.49                [c_532,c_26,c_25,c_24,c_23,c_22]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_535,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ r2_hidden(X0,k3_orders_2(sK2,X2,X1))
% 22.61/3.49      | ~ r2_hidden(X0,sK5)
% 22.61/3.49      | ~ r2_hidden(X1,sK4)
% 22.61/3.49      | r2_hidden(X0,sK4) ),
% 22.61/3.49      inference(renaming,[status(thm)],[c_534]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_10194,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
% 22.61/3.49      | ~ r2_hidden(X0,sK4)
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,X1,X0))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK5)
% 22.61/3.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_535]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_74868,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,X0,sK3))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK5)
% 22.61/3.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4)
% 22.61/3.49      | ~ r2_hidden(sK3,sK4) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_10194]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_83558,plain,
% 22.61/3.49      ( ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK5)
% 22.61/3.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4)
% 22.61/3.49      | ~ r2_hidden(sK3,sK4) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_74868]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_11,plain,
% 22.61/3.49      ( ~ r2_orders_2(X0,X1,X2)
% 22.61/3.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 22.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 22.61/3.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 22.61/3.49      | ~ r2_hidden(X1,X3)
% 22.61/3.49      | r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 22.61/3.49      | v2_struct_0(X0)
% 22.61/3.49      | ~ v3_orders_2(X0)
% 22.61/3.49      | ~ v4_orders_2(X0)
% 22.61/3.49      | ~ v5_orders_2(X0)
% 22.61/3.49      | ~ l1_orders_2(X0) ),
% 22.61/3.49      inference(cnf_transformation,[],[f58]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_492,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 22.61/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 22.61/3.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 22.61/3.49      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 22.61/3.49      | ~ r2_hidden(X2,X4)
% 22.61/3.49      | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
% 22.61/3.49      | r2_hidden(X2,k3_orders_2(X1,X4,X0))
% 22.61/3.49      | v2_struct_0(X1)
% 22.61/3.49      | ~ v3_orders_2(X1)
% 22.61/3.49      | ~ v4_orders_2(X1)
% 22.61/3.49      | ~ v5_orders_2(X1)
% 22.61/3.49      | ~ l1_orders_2(X1) ),
% 22.61/3.49      inference(resolution,[status(thm)],[c_13,c_11]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_8,plain,
% 22.61/3.49      ( m1_subset_1(X0,X1)
% 22.61/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 22.61/3.49      | ~ r2_hidden(X0,X2) ),
% 22.61/3.49      inference(cnf_transformation,[],[f53]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_518,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 22.61/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 22.61/3.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 22.61/3.49      | ~ r2_hidden(X4,X3)
% 22.61/3.49      | ~ r2_hidden(X4,k3_orders_2(X1,X2,X0))
% 22.61/3.49      | r2_hidden(X4,k3_orders_2(X1,X3,X0))
% 22.61/3.49      | v2_struct_0(X1)
% 22.61/3.49      | ~ v3_orders_2(X1)
% 22.61/3.49      | ~ v4_orders_2(X1)
% 22.61/3.49      | ~ v5_orders_2(X1)
% 22.61/3.49      | ~ l1_orders_2(X1) ),
% 22.61/3.49      inference(forward_subsumption_resolution,[status(thm)],[c_492,c_8]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_569,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 22.61/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 22.61/3.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 22.61/3.49      | ~ r2_hidden(X4,X3)
% 22.61/3.49      | ~ r2_hidden(X4,k3_orders_2(X1,X2,X0))
% 22.61/3.49      | r2_hidden(X4,k3_orders_2(X1,X3,X0))
% 22.61/3.49      | v2_struct_0(X1)
% 22.61/3.49      | ~ v3_orders_2(X1)
% 22.61/3.49      | ~ v4_orders_2(X1)
% 22.61/3.49      | ~ v5_orders_2(X1)
% 22.61/3.49      | sK2 != X1 ),
% 22.61/3.49      inference(resolution_lifted,[status(thm)],[c_518,c_22]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_570,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ r2_hidden(X3,X2)
% 22.61/3.49      | ~ r2_hidden(X3,k3_orders_2(sK2,X1,X0))
% 22.61/3.49      | r2_hidden(X3,k3_orders_2(sK2,X2,X0))
% 22.61/3.49      | v2_struct_0(sK2)
% 22.61/3.49      | ~ v3_orders_2(sK2)
% 22.61/3.49      | ~ v4_orders_2(sK2)
% 22.61/3.49      | ~ v5_orders_2(sK2) ),
% 22.61/3.49      inference(unflattening,[status(thm)],[c_569]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_572,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ r2_hidden(X3,X2)
% 22.61/3.49      | ~ r2_hidden(X3,k3_orders_2(sK2,X1,X0))
% 22.61/3.49      | r2_hidden(X3,k3_orders_2(sK2,X2,X0)) ),
% 22.61/3.49      inference(global_propositional_subsumption,
% 22.61/3.49                [status(thm)],
% 22.61/3.49                [c_570,c_26,c_25,c_24,c_23]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_573,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ r2_hidden(X3,X1)
% 22.61/3.49      | ~ r2_hidden(X3,k3_orders_2(sK2,X2,X0))
% 22.61/3.49      | r2_hidden(X3,k3_orders_2(sK2,X1,X0)) ),
% 22.61/3.49      inference(renaming,[status(thm)],[c_572]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_1516,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | ~ r2_hidden(X2,X1)
% 22.61/3.49      | ~ r2_hidden(X2,k3_orders_2(sK2,X0,sK3))
% 22.61/3.49      | r2_hidden(X2,k3_orders_2(sK2,X1,sK3)) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_573]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_1729,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(k3_orders_2(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | ~ r2_hidden(X1,X0)
% 22.61/3.49      | r2_hidden(X1,k3_orders_2(sK2,X0,sK3))
% 22.61/3.49      | ~ r2_hidden(X1,k3_orders_2(sK2,k3_orders_2(sK2,sK4,sK3),sK3)) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_1516]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_9195,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(k3_orders_2(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),X0)
% 22.61/3.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,X0,sK3))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,k3_orders_2(sK2,sK4,sK3),sK3)) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_1729]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_24506,plain,
% 22.61/3.49      ( ~ m1_subset_1(k3_orders_2(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,k3_orders_2(sK2,sK4,sK3),sK3))
% 22.61/3.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK5) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_9195]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_2,plain,
% 22.61/3.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 22.61/3.49      inference(cnf_transformation,[],[f45]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_2111,plain,
% 22.61/3.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,sK5) | ~ r1_tarski(X1,sK5) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_2]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_5071,plain,
% 22.61/3.49      ( r2_hidden(X0,sK5) | ~ r2_hidden(X0,sK4) | ~ r1_tarski(sK4,sK5) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_2111]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_10204,plain,
% 22.61/3.49      ( r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK5)
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4)
% 22.61/3.49      | ~ r1_tarski(sK4,sK5) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_5071]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_1714,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | ~ r2_hidden(X1,X0)
% 22.61/3.49      | r2_hidden(X1,k3_orders_2(sK2,X0,sK3))
% 22.61/3.49      | ~ r2_hidden(X1,k3_orders_2(sK2,sK5,sK3)) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_1516]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_1914,plain,
% 22.61/3.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ r2_hidden(X0,k3_orders_2(sK2,sK5,sK3))
% 22.61/3.49      | r2_hidden(X0,k3_orders_2(sK2,sK4,sK3))
% 22.61/3.49      | ~ r2_hidden(X0,sK4) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_1714]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_10205,plain,
% 22.61/3.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
% 22.61/3.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_1914]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_12,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 22.61/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 22.61/3.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 22.61/3.49      | r2_hidden(X2,X3)
% 22.61/3.49      | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
% 22.61/3.49      | v2_struct_0(X1)
% 22.61/3.49      | ~ v3_orders_2(X1)
% 22.61/3.49      | ~ v4_orders_2(X1)
% 22.61/3.49      | ~ v5_orders_2(X1)
% 22.61/3.49      | ~ l1_orders_2(X1) ),
% 22.61/3.49      inference(cnf_transformation,[],[f57]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_595,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 22.61/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 22.61/3.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 22.61/3.49      | r2_hidden(X2,X3)
% 22.61/3.49      | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
% 22.61/3.49      | v2_struct_0(X1)
% 22.61/3.49      | ~ v3_orders_2(X1)
% 22.61/3.49      | ~ v4_orders_2(X1)
% 22.61/3.49      | ~ v5_orders_2(X1)
% 22.61/3.49      | sK2 != X1 ),
% 22.61/3.49      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_596,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | r2_hidden(X0,X2)
% 22.61/3.49      | ~ r2_hidden(X0,k3_orders_2(sK2,X2,X1))
% 22.61/3.49      | v2_struct_0(sK2)
% 22.61/3.49      | ~ v3_orders_2(sK2)
% 22.61/3.49      | ~ v4_orders_2(sK2)
% 22.61/3.49      | ~ v5_orders_2(sK2) ),
% 22.61/3.49      inference(unflattening,[status(thm)],[c_595]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_600,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | r2_hidden(X0,X2)
% 22.61/3.49      | ~ r2_hidden(X0,k3_orders_2(sK2,X2,X1)) ),
% 22.61/3.49      inference(global_propositional_subsumption,
% 22.61/3.49                [status(thm)],
% 22.61/3.49                [c_596,c_26,c_25,c_24,c_23]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_601,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | r2_hidden(X1,X2)
% 22.61/3.49      | ~ r2_hidden(X1,k3_orders_2(sK2,X2,X0)) ),
% 22.61/3.49      inference(renaming,[status(thm)],[c_600]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_1511,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | r2_hidden(X0,X1)
% 22.61/3.49      | ~ r2_hidden(X0,k3_orders_2(sK2,X1,sK3)) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_601]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_3101,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),X0)
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,X0,sK3)) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_1511]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_10203,plain,
% 22.61/3.49      ( ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3))
% 22.61/3.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK4) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_3101]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_10192,plain,
% 22.61/3.49      ( ~ m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
% 22.61/3.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),sK5) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_3101]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_1747,plain,
% 22.61/3.49      ( ~ m1_subset_1(k3_orders_2(sK2,sK4,sK3),k1_zfmisc_1(X0))
% 22.61/3.49      | m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),X0)
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3)) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_8]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_3571,plain,
% 22.61/3.49      ( ~ m1_subset_1(k3_orders_2(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3)) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_1747]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_1719,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ r2_hidden(X1,X0)
% 22.61/3.49      | r2_hidden(X1,k3_orders_2(sK2,X0,sK3))
% 22.61/3.49      | ~ r2_hidden(X1,k3_orders_2(sK2,sK4,sK3)) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_1516]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_1941,plain,
% 22.61/3.49      ( ~ m1_subset_1(k3_orders_2(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | r2_hidden(X0,k3_orders_2(sK2,k3_orders_2(sK2,sK4,sK3),sK3))
% 22.61/3.49      | ~ r2_hidden(X0,k3_orders_2(sK2,sK4,sK3)) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_1719]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_3282,plain,
% 22.61/3.49      ( ~ m1_subset_1(k3_orders_2(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,k3_orders_2(sK2,sK4,sK3),sK3))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3)) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_1941]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_1587,plain,
% 22.61/3.49      ( ~ m1_subset_1(k3_orders_2(sK2,sK5,sK3),k1_zfmisc_1(X0))
% 22.61/3.49      | m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),X0)
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3)) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_8]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_2163,plain,
% 22.61/3.49      ( ~ m1_subset_1(k3_orders_2(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | m1_subset_1(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),u1_struct_0(sK2))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3)) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_1587]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_9,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 22.61/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 22.61/3.49      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 22.61/3.49      | v2_struct_0(X1)
% 22.61/3.49      | ~ v3_orders_2(X1)
% 22.61/3.49      | ~ v4_orders_2(X1)
% 22.61/3.49      | ~ v5_orders_2(X1)
% 22.61/3.49      | ~ l1_orders_2(X1) ),
% 22.61/3.49      inference(cnf_transformation,[],[f54]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_622,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 22.61/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 22.61/3.49      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 22.61/3.49      | v2_struct_0(X1)
% 22.61/3.49      | ~ v3_orders_2(X1)
% 22.61/3.49      | ~ v4_orders_2(X1)
% 22.61/3.49      | ~ v5_orders_2(X1)
% 22.61/3.49      | sK2 != X1 ),
% 22.61/3.49      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_623,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | m1_subset_1(k3_orders_2(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | v2_struct_0(sK2)
% 22.61/3.49      | ~ v3_orders_2(sK2)
% 22.61/3.49      | ~ v4_orders_2(sK2)
% 22.61/3.49      | ~ v5_orders_2(sK2) ),
% 22.61/3.49      inference(unflattening,[status(thm)],[c_622]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_627,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | m1_subset_1(k3_orders_2(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 22.61/3.49      inference(global_propositional_subsumption,
% 22.61/3.49                [status(thm)],
% 22.61/3.49                [c_623,c_26,c_25,c_24,c_23]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_1506,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | m1_subset_1(k3_orders_2(sK2,X0,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_627]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_1608,plain,
% 22.61/3.49      ( m1_subset_1(k3_orders_2(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 22.61/3.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_1506]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_1605,plain,
% 22.61/3.49      ( m1_subset_1(k3_orders_2(sK2,sK5,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_1506]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_4,plain,
% 22.61/3.49      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 22.61/3.49      inference(cnf_transformation,[],[f48]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_1544,plain,
% 22.61/3.49      ( r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
% 22.61/3.49      | r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3))
% 22.61/3.49      | k3_orders_2(sK2,sK4,sK3) = k3_orders_2(sK2,sK5,sK3) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_4]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_3,plain,
% 22.61/3.49      ( ~ r2_hidden(sK1(X0,X1),X1)
% 22.61/3.49      | ~ r2_hidden(sK1(X0,X1),X0)
% 22.61/3.49      | X1 = X0 ),
% 22.61/3.49      inference(cnf_transformation,[],[f49]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_1541,plain,
% 22.61/3.49      ( ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK5,sK3))
% 22.61/3.49      | ~ r2_hidden(sK1(k3_orders_2(sK2,sK5,sK3),k3_orders_2(sK2,sK4,sK3)),k3_orders_2(sK2,sK4,sK3))
% 22.61/3.49      | k3_orders_2(sK2,sK4,sK3) = k3_orders_2(sK2,sK5,sK3) ),
% 22.61/3.49      inference(instantiation,[status(thm)],[c_3]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_14,plain,
% 22.61/3.49      ( ~ m1_orders_2(X0,X1,X2)
% 22.61/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 22.61/3.49      | r1_tarski(X0,X2)
% 22.61/3.49      | v2_struct_0(X1)
% 22.61/3.49      | ~ v3_orders_2(X1)
% 22.61/3.49      | ~ v4_orders_2(X1)
% 22.61/3.49      | ~ v5_orders_2(X1)
% 22.61/3.49      | ~ l1_orders_2(X1) ),
% 22.61/3.49      inference(cnf_transformation,[],[f59]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_347,plain,
% 22.61/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 22.61/3.49      | r1_tarski(X2,X0)
% 22.61/3.49      | v2_struct_0(X1)
% 22.61/3.49      | ~ v3_orders_2(X1)
% 22.61/3.49      | ~ v4_orders_2(X1)
% 22.61/3.49      | ~ v5_orders_2(X1)
% 22.61/3.49      | ~ l1_orders_2(X1)
% 22.61/3.49      | sK5 != X0
% 22.61/3.49      | sK4 != X2
% 22.61/3.49      | sK2 != X1 ),
% 22.61/3.49      inference(resolution_lifted,[status(thm)],[c_14,c_17]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_348,plain,
% 22.61/3.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 22.61/3.49      | r1_tarski(sK4,sK5)
% 22.61/3.49      | v2_struct_0(sK2)
% 22.61/3.49      | ~ v3_orders_2(sK2)
% 22.61/3.49      | ~ v4_orders_2(sK2)
% 22.61/3.49      | ~ v5_orders_2(sK2)
% 22.61/3.49      | ~ l1_orders_2(sK2) ),
% 22.61/3.49      inference(unflattening,[status(thm)],[c_347]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_16,negated_conjecture,
% 22.61/3.49      ( k3_orders_2(sK2,sK4,sK3) != k3_orders_2(sK2,sK5,sK3) ),
% 22.61/3.49      inference(cnf_transformation,[],[f71]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_18,negated_conjecture,
% 22.61/3.49      ( r2_hidden(sK3,sK4) ),
% 22.61/3.49      inference(cnf_transformation,[],[f69]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(c_21,negated_conjecture,
% 22.61/3.49      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 22.61/3.49      inference(cnf_transformation,[],[f66]) ).
% 22.61/3.49  
% 22.61/3.49  cnf(contradiction,plain,
% 22.61/3.49      ( $false ),
% 22.61/3.49      inference(minisat,
% 22.61/3.49                [status(thm)],
% 22.61/3.49                [c_83558,c_24506,c_10204,c_10205,c_10203,c_10192,c_3571,
% 22.61/3.49                 c_3282,c_2163,c_1608,c_1605,c_1544,c_1541,c_348,c_16,
% 22.61/3.49                 c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26]) ).
% 22.61/3.49  
% 22.61/3.49  
% 22.61/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 22.61/3.49  
% 22.61/3.49  ------                               Statistics
% 22.61/3.49  
% 22.61/3.49  ------ General
% 22.61/3.49  
% 22.61/3.49  abstr_ref_over_cycles:                  0
% 22.61/3.49  abstr_ref_under_cycles:                 0
% 22.61/3.49  gc_basic_clause_elim:                   0
% 22.61/3.49  forced_gc_time:                         0
% 22.61/3.49  parsing_time:                           0.01
% 22.61/3.49  unif_index_cands_time:                  0.
% 22.61/3.49  unif_index_add_time:                    0.
% 22.61/3.49  orderings_time:                         0.
% 22.61/3.49  out_proof_time:                         0.015
% 22.61/3.49  total_time:                             2.972
% 22.61/3.49  num_of_symbols:                         50
% 22.61/3.49  num_of_terms:                           34578
% 22.61/3.49  
% 22.61/3.49  ------ Preprocessing
% 22.61/3.49  
% 22.61/3.49  num_of_splits:                          0
% 22.61/3.49  num_of_split_atoms:                     0
% 22.61/3.49  num_of_reused_defs:                     0
% 22.61/3.49  num_eq_ax_congr_red:                    17
% 22.61/3.49  num_of_sem_filtered_clauses:            1
% 22.61/3.49  num_of_subtypes:                        0
% 22.61/3.49  monotx_restored_types:                  0
% 22.61/3.49  sat_num_of_epr_types:                   0
% 22.61/3.49  sat_num_of_non_cyclic_types:            0
% 22.61/3.49  sat_guarded_non_collapsed_types:        0
% 22.61/3.49  num_pure_diseq_elim:                    0
% 22.61/3.49  simp_replaced_by:                       0
% 22.61/3.49  res_preprocessed:                       101
% 22.61/3.49  prep_upred:                             0
% 22.61/3.49  prep_unflattend:                        35
% 22.61/3.49  smt_new_axioms:                         0
% 22.61/3.49  pred_elim_cands:                        3
% 22.61/3.49  pred_elim:                              7
% 22.61/3.49  pred_elim_cl:                           8
% 22.61/3.49  pred_elim_cycles:                       10
% 22.61/3.49  merged_defs:                            8
% 22.61/3.49  merged_defs_ncl:                        0
% 22.61/3.49  bin_hyper_res:                          8
% 22.61/3.49  prep_cycles:                            4
% 22.61/3.49  pred_elim_time:                         0.009
% 22.61/3.49  splitting_time:                         0.
% 22.61/3.49  sem_filter_time:                        0.
% 22.61/3.49  monotx_time:                            0.001
% 22.61/3.49  subtype_inf_time:                       0.
% 22.61/3.49  
% 22.61/3.49  ------ Problem properties
% 22.61/3.49  
% 22.61/3.49  clauses:                                19
% 22.61/3.49  conjectures:                            5
% 22.61/3.49  epr:                                    4
% 22.61/3.49  horn:                                   17
% 22.61/3.49  ground:                                 6
% 22.61/3.49  unary:                                  6
% 22.61/3.49  binary:                                 5
% 22.61/3.49  lits:                                   49
% 22.61/3.49  lits_eq:                                3
% 22.61/3.49  fd_pure:                                0
% 22.61/3.49  fd_pseudo:                              0
% 22.61/3.49  fd_cond:                                0
% 22.61/3.49  fd_pseudo_cond:                         2
% 22.61/3.49  ac_symbols:                             0
% 22.61/3.49  
% 22.61/3.49  ------ Propositional Solver
% 22.61/3.49  
% 22.61/3.49  prop_solver_calls:                      30
% 22.61/3.49  prop_fast_solver_calls:                 3459
% 22.61/3.49  smt_solver_calls:                       0
% 22.61/3.49  smt_fast_solver_calls:                  0
% 22.61/3.49  prop_num_of_clauses:                    10834
% 22.61/3.49  prop_preprocess_simplified:             16567
% 22.61/3.49  prop_fo_subsumed:                       41
% 22.61/3.49  prop_solver_time:                       0.
% 22.61/3.49  smt_solver_time:                        0.
% 22.61/3.49  smt_fast_solver_time:                   0.
% 22.61/3.49  prop_fast_solver_time:                  0.
% 22.61/3.49  prop_unsat_core_time:                   0.002
% 22.61/3.49  
% 22.61/3.49  ------ QBF
% 22.61/3.49  
% 22.61/3.49  qbf_q_res:                              0
% 22.61/3.49  qbf_num_tautologies:                    0
% 22.61/3.49  qbf_prep_cycles:                        0
% 22.61/3.49  
% 22.61/3.49  ------ BMC1
% 22.61/3.49  
% 22.61/3.49  bmc1_current_bound:                     -1
% 22.61/3.49  bmc1_last_solved_bound:                 -1
% 22.61/3.49  bmc1_unsat_core_size:                   -1
% 22.61/3.49  bmc1_unsat_core_parents_size:           -1
% 22.61/3.49  bmc1_merge_next_fun:                    0
% 22.61/3.49  bmc1_unsat_core_clauses_time:           0.
% 22.61/3.49  
% 22.61/3.49  ------ Instantiation
% 22.61/3.49  
% 22.61/3.49  inst_num_of_clauses:                    1913
% 22.61/3.49  inst_num_in_passive:                    1206
% 22.61/3.49  inst_num_in_active:                     679
% 22.61/3.49  inst_num_in_unprocessed:                27
% 22.61/3.49  inst_num_of_loops:                      994
% 22.61/3.49  inst_num_of_learning_restarts:          0
% 22.61/3.49  inst_num_moves_active_passive:          310
% 22.61/3.49  inst_lit_activity:                      0
% 22.61/3.49  inst_lit_activity_moves:                0
% 22.61/3.49  inst_num_tautologies:                   0
% 22.61/3.49  inst_num_prop_implied:                  0
% 22.61/3.49  inst_num_existing_simplified:           0
% 22.61/3.49  inst_num_eq_res_simplified:             0
% 22.61/3.49  inst_num_child_elim:                    0
% 22.61/3.49  inst_num_of_dismatching_blockings:      2369
% 22.61/3.49  inst_num_of_non_proper_insts:           2858
% 22.61/3.49  inst_num_of_duplicates:                 0
% 22.61/3.49  inst_inst_num_from_inst_to_res:         0
% 22.61/3.49  inst_dismatching_checking_time:         0.
% 22.61/3.49  
% 22.61/3.49  ------ Resolution
% 22.61/3.49  
% 22.61/3.49  res_num_of_clauses:                     0
% 22.61/3.49  res_num_in_passive:                     0
% 22.61/3.49  res_num_in_active:                      0
% 22.61/3.49  res_num_of_loops:                       105
% 22.61/3.49  res_forward_subset_subsumed:            279
% 22.61/3.49  res_backward_subset_subsumed:           0
% 22.61/3.49  res_forward_subsumed:                   0
% 22.61/3.49  res_backward_subsumed:                  0
% 22.61/3.49  res_forward_subsumption_resolution:     1
% 22.61/3.49  res_backward_subsumption_resolution:    0
% 22.61/3.49  res_clause_to_clause_subsumption:       109784
% 22.61/3.49  res_orphan_elimination:                 0
% 22.61/3.49  res_tautology_del:                      203
% 22.61/3.49  res_num_eq_res_simplified:              0
% 22.61/3.49  res_num_sel_changes:                    0
% 22.61/3.49  res_moves_from_active_to_pass:          0
% 22.61/3.49  
% 22.61/3.49  ------ Superposition
% 22.61/3.49  
% 22.61/3.49  sup_time_total:                         0.
% 22.61/3.49  sup_time_generating:                    0.
% 22.61/3.49  sup_time_sim_full:                      0.
% 22.61/3.49  sup_time_sim_immed:                     0.
% 22.61/3.49  
% 22.61/3.49  sup_num_of_clauses:                     1687
% 22.61/3.49  sup_num_in_active:                      198
% 22.61/3.49  sup_num_in_passive:                     1489
% 22.61/3.49  sup_num_of_loops:                       198
% 22.61/3.49  sup_fw_superposition:                   682
% 22.61/3.49  sup_bw_superposition:                   2360
% 22.61/3.49  sup_immediate_simplified:               1211
% 22.61/3.49  sup_given_eliminated:                   0
% 22.61/3.49  comparisons_done:                       0
% 22.61/3.49  comparisons_avoided:                    0
% 22.61/3.49  
% 22.61/3.49  ------ Simplifications
% 22.61/3.49  
% 22.61/3.49  
% 22.61/3.49  sim_fw_subset_subsumed:                 12
% 22.61/3.49  sim_bw_subset_subsumed:                 2
% 22.61/3.49  sim_fw_subsumed:                        1133
% 22.61/3.49  sim_bw_subsumed:                        25
% 22.61/3.49  sim_fw_subsumption_res:                 105
% 22.61/3.49  sim_bw_subsumption_res:                 44
% 22.61/3.49  sim_tautology_del:                      122
% 22.61/3.49  sim_eq_tautology_del:                   35
% 22.61/3.49  sim_eq_res_simp:                        77
% 22.61/3.49  sim_fw_demodulated:                     0
% 22.61/3.49  sim_bw_demodulated:                     0
% 22.61/3.49  sim_light_normalised:                   0
% 22.61/3.49  sim_joinable_taut:                      0
% 22.61/3.49  sim_joinable_simp:                      0
% 22.61/3.49  sim_ac_normalised:                      0
% 22.61/3.49  sim_smt_subsumption:                    0
% 22.61/3.49  
%------------------------------------------------------------------------------
