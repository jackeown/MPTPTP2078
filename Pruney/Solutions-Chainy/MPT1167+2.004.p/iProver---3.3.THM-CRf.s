%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:42 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  162 (2959 expanded)
%              Number of clauses        :  116 ( 606 expanded)
%              Number of leaves         :   14 (1249 expanded)
%              Depth                    :   32
%              Number of atoms          :  898 (35975 expanded)
%              Number of equality atoms :  226 (1330 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   28 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
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

fof(f5,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_hidden(X1,X4)
                      & m1_orders_2(X4,X0,X3)
                      & r2_hidden(X2,X4)
                      & r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_hidden(X1,X4)
                      & m1_orders_2(X4,X0,X3)
                      & r2_hidden(X2,X4)
                      & r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r2_hidden(X1,X4)
          & m1_orders_2(X4,X0,X3)
          & r2_hidden(X2,X4)
          & r2_hidden(X1,X3)
          & r2_orders_2(X0,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(X1,sK5)
        & m1_orders_2(sK5,X0,X3)
        & r2_hidden(X2,sK5)
        & r2_hidden(X1,X3)
        & r2_orders_2(X0,X1,X2)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_hidden(X1,X4)
              & m1_orders_2(X4,X0,X3)
              & r2_hidden(X2,X4)
              & r2_hidden(X1,X3)
              & r2_orders_2(X0,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X4] :
            ( ~ r2_hidden(X1,X4)
            & m1_orders_2(X4,X0,sK4)
            & r2_hidden(X2,X4)
            & r2_hidden(X1,sK4)
            & r2_orders_2(X0,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(X1,X4)
                  & m1_orders_2(X4,X0,X3)
                  & r2_hidden(X2,X4)
                  & r2_hidden(X1,X3)
                  & r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_hidden(X1,X4)
                & m1_orders_2(X4,X0,X3)
                & r2_hidden(sK3,X4)
                & r2_hidden(X1,X3)
                & r2_orders_2(X0,X1,sK3)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_hidden(X1,X4)
                      & m1_orders_2(X4,X0,X3)
                      & r2_hidden(X2,X4)
                      & r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r2_hidden(sK2,X4)
                    & m1_orders_2(X4,X0,X3)
                    & r2_hidden(X2,X4)
                    & r2_hidden(sK2,X3)
                    & r2_orders_2(X0,sK2,X2)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(X1,X4)
                        & m1_orders_2(X4,X0,X3)
                        & r2_hidden(X2,X4)
                        & r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_hidden(X1,X4)
                      & m1_orders_2(X4,sK1,X3)
                      & r2_hidden(X2,X4)
                      & r2_hidden(X1,X3)
                      & r2_orders_2(sK1,X1,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r2_hidden(sK2,sK5)
    & m1_orders_2(sK5,sK1,sK4)
    & r2_hidden(sK3,sK5)
    & r2_hidden(sK2,sK4)
    & r2_orders_2(sK1,sK2,sK3)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f13,f24,f23,f22,f21,f20])).

fof(f44,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    r2_orders_2(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X3] :
                          ( k3_orders_2(X0,X1,X3) = X2
                          & r2_hidden(X3,X1)
                          & m1_subset_1(X3,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X4] :
                          ( k3_orders_2(X0,X1,X4) = X2
                          & r2_hidden(X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ( k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2
                        & r2_hidden(sK0(X0,X1,X2),X1)
                        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    m1_orders_2(sK5,sK1,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f33,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r2_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ~ r2_orders_2(X0,X2,X3)
                  | ~ r2_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ~ r2_orders_2(X0,X2,X3)
                  | ~ r2_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X0,X1,X3)
      | ~ r2_orders_2(X0,X2,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    r2_hidden(sK3,sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ~ r2_hidden(sK2,sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f30])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1030,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1376,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1030])).

cnf(c_14,negated_conjecture,
    ( r2_orders_2(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1031,negated_conjecture,
    ( r2_orders_2(sK1,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1375,plain,
    ( r2_orders_2(sK1,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1031])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1029,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1377,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1029])).

cnf(c_3,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_22,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_404,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_405,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_21,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_20,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_409,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_23,c_21,c_20,c_19])).

cnf(c_1020,plain,
    ( ~ m1_orders_2(X0_48,sK1,X1_48)
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,X1_48,sK0(sK1,X1_48,X0_48)) = X0_48
    | k1_xboole_0 = X1_48 ),
    inference(subtyping,[status(esa)],[c_409])).

cnf(c_1386,plain,
    ( k3_orders_2(sK1,X0_48,sK0(sK1,X0_48,X1_48)) = X1_48
    | k1_xboole_0 = X0_48
    | m1_orders_2(X1_48,sK1,X0_48) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_2257,plain,
    ( k3_orders_2(sK1,sK4,sK0(sK1,sK4,X0_48)) = X0_48
    | sK4 = k1_xboole_0
    | m1_orders_2(X0_48,sK1,sK4) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1377,c_1386])).

cnf(c_2427,plain,
    ( k3_orders_2(sK1,sK4,sK0(sK1,sK4,sK5)) = sK5
    | sK4 = k1_xboole_0
    | m1_orders_2(sK5,sK1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1376,c_2257])).

cnf(c_11,negated_conjecture,
    ( m1_orders_2(sK5,sK1,sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_36,plain,
    ( m1_orders_2(sK5,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2444,plain,
    ( sK4 = k1_xboole_0
    | k3_orders_2(sK1,sK4,sK0(sK1,sK4,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2427,c_36])).

cnf(c_2445,plain,
    ( k3_orders_2(sK1,sK4,sK0(sK1,sK4,sK5)) = sK5
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2444])).

cnf(c_9,plain,
    ( r2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_249,plain,
    ( r2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_250,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_249])).

cnf(c_254,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_250,c_23,c_21,c_20,c_19])).

cnf(c_255,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_254])).

cnf(c_1026,plain,
    ( r2_orders_2(sK1,X0_48,X1_48)
    | ~ r2_hidden(X0_48,k3_orders_2(sK1,X2_48,X1_48))
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_255])).

cnf(c_1380,plain,
    ( r2_orders_2(sK1,X0_48,X1_48) = iProver_top
    | r2_hidden(X0_48,k3_orders_2(sK1,X2_48,X1_48)) != iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1026])).

cnf(c_2451,plain,
    ( sK4 = k1_xboole_0
    | r2_orders_2(sK1,X0_48,sK0(sK1,sK4,sK5)) = iProver_top
    | r2_hidden(X0_48,sK5) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2445,c_1380])).

cnf(c_31,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_32,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1037,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1755,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1037])).

cnf(c_5,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_350,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_22])).

cnf(c_351,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_355,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_351,c_23,c_21,c_20,c_19])).

cnf(c_1022,plain,
    ( ~ m1_orders_2(X0_48,sK1,X1_48)
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X1_48,X0_48),u1_struct_0(sK1))
    | k1_xboole_0 = X1_48 ),
    inference(subtyping,[status(esa)],[c_355])).

cnf(c_1739,plain,
    ( ~ m1_orders_2(X0_48,sK1,sK4)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,sK4,X0_48),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_2238,plain,
    ( ~ m1_orders_2(sK5,sK1,sK4)
    | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_2239,plain,
    ( k1_xboole_0 = sK4
    | m1_orders_2(sK5,sK1,sK4) != iProver_top
    | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2238])).

cnf(c_1038,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_1874,plain,
    ( X0_48 != X1_48
    | sK4 != X1_48
    | sK4 = X0_48 ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_2299,plain,
    ( X0_48 != sK4
    | sK4 = X0_48
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1874])).

cnf(c_2300,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2299])).

cnf(c_2608,plain,
    ( sK4 = k1_xboole_0
    | r2_orders_2(sK1,X0_48,sK0(sK1,sK4,sK5)) = iProver_top
    | r2_hidden(X0_48,sK5) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2451,c_31,c_32,c_36,c_1755,c_2239,c_2300])).

cnf(c_6,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X3,X1)
    | r2_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_534,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X3,X1)
    | r2_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_535,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X2,X0)
    | r2_orders_2(sK1,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_537,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X2,X0)
    | r2_orders_2(sK1,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_21,c_20])).

cnf(c_538,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X2,X0)
    | r2_orders_2(sK1,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_537])).

cnf(c_1017,plain,
    ( ~ r2_orders_2(sK1,X0_48,X1_48)
    | ~ r2_orders_2(sK1,X2_48,X0_48)
    | r2_orders_2(sK1,X2_48,X1_48)
    | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_48,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_538])).

cnf(c_1389,plain,
    ( r2_orders_2(sK1,X0_48,X1_48) != iProver_top
    | r2_orders_2(sK1,X2_48,X0_48) != iProver_top
    | r2_orders_2(sK1,X2_48,X1_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2_48,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1017])).

cnf(c_2618,plain,
    ( sK4 = k1_xboole_0
    | r2_orders_2(sK1,X0_48,X1_48) != iProver_top
    | r2_orders_2(sK1,X0_48,sK0(sK1,sK4,sK5)) = iProver_top
    | r2_hidden(X1_48,sK5) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2608,c_1389])).

cnf(c_3246,plain,
    ( m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X1_48,sK5) != iProver_top
    | r2_orders_2(sK1,X0_48,sK0(sK1,sK4,sK5)) = iProver_top
    | r2_orders_2(sK1,X0_48,X1_48) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2618,c_31,c_32,c_36,c_1755,c_2239,c_2300])).

cnf(c_3247,plain,
    ( sK4 = k1_xboole_0
    | r2_orders_2(sK1,X0_48,X1_48) != iProver_top
    | r2_orders_2(sK1,X0_48,sK0(sK1,sK4,sK5)) = iProver_top
    | r2_hidden(X1_48,sK5) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3246])).

cnf(c_3256,plain,
    ( sK4 = k1_xboole_0
    | r2_orders_2(sK1,sK2,sK0(sK1,sK4,sK5)) = iProver_top
    | r2_hidden(sK3,sK5) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1375,c_3247])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK3,sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_35,plain,
    ( r2_hidden(sK3,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3276,plain,
    ( r2_orders_2(sK1,sK2,sK0(sK1,sK4,sK5)) = iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3256,c_29,c_30,c_35])).

cnf(c_3277,plain,
    ( sK4 = k1_xboole_0
    | r2_orders_2(sK1,sK2,sK0(sK1,sK4,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3276])).

cnf(c_7,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X1,k3_orders_2(X0,X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_276,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X1,k3_orders_2(X0,X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_277,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_281,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_277,c_23,c_21,c_20,c_19])).

cnf(c_282,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_281])).

cnf(c_1025,plain,
    ( ~ r2_orders_2(sK1,X0_48,X1_48)
    | ~ r2_hidden(X0_48,X2_48)
    | r2_hidden(X0_48,k3_orders_2(sK1,X2_48,X1_48))
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_282])).

cnf(c_1381,plain,
    ( r2_orders_2(sK1,X0_48,X1_48) != iProver_top
    | r2_hidden(X0_48,X2_48) != iProver_top
    | r2_hidden(X0_48,k3_orders_2(sK1,X2_48,X1_48)) = iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1025])).

cnf(c_2450,plain,
    ( sK4 = k1_xboole_0
    | r2_orders_2(sK1,X0_48,sK0(sK1,sK4,sK5)) != iProver_top
    | r2_hidden(X0_48,sK4) != iProver_top
    | r2_hidden(X0_48,sK5) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2445,c_1381])).

cnf(c_2815,plain,
    ( sK4 = k1_xboole_0
    | r2_orders_2(sK1,X0_48,sK0(sK1,sK4,sK5)) != iProver_top
    | r2_hidden(X0_48,sK4) != iProver_top
    | r2_hidden(X0_48,sK5) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2450,c_31,c_32,c_36,c_1755,c_2239,c_2300])).

cnf(c_3284,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK2,sK5) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3277,c_2815])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_34,plain,
    ( r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,negated_conjecture,
    ( ~ r2_hidden(sK2,sK5) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_37,plain,
    ( r2_hidden(sK2,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3329,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3284,c_29,c_34,c_37])).

cnf(c_3339,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3329,c_1377])).

cnf(c_1,plain,
    ( ~ m1_orders_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_431,plain,
    ( ~ m1_orders_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_22])).

cnf(c_432,plain,
    ( ~ m1_orders_2(X0,sK1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_436,plain,
    ( ~ m1_orders_2(X0,sK1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_23,c_21,c_20,c_19])).

cnf(c_1019,plain,
    ( ~ m1_orders_2(X0_48,sK1,k1_xboole_0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0_48 ),
    inference(subtyping,[status(esa)],[c_436])).

cnf(c_1387,plain,
    ( k1_xboole_0 = X0_48
    | m1_orders_2(X0_48,sK1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1019])).

cnf(c_3415,plain,
    ( k1_xboole_0 = X0_48
    | m1_orders_2(X0_48,sK1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3339,c_1387])).

cnf(c_3556,plain,
    ( sK5 = k1_xboole_0
    | m1_orders_2(sK5,sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1376,c_3415])).

cnf(c_1050,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1037])).

cnf(c_1040,plain,
    ( ~ m1_subset_1(X0_48,X0_49)
    | m1_subset_1(X1_48,X0_49)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_1593,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_48 != sK4 ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_1595,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_1649,plain,
    ( ~ m1_orders_2(sK5,sK1,k1_xboole_0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1019])).

cnf(c_1675,plain,
    ( X0_48 != X1_48
    | X0_48 = sK4
    | sK4 != X1_48 ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_1676,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1675])).

cnf(c_1872,plain,
    ( X0_48 != X1_48
    | sK5 != X1_48
    | sK5 = X0_48 ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_2292,plain,
    ( X0_48 != sK5
    | sK5 = X0_48
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1872])).

cnf(c_2294,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2292])).

cnf(c_2293,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1037])).

cnf(c_1039,plain,
    ( ~ m1_orders_2(X0_48,X0_47,X1_48)
    | m1_orders_2(X2_48,X0_47,X3_48)
    | X2_48 != X0_48
    | X3_48 != X1_48 ),
    theory(equality)).

cnf(c_1622,plain,
    ( m1_orders_2(X0_48,sK1,X1_48)
    | ~ m1_orders_2(sK5,sK1,sK4)
    | X1_48 != sK4
    | X0_48 != sK5 ),
    inference(instantiation,[status(thm)],[c_1039])).

cnf(c_2682,plain,
    ( ~ m1_orders_2(sK5,sK1,sK4)
    | m1_orders_2(sK5,sK1,k1_xboole_0)
    | sK5 != sK5
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1622])).

cnf(c_3564,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3556,c_29,c_16,c_15,c_34,c_11,c_37,c_1050,c_1595,c_1649,c_1676,c_2294,c_2293,c_2682,c_3284])).

cnf(c_1035,negated_conjecture,
    ( ~ r2_hidden(sK2,sK5) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1371,plain,
    ( r2_hidden(sK2,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1035])).

cnf(c_3571,plain,
    ( r2_hidden(sK2,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3564,c_1371])).

cnf(c_1032,negated_conjecture,
    ( r2_hidden(sK2,sK4) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1374,plain,
    ( r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1032])).

cnf(c_3341,plain,
    ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3329,c_1374])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3571,c_3341])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.14/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.02  
% 2.14/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.14/1.02  
% 2.14/1.02  ------  iProver source info
% 2.14/1.02  
% 2.14/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.14/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.14/1.02  git: non_committed_changes: false
% 2.14/1.02  git: last_make_outside_of_git: false
% 2.14/1.02  
% 2.14/1.02  ------ 
% 2.14/1.02  
% 2.14/1.02  ------ Input Options
% 2.14/1.02  
% 2.14/1.02  --out_options                           all
% 2.14/1.02  --tptp_safe_out                         true
% 2.14/1.02  --problem_path                          ""
% 2.14/1.02  --include_path                          ""
% 2.14/1.02  --clausifier                            res/vclausify_rel
% 2.14/1.02  --clausifier_options                    --mode clausify
% 2.14/1.02  --stdin                                 false
% 2.14/1.02  --stats_out                             all
% 2.14/1.02  
% 2.14/1.02  ------ General Options
% 2.14/1.02  
% 2.14/1.02  --fof                                   false
% 2.14/1.02  --time_out_real                         305.
% 2.14/1.02  --time_out_virtual                      -1.
% 2.14/1.02  --symbol_type_check                     false
% 2.14/1.02  --clausify_out                          false
% 2.14/1.02  --sig_cnt_out                           false
% 2.14/1.02  --trig_cnt_out                          false
% 2.14/1.02  --trig_cnt_out_tolerance                1.
% 2.14/1.02  --trig_cnt_out_sk_spl                   false
% 2.14/1.02  --abstr_cl_out                          false
% 2.14/1.02  
% 2.14/1.02  ------ Global Options
% 2.14/1.02  
% 2.14/1.02  --schedule                              default
% 2.14/1.02  --add_important_lit                     false
% 2.14/1.02  --prop_solver_per_cl                    1000
% 2.14/1.02  --min_unsat_core                        false
% 2.14/1.02  --soft_assumptions                      false
% 2.14/1.02  --soft_lemma_size                       3
% 2.14/1.02  --prop_impl_unit_size                   0
% 2.14/1.02  --prop_impl_unit                        []
% 2.14/1.02  --share_sel_clauses                     true
% 2.14/1.02  --reset_solvers                         false
% 2.14/1.02  --bc_imp_inh                            [conj_cone]
% 2.14/1.02  --conj_cone_tolerance                   3.
% 2.14/1.02  --extra_neg_conj                        none
% 2.14/1.02  --large_theory_mode                     true
% 2.14/1.02  --prolific_symb_bound                   200
% 2.14/1.02  --lt_threshold                          2000
% 2.14/1.02  --clause_weak_htbl                      true
% 2.14/1.02  --gc_record_bc_elim                     false
% 2.14/1.02  
% 2.14/1.02  ------ Preprocessing Options
% 2.14/1.02  
% 2.14/1.02  --preprocessing_flag                    true
% 2.14/1.02  --time_out_prep_mult                    0.1
% 2.14/1.02  --splitting_mode                        input
% 2.14/1.02  --splitting_grd                         true
% 2.14/1.02  --splitting_cvd                         false
% 2.14/1.02  --splitting_cvd_svl                     false
% 2.14/1.02  --splitting_nvd                         32
% 2.14/1.02  --sub_typing                            true
% 2.14/1.02  --prep_gs_sim                           true
% 2.14/1.02  --prep_unflatten                        true
% 2.14/1.02  --prep_res_sim                          true
% 2.14/1.02  --prep_upred                            true
% 2.14/1.02  --prep_sem_filter                       exhaustive
% 2.14/1.02  --prep_sem_filter_out                   false
% 2.14/1.02  --pred_elim                             true
% 2.14/1.02  --res_sim_input                         true
% 2.14/1.02  --eq_ax_congr_red                       true
% 2.14/1.02  --pure_diseq_elim                       true
% 2.14/1.02  --brand_transform                       false
% 2.14/1.02  --non_eq_to_eq                          false
% 2.14/1.02  --prep_def_merge                        true
% 2.14/1.02  --prep_def_merge_prop_impl              false
% 2.14/1.02  --prep_def_merge_mbd                    true
% 2.14/1.02  --prep_def_merge_tr_red                 false
% 2.14/1.02  --prep_def_merge_tr_cl                  false
% 2.14/1.02  --smt_preprocessing                     true
% 2.14/1.02  --smt_ac_axioms                         fast
% 2.14/1.02  --preprocessed_out                      false
% 2.14/1.02  --preprocessed_stats                    false
% 2.14/1.02  
% 2.14/1.02  ------ Abstraction refinement Options
% 2.14/1.02  
% 2.14/1.02  --abstr_ref                             []
% 2.14/1.02  --abstr_ref_prep                        false
% 2.14/1.02  --abstr_ref_until_sat                   false
% 2.14/1.02  --abstr_ref_sig_restrict                funpre
% 2.14/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.14/1.02  --abstr_ref_under                       []
% 2.14/1.02  
% 2.14/1.02  ------ SAT Options
% 2.14/1.02  
% 2.14/1.02  --sat_mode                              false
% 2.14/1.02  --sat_fm_restart_options                ""
% 2.14/1.02  --sat_gr_def                            false
% 2.14/1.02  --sat_epr_types                         true
% 2.14/1.02  --sat_non_cyclic_types                  false
% 2.14/1.02  --sat_finite_models                     false
% 2.14/1.02  --sat_fm_lemmas                         false
% 2.14/1.02  --sat_fm_prep                           false
% 2.14/1.02  --sat_fm_uc_incr                        true
% 2.14/1.02  --sat_out_model                         small
% 2.14/1.02  --sat_out_clauses                       false
% 2.14/1.02  
% 2.14/1.02  ------ QBF Options
% 2.14/1.02  
% 2.14/1.02  --qbf_mode                              false
% 2.14/1.02  --qbf_elim_univ                         false
% 2.14/1.02  --qbf_dom_inst                          none
% 2.14/1.02  --qbf_dom_pre_inst                      false
% 2.14/1.02  --qbf_sk_in                             false
% 2.14/1.02  --qbf_pred_elim                         true
% 2.14/1.02  --qbf_split                             512
% 2.14/1.02  
% 2.14/1.02  ------ BMC1 Options
% 2.14/1.02  
% 2.14/1.02  --bmc1_incremental                      false
% 2.14/1.02  --bmc1_axioms                           reachable_all
% 2.14/1.02  --bmc1_min_bound                        0
% 2.14/1.02  --bmc1_max_bound                        -1
% 2.14/1.02  --bmc1_max_bound_default                -1
% 2.14/1.02  --bmc1_symbol_reachability              true
% 2.14/1.02  --bmc1_property_lemmas                  false
% 2.14/1.02  --bmc1_k_induction                      false
% 2.14/1.02  --bmc1_non_equiv_states                 false
% 2.14/1.02  --bmc1_deadlock                         false
% 2.14/1.02  --bmc1_ucm                              false
% 2.14/1.02  --bmc1_add_unsat_core                   none
% 2.14/1.02  --bmc1_unsat_core_children              false
% 2.14/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.14/1.02  --bmc1_out_stat                         full
% 2.14/1.02  --bmc1_ground_init                      false
% 2.14/1.02  --bmc1_pre_inst_next_state              false
% 2.14/1.02  --bmc1_pre_inst_state                   false
% 2.14/1.02  --bmc1_pre_inst_reach_state             false
% 2.14/1.02  --bmc1_out_unsat_core                   false
% 2.14/1.02  --bmc1_aig_witness_out                  false
% 2.14/1.02  --bmc1_verbose                          false
% 2.14/1.02  --bmc1_dump_clauses_tptp                false
% 2.14/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.14/1.02  --bmc1_dump_file                        -
% 2.14/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.14/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.14/1.02  --bmc1_ucm_extend_mode                  1
% 2.14/1.02  --bmc1_ucm_init_mode                    2
% 2.14/1.02  --bmc1_ucm_cone_mode                    none
% 2.14/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.14/1.02  --bmc1_ucm_relax_model                  4
% 2.14/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.14/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.14/1.02  --bmc1_ucm_layered_model                none
% 2.14/1.02  --bmc1_ucm_max_lemma_size               10
% 2.14/1.02  
% 2.14/1.02  ------ AIG Options
% 2.14/1.02  
% 2.14/1.02  --aig_mode                              false
% 2.14/1.02  
% 2.14/1.02  ------ Instantiation Options
% 2.14/1.02  
% 2.14/1.02  --instantiation_flag                    true
% 2.14/1.02  --inst_sos_flag                         false
% 2.14/1.02  --inst_sos_phase                        true
% 2.14/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.14/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.14/1.02  --inst_lit_sel_side                     num_symb
% 2.14/1.02  --inst_solver_per_active                1400
% 2.14/1.02  --inst_solver_calls_frac                1.
% 2.14/1.02  --inst_passive_queue_type               priority_queues
% 2.14/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.14/1.02  --inst_passive_queues_freq              [25;2]
% 2.14/1.02  --inst_dismatching                      true
% 2.14/1.02  --inst_eager_unprocessed_to_passive     true
% 2.14/1.02  --inst_prop_sim_given                   true
% 2.14/1.02  --inst_prop_sim_new                     false
% 2.14/1.02  --inst_subs_new                         false
% 2.14/1.02  --inst_eq_res_simp                      false
% 2.14/1.02  --inst_subs_given                       false
% 2.14/1.02  --inst_orphan_elimination               true
% 2.14/1.02  --inst_learning_loop_flag               true
% 2.14/1.02  --inst_learning_start                   3000
% 2.14/1.02  --inst_learning_factor                  2
% 2.14/1.02  --inst_start_prop_sim_after_learn       3
% 2.14/1.02  --inst_sel_renew                        solver
% 2.14/1.02  --inst_lit_activity_flag                true
% 2.14/1.02  --inst_restr_to_given                   false
% 2.14/1.02  --inst_activity_threshold               500
% 2.14/1.02  --inst_out_proof                        true
% 2.14/1.02  
% 2.14/1.02  ------ Resolution Options
% 2.14/1.02  
% 2.14/1.02  --resolution_flag                       true
% 2.14/1.02  --res_lit_sel                           adaptive
% 2.14/1.02  --res_lit_sel_side                      none
% 2.14/1.02  --res_ordering                          kbo
% 2.14/1.02  --res_to_prop_solver                    active
% 2.14/1.02  --res_prop_simpl_new                    false
% 2.14/1.02  --res_prop_simpl_given                  true
% 2.14/1.02  --res_passive_queue_type                priority_queues
% 2.14/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.14/1.02  --res_passive_queues_freq               [15;5]
% 2.14/1.02  --res_forward_subs                      full
% 2.14/1.02  --res_backward_subs                     full
% 2.14/1.02  --res_forward_subs_resolution           true
% 2.14/1.02  --res_backward_subs_resolution          true
% 2.14/1.02  --res_orphan_elimination                true
% 2.14/1.02  --res_time_limit                        2.
% 2.14/1.02  --res_out_proof                         true
% 2.14/1.02  
% 2.14/1.02  ------ Superposition Options
% 2.14/1.02  
% 2.14/1.02  --superposition_flag                    true
% 2.14/1.02  --sup_passive_queue_type                priority_queues
% 2.14/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.14/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.14/1.02  --demod_completeness_check              fast
% 2.14/1.02  --demod_use_ground                      true
% 2.14/1.02  --sup_to_prop_solver                    passive
% 2.14/1.02  --sup_prop_simpl_new                    true
% 2.14/1.02  --sup_prop_simpl_given                  true
% 2.14/1.02  --sup_fun_splitting                     false
% 2.14/1.02  --sup_smt_interval                      50000
% 2.14/1.02  
% 2.14/1.02  ------ Superposition Simplification Setup
% 2.14/1.02  
% 2.14/1.02  --sup_indices_passive                   []
% 2.14/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.14/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.02  --sup_full_bw                           [BwDemod]
% 2.14/1.02  --sup_immed_triv                        [TrivRules]
% 2.14/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.14/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.02  --sup_immed_bw_main                     []
% 2.14/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.14/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/1.02  
% 2.14/1.02  ------ Combination Options
% 2.14/1.02  
% 2.14/1.02  --comb_res_mult                         3
% 2.14/1.02  --comb_sup_mult                         2
% 2.14/1.02  --comb_inst_mult                        10
% 2.14/1.02  
% 2.14/1.02  ------ Debug Options
% 2.14/1.02  
% 2.14/1.02  --dbg_backtrace                         false
% 2.14/1.02  --dbg_dump_prop_clauses                 false
% 2.14/1.02  --dbg_dump_prop_clauses_file            -
% 2.14/1.02  --dbg_out_stat                          false
% 2.14/1.02  ------ Parsing...
% 2.14/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.14/1.02  
% 2.14/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.14/1.02  
% 2.14/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.14/1.02  
% 2.14/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.14/1.02  ------ Proving...
% 2.14/1.02  ------ Problem Properties 
% 2.14/1.02  
% 2.14/1.02  
% 2.14/1.02  clauses                                 19
% 2.14/1.02  conjectures                             9
% 2.14/1.02  EPR                                     5
% 2.14/1.02  Horn                                    15
% 2.14/1.02  unary                                   9
% 2.14/1.02  binary                                  1
% 2.14/1.02  lits                                    58
% 2.14/1.02  lits eq                                 6
% 2.14/1.02  fd_pure                                 0
% 2.14/1.02  fd_pseudo                               0
% 2.14/1.02  fd_cond                                 4
% 2.14/1.02  fd_pseudo_cond                          0
% 2.14/1.02  AC symbols                              0
% 2.14/1.02  
% 2.14/1.02  ------ Schedule dynamic 5 is on 
% 2.14/1.02  
% 2.14/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.14/1.02  
% 2.14/1.02  
% 2.14/1.02  ------ 
% 2.14/1.02  Current options:
% 2.14/1.02  ------ 
% 2.14/1.02  
% 2.14/1.02  ------ Input Options
% 2.14/1.02  
% 2.14/1.02  --out_options                           all
% 2.14/1.02  --tptp_safe_out                         true
% 2.14/1.02  --problem_path                          ""
% 2.14/1.02  --include_path                          ""
% 2.14/1.02  --clausifier                            res/vclausify_rel
% 2.14/1.02  --clausifier_options                    --mode clausify
% 2.14/1.02  --stdin                                 false
% 2.14/1.02  --stats_out                             all
% 2.14/1.02  
% 2.14/1.02  ------ General Options
% 2.14/1.02  
% 2.14/1.02  --fof                                   false
% 2.14/1.02  --time_out_real                         305.
% 2.14/1.02  --time_out_virtual                      -1.
% 2.14/1.02  --symbol_type_check                     false
% 2.14/1.02  --clausify_out                          false
% 2.14/1.02  --sig_cnt_out                           false
% 2.14/1.02  --trig_cnt_out                          false
% 2.14/1.02  --trig_cnt_out_tolerance                1.
% 2.14/1.02  --trig_cnt_out_sk_spl                   false
% 2.14/1.02  --abstr_cl_out                          false
% 2.14/1.02  
% 2.14/1.02  ------ Global Options
% 2.14/1.02  
% 2.14/1.02  --schedule                              default
% 2.14/1.02  --add_important_lit                     false
% 2.14/1.02  --prop_solver_per_cl                    1000
% 2.14/1.02  --min_unsat_core                        false
% 2.14/1.02  --soft_assumptions                      false
% 2.14/1.02  --soft_lemma_size                       3
% 2.14/1.02  --prop_impl_unit_size                   0
% 2.14/1.02  --prop_impl_unit                        []
% 2.14/1.02  --share_sel_clauses                     true
% 2.14/1.02  --reset_solvers                         false
% 2.14/1.02  --bc_imp_inh                            [conj_cone]
% 2.14/1.02  --conj_cone_tolerance                   3.
% 2.14/1.02  --extra_neg_conj                        none
% 2.14/1.02  --large_theory_mode                     true
% 2.14/1.02  --prolific_symb_bound                   200
% 2.14/1.02  --lt_threshold                          2000
% 2.14/1.02  --clause_weak_htbl                      true
% 2.14/1.02  --gc_record_bc_elim                     false
% 2.14/1.02  
% 2.14/1.02  ------ Preprocessing Options
% 2.14/1.02  
% 2.14/1.02  --preprocessing_flag                    true
% 2.14/1.02  --time_out_prep_mult                    0.1
% 2.14/1.02  --splitting_mode                        input
% 2.14/1.02  --splitting_grd                         true
% 2.14/1.02  --splitting_cvd                         false
% 2.14/1.02  --splitting_cvd_svl                     false
% 2.14/1.02  --splitting_nvd                         32
% 2.14/1.02  --sub_typing                            true
% 2.14/1.02  --prep_gs_sim                           true
% 2.14/1.02  --prep_unflatten                        true
% 2.14/1.02  --prep_res_sim                          true
% 2.14/1.02  --prep_upred                            true
% 2.14/1.02  --prep_sem_filter                       exhaustive
% 2.14/1.02  --prep_sem_filter_out                   false
% 2.14/1.02  --pred_elim                             true
% 2.14/1.02  --res_sim_input                         true
% 2.14/1.02  --eq_ax_congr_red                       true
% 2.14/1.02  --pure_diseq_elim                       true
% 2.14/1.02  --brand_transform                       false
% 2.14/1.02  --non_eq_to_eq                          false
% 2.14/1.02  --prep_def_merge                        true
% 2.14/1.02  --prep_def_merge_prop_impl              false
% 2.14/1.02  --prep_def_merge_mbd                    true
% 2.14/1.02  --prep_def_merge_tr_red                 false
% 2.14/1.02  --prep_def_merge_tr_cl                  false
% 2.14/1.02  --smt_preprocessing                     true
% 2.14/1.02  --smt_ac_axioms                         fast
% 2.14/1.02  --preprocessed_out                      false
% 2.14/1.02  --preprocessed_stats                    false
% 2.14/1.02  
% 2.14/1.02  ------ Abstraction refinement Options
% 2.14/1.02  
% 2.14/1.02  --abstr_ref                             []
% 2.14/1.02  --abstr_ref_prep                        false
% 2.14/1.02  --abstr_ref_until_sat                   false
% 2.14/1.02  --abstr_ref_sig_restrict                funpre
% 2.14/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.14/1.02  --abstr_ref_under                       []
% 2.14/1.02  
% 2.14/1.02  ------ SAT Options
% 2.14/1.02  
% 2.14/1.02  --sat_mode                              false
% 2.14/1.02  --sat_fm_restart_options                ""
% 2.14/1.02  --sat_gr_def                            false
% 2.14/1.02  --sat_epr_types                         true
% 2.14/1.02  --sat_non_cyclic_types                  false
% 2.14/1.02  --sat_finite_models                     false
% 2.14/1.02  --sat_fm_lemmas                         false
% 2.14/1.02  --sat_fm_prep                           false
% 2.14/1.02  --sat_fm_uc_incr                        true
% 2.14/1.02  --sat_out_model                         small
% 2.14/1.02  --sat_out_clauses                       false
% 2.14/1.02  
% 2.14/1.02  ------ QBF Options
% 2.14/1.02  
% 2.14/1.02  --qbf_mode                              false
% 2.14/1.02  --qbf_elim_univ                         false
% 2.14/1.02  --qbf_dom_inst                          none
% 2.14/1.02  --qbf_dom_pre_inst                      false
% 2.14/1.02  --qbf_sk_in                             false
% 2.14/1.02  --qbf_pred_elim                         true
% 2.14/1.02  --qbf_split                             512
% 2.14/1.02  
% 2.14/1.02  ------ BMC1 Options
% 2.14/1.02  
% 2.14/1.02  --bmc1_incremental                      false
% 2.14/1.02  --bmc1_axioms                           reachable_all
% 2.14/1.02  --bmc1_min_bound                        0
% 2.14/1.02  --bmc1_max_bound                        -1
% 2.14/1.02  --bmc1_max_bound_default                -1
% 2.14/1.02  --bmc1_symbol_reachability              true
% 2.14/1.02  --bmc1_property_lemmas                  false
% 2.14/1.02  --bmc1_k_induction                      false
% 2.14/1.02  --bmc1_non_equiv_states                 false
% 2.14/1.02  --bmc1_deadlock                         false
% 2.14/1.02  --bmc1_ucm                              false
% 2.14/1.02  --bmc1_add_unsat_core                   none
% 2.14/1.02  --bmc1_unsat_core_children              false
% 2.14/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.14/1.02  --bmc1_out_stat                         full
% 2.14/1.02  --bmc1_ground_init                      false
% 2.14/1.02  --bmc1_pre_inst_next_state              false
% 2.14/1.02  --bmc1_pre_inst_state                   false
% 2.14/1.02  --bmc1_pre_inst_reach_state             false
% 2.14/1.02  --bmc1_out_unsat_core                   false
% 2.14/1.02  --bmc1_aig_witness_out                  false
% 2.14/1.02  --bmc1_verbose                          false
% 2.14/1.02  --bmc1_dump_clauses_tptp                false
% 2.14/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.14/1.02  --bmc1_dump_file                        -
% 2.14/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.14/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.14/1.02  --bmc1_ucm_extend_mode                  1
% 2.14/1.02  --bmc1_ucm_init_mode                    2
% 2.14/1.02  --bmc1_ucm_cone_mode                    none
% 2.14/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.14/1.02  --bmc1_ucm_relax_model                  4
% 2.14/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.14/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.14/1.02  --bmc1_ucm_layered_model                none
% 2.14/1.02  --bmc1_ucm_max_lemma_size               10
% 2.14/1.02  
% 2.14/1.02  ------ AIG Options
% 2.14/1.02  
% 2.14/1.02  --aig_mode                              false
% 2.14/1.02  
% 2.14/1.02  ------ Instantiation Options
% 2.14/1.02  
% 2.14/1.02  --instantiation_flag                    true
% 2.14/1.02  --inst_sos_flag                         false
% 2.14/1.02  --inst_sos_phase                        true
% 2.14/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.14/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.14/1.02  --inst_lit_sel_side                     none
% 2.14/1.02  --inst_solver_per_active                1400
% 2.14/1.02  --inst_solver_calls_frac                1.
% 2.14/1.02  --inst_passive_queue_type               priority_queues
% 2.14/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.14/1.02  --inst_passive_queues_freq              [25;2]
% 2.14/1.02  --inst_dismatching                      true
% 2.14/1.02  --inst_eager_unprocessed_to_passive     true
% 2.14/1.02  --inst_prop_sim_given                   true
% 2.14/1.02  --inst_prop_sim_new                     false
% 2.14/1.02  --inst_subs_new                         false
% 2.14/1.02  --inst_eq_res_simp                      false
% 2.14/1.02  --inst_subs_given                       false
% 2.14/1.02  --inst_orphan_elimination               true
% 2.14/1.02  --inst_learning_loop_flag               true
% 2.14/1.02  --inst_learning_start                   3000
% 2.14/1.02  --inst_learning_factor                  2
% 2.14/1.02  --inst_start_prop_sim_after_learn       3
% 2.14/1.02  --inst_sel_renew                        solver
% 2.14/1.02  --inst_lit_activity_flag                true
% 2.14/1.02  --inst_restr_to_given                   false
% 2.14/1.02  --inst_activity_threshold               500
% 2.14/1.02  --inst_out_proof                        true
% 2.14/1.02  
% 2.14/1.02  ------ Resolution Options
% 2.14/1.02  
% 2.14/1.02  --resolution_flag                       false
% 2.14/1.02  --res_lit_sel                           adaptive
% 2.14/1.02  --res_lit_sel_side                      none
% 2.14/1.02  --res_ordering                          kbo
% 2.14/1.02  --res_to_prop_solver                    active
% 2.14/1.02  --res_prop_simpl_new                    false
% 2.14/1.02  --res_prop_simpl_given                  true
% 2.14/1.02  --res_passive_queue_type                priority_queues
% 2.14/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.14/1.02  --res_passive_queues_freq               [15;5]
% 2.14/1.02  --res_forward_subs                      full
% 2.14/1.02  --res_backward_subs                     full
% 2.14/1.02  --res_forward_subs_resolution           true
% 2.14/1.02  --res_backward_subs_resolution          true
% 2.14/1.02  --res_orphan_elimination                true
% 2.14/1.02  --res_time_limit                        2.
% 2.14/1.02  --res_out_proof                         true
% 2.14/1.02  
% 2.14/1.02  ------ Superposition Options
% 2.14/1.02  
% 2.14/1.02  --superposition_flag                    true
% 2.14/1.02  --sup_passive_queue_type                priority_queues
% 2.14/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.14/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.14/1.02  --demod_completeness_check              fast
% 2.14/1.02  --demod_use_ground                      true
% 2.14/1.02  --sup_to_prop_solver                    passive
% 2.14/1.02  --sup_prop_simpl_new                    true
% 2.14/1.02  --sup_prop_simpl_given                  true
% 2.14/1.02  --sup_fun_splitting                     false
% 2.14/1.02  --sup_smt_interval                      50000
% 2.14/1.02  
% 2.14/1.02  ------ Superposition Simplification Setup
% 2.14/1.02  
% 2.14/1.02  --sup_indices_passive                   []
% 2.14/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.14/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.02  --sup_full_bw                           [BwDemod]
% 2.14/1.02  --sup_immed_triv                        [TrivRules]
% 2.14/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.14/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.02  --sup_immed_bw_main                     []
% 2.14/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.14/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/1.02  
% 2.14/1.02  ------ Combination Options
% 2.14/1.02  
% 2.14/1.02  --comb_res_mult                         3
% 2.14/1.02  --comb_sup_mult                         2
% 2.14/1.02  --comb_inst_mult                        10
% 2.14/1.02  
% 2.14/1.02  ------ Debug Options
% 2.14/1.02  
% 2.14/1.02  --dbg_backtrace                         false
% 2.14/1.02  --dbg_dump_prop_clauses                 false
% 2.14/1.02  --dbg_dump_prop_clauses_file            -
% 2.14/1.02  --dbg_out_stat                          false
% 2.14/1.02  
% 2.14/1.02  
% 2.14/1.02  
% 2.14/1.02  
% 2.14/1.02  ------ Proving...
% 2.14/1.02  
% 2.14/1.02  
% 2.14/1.02  % SZS status Theorem for theBenchmark.p
% 2.14/1.02  
% 2.14/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.14/1.02  
% 2.14/1.02  fof(f4,conjecture,(
% 2.14/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 2.14/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.02  
% 2.14/1.02  fof(f5,negated_conjecture,(
% 2.14/1.02    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 2.14/1.02    inference(negated_conjecture,[],[f4])).
% 2.14/1.02  
% 2.14/1.02  fof(f12,plain,(
% 2.14/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_hidden(X1,X4) & (m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.14/1.02    inference(ennf_transformation,[],[f5])).
% 2.14/1.02  
% 2.14/1.02  fof(f13,plain,(
% 2.14/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.14/1.02    inference(flattening,[],[f12])).
% 2.14/1.02  
% 2.14/1.02  fof(f24,plain,(
% 2.14/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(X1,sK5) & m1_orders_2(sK5,X0,X3) & r2_hidden(X2,sK5) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.14/1.02    introduced(choice_axiom,[])).
% 2.14/1.02  
% 2.14/1.02  fof(f23,plain,(
% 2.14/1.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,sK4) & r2_hidden(X2,X4) & r2_hidden(X1,sK4) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.14/1.02    introduced(choice_axiom,[])).
% 2.14/1.02  
% 2.14/1.02  fof(f22,plain,(
% 2.14/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(sK3,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,sK3) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.14/1.02    introduced(choice_axiom,[])).
% 2.14/1.02  
% 2.14/1.02  fof(f21,plain,(
% 2.14/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(sK2,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(sK2,X3) & r2_orders_2(X0,sK2,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.14/1.02    introduced(choice_axiom,[])).
% 2.14/1.02  
% 2.14/1.02  fof(f20,plain,(
% 2.14/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,sK1,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(sK1,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 2.14/1.02    introduced(choice_axiom,[])).
% 2.14/1.02  
% 2.14/1.02  fof(f25,plain,(
% 2.14/1.02    ((((~r2_hidden(sK2,sK5) & m1_orders_2(sK5,sK1,sK4) & r2_hidden(sK3,sK5) & r2_hidden(sK2,sK4) & r2_orders_2(sK1,sK2,sK3) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 2.14/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f13,f24,f23,f22,f21,f20])).
% 2.14/1.02  
% 2.14/1.02  fof(f44,plain,(
% 2.14/1.02    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.14/1.02    inference(cnf_transformation,[],[f25])).
% 2.14/1.02  
% 2.14/1.02  fof(f45,plain,(
% 2.14/1.02    r2_orders_2(sK1,sK2,sK3)),
% 2.14/1.02    inference(cnf_transformation,[],[f25])).
% 2.14/1.02  
% 2.14/1.02  fof(f43,plain,(
% 2.14/1.02    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.14/1.02    inference(cnf_transformation,[],[f25])).
% 2.14/1.02  
% 2.14/1.02  fof(f1,axiom,(
% 2.14/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 2.14/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.02  
% 2.14/1.02  fof(f6,plain,(
% 2.14/1.02    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.14/1.02    inference(ennf_transformation,[],[f1])).
% 2.14/1.02  
% 2.14/1.02  fof(f7,plain,(
% 2.14/1.02    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.14/1.02    inference(flattening,[],[f6])).
% 2.14/1.02  
% 2.14/1.02  fof(f14,plain,(
% 2.14/1.02    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.14/1.02    inference(nnf_transformation,[],[f7])).
% 2.14/1.02  
% 2.14/1.02  fof(f15,plain,(
% 2.14/1.02    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.14/1.02    inference(rectify,[],[f14])).
% 2.14/1.02  
% 2.14/1.02  fof(f16,plain,(
% 2.14/1.02    ! [X2,X1,X0] : (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2 & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 2.14/1.02    introduced(choice_axiom,[])).
% 2.14/1.02  
% 2.14/1.02  fof(f17,plain,(
% 2.14/1.02    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2 & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.14/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 2.14/1.02  
% 2.14/1.02  fof(f28,plain,(
% 2.14/1.02    ( ! [X2,X0,X1] : (k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.14/1.02    inference(cnf_transformation,[],[f17])).
% 2.14/1.02  
% 2.14/1.02  fof(f37,plain,(
% 2.14/1.02    v3_orders_2(sK1)),
% 2.14/1.02    inference(cnf_transformation,[],[f25])).
% 2.14/1.02  
% 2.14/1.02  fof(f36,plain,(
% 2.14/1.02    ~v2_struct_0(sK1)),
% 2.14/1.02    inference(cnf_transformation,[],[f25])).
% 2.14/1.02  
% 2.14/1.02  fof(f38,plain,(
% 2.14/1.02    v4_orders_2(sK1)),
% 2.14/1.02    inference(cnf_transformation,[],[f25])).
% 2.14/1.02  
% 2.14/1.02  fof(f39,plain,(
% 2.14/1.02    v5_orders_2(sK1)),
% 2.14/1.02    inference(cnf_transformation,[],[f25])).
% 2.14/1.02  
% 2.14/1.02  fof(f40,plain,(
% 2.14/1.02    l1_orders_2(sK1)),
% 2.14/1.02    inference(cnf_transformation,[],[f25])).
% 2.14/1.02  
% 2.14/1.02  fof(f48,plain,(
% 2.14/1.02    m1_orders_2(sK5,sK1,sK4)),
% 2.14/1.02    inference(cnf_transformation,[],[f25])).
% 2.14/1.02  
% 2.14/1.02  fof(f3,axiom,(
% 2.14/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 2.14/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.02  
% 2.14/1.02  fof(f10,plain,(
% 2.14/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.14/1.02    inference(ennf_transformation,[],[f3])).
% 2.14/1.02  
% 2.14/1.02  fof(f11,plain,(
% 2.14/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.14/1.02    inference(flattening,[],[f10])).
% 2.14/1.02  
% 2.14/1.02  fof(f18,plain,(
% 2.14/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.14/1.02    inference(nnf_transformation,[],[f11])).
% 2.14/1.02  
% 2.14/1.02  fof(f19,plain,(
% 2.14/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.14/1.02    inference(flattening,[],[f18])).
% 2.14/1.02  
% 2.14/1.02  fof(f33,plain,(
% 2.14/1.02    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.14/1.02    inference(cnf_transformation,[],[f19])).
% 2.14/1.02  
% 2.14/1.02  fof(f26,plain,(
% 2.14/1.02    ( ! [X2,X0,X1] : (m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.14/1.02    inference(cnf_transformation,[],[f17])).
% 2.14/1.02  
% 2.14/1.02  fof(f2,axiom,(
% 2.14/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2)) => r2_orders_2(X0,X1,X3))))))),
% 2.14/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.02  
% 2.14/1.02  fof(f8,plain,(
% 2.14/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_orders_2(X0,X1,X3) | (~r2_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)))),
% 2.14/1.02    inference(ennf_transformation,[],[f2])).
% 2.14/1.02  
% 2.14/1.02  fof(f9,plain,(
% 2.14/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_orders_2(X0,X1,X3) | ~r2_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0))),
% 2.14/1.02    inference(flattening,[],[f8])).
% 2.14/1.02  
% 2.14/1.02  fof(f32,plain,(
% 2.14/1.02    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X3) | ~r2_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)) )),
% 2.14/1.02    inference(cnf_transformation,[],[f9])).
% 2.14/1.02  
% 2.14/1.02  fof(f41,plain,(
% 2.14/1.02    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.14/1.02    inference(cnf_transformation,[],[f25])).
% 2.14/1.02  
% 2.14/1.02  fof(f42,plain,(
% 2.14/1.02    m1_subset_1(sK3,u1_struct_0(sK1))),
% 2.14/1.02    inference(cnf_transformation,[],[f25])).
% 2.14/1.02  
% 2.14/1.02  fof(f47,plain,(
% 2.14/1.02    r2_hidden(sK3,sK5)),
% 2.14/1.02    inference(cnf_transformation,[],[f25])).
% 2.14/1.02  
% 2.14/1.02  fof(f35,plain,(
% 2.14/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.14/1.02    inference(cnf_transformation,[],[f19])).
% 2.14/1.02  
% 2.14/1.02  fof(f46,plain,(
% 2.14/1.02    r2_hidden(sK2,sK4)),
% 2.14/1.02    inference(cnf_transformation,[],[f25])).
% 2.14/1.02  
% 2.14/1.02  fof(f49,plain,(
% 2.14/1.02    ~r2_hidden(sK2,sK5)),
% 2.14/1.02    inference(cnf_transformation,[],[f25])).
% 2.14/1.02  
% 2.14/1.02  fof(f30,plain,(
% 2.14/1.02    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.14/1.02    inference(cnf_transformation,[],[f17])).
% 2.14/1.02  
% 2.14/1.02  fof(f52,plain,(
% 2.14/1.02    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.14/1.02    inference(equality_resolution,[],[f30])).
% 2.14/1.02  
% 2.14/1.02  cnf(c_15,negated_conjecture,
% 2.14/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.14/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1030,negated_conjecture,
% 2.14/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.14/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1376,plain,
% 2.14/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_1030]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_14,negated_conjecture,
% 2.14/1.02      ( r2_orders_2(sK1,sK2,sK3) ),
% 2.14/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1031,negated_conjecture,
% 2.14/1.02      ( r2_orders_2(sK1,sK2,sK3) ),
% 2.14/1.02      inference(subtyping,[status(esa)],[c_14]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1375,plain,
% 2.14/1.02      ( r2_orders_2(sK1,sK2,sK3) = iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_1031]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_16,negated_conjecture,
% 2.14/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.14/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1029,negated_conjecture,
% 2.14/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.14/1.02      inference(subtyping,[status(esa)],[c_16]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1377,plain,
% 2.14/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_1029]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_3,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0,X1,X2)
% 2.14/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.02      | v2_struct_0(X1)
% 2.14/1.02      | ~ v3_orders_2(X1)
% 2.14/1.02      | ~ v4_orders_2(X1)
% 2.14/1.02      | ~ v5_orders_2(X1)
% 2.14/1.02      | ~ l1_orders_2(X1)
% 2.14/1.02      | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
% 2.14/1.02      | k1_xboole_0 = X2 ),
% 2.14/1.02      inference(cnf_transformation,[],[f28]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_22,negated_conjecture,
% 2.14/1.02      ( v3_orders_2(sK1) ),
% 2.14/1.02      inference(cnf_transformation,[],[f37]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_404,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0,X1,X2)
% 2.14/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.02      | v2_struct_0(X1)
% 2.14/1.02      | ~ v4_orders_2(X1)
% 2.14/1.02      | ~ v5_orders_2(X1)
% 2.14/1.02      | ~ l1_orders_2(X1)
% 2.14/1.02      | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
% 2.14/1.02      | sK1 != X1
% 2.14/1.02      | k1_xboole_0 = X2 ),
% 2.14/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_405,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0,sK1,X1)
% 2.14/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | v2_struct_0(sK1)
% 2.14/1.02      | ~ v4_orders_2(sK1)
% 2.14/1.02      | ~ v5_orders_2(sK1)
% 2.14/1.02      | ~ l1_orders_2(sK1)
% 2.14/1.02      | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
% 2.14/1.02      | k1_xboole_0 = X1 ),
% 2.14/1.02      inference(unflattening,[status(thm)],[c_404]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_23,negated_conjecture,
% 2.14/1.02      ( ~ v2_struct_0(sK1) ),
% 2.14/1.02      inference(cnf_transformation,[],[f36]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_21,negated_conjecture,
% 2.14/1.02      ( v4_orders_2(sK1) ),
% 2.14/1.02      inference(cnf_transformation,[],[f38]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_20,negated_conjecture,
% 2.14/1.02      ( v5_orders_2(sK1) ),
% 2.14/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_19,negated_conjecture,
% 2.14/1.02      ( l1_orders_2(sK1) ),
% 2.14/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_409,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0,sK1,X1)
% 2.14/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
% 2.14/1.02      | k1_xboole_0 = X1 ),
% 2.14/1.02      inference(global_propositional_subsumption,
% 2.14/1.02                [status(thm)],
% 2.14/1.02                [c_405,c_23,c_21,c_20,c_19]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1020,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0_48,sK1,X1_48)
% 2.14/1.02      | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | k3_orders_2(sK1,X1_48,sK0(sK1,X1_48,X0_48)) = X0_48
% 2.14/1.02      | k1_xboole_0 = X1_48 ),
% 2.14/1.02      inference(subtyping,[status(esa)],[c_409]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1386,plain,
% 2.14/1.02      ( k3_orders_2(sK1,X0_48,sK0(sK1,X0_48,X1_48)) = X1_48
% 2.14/1.02      | k1_xboole_0 = X0_48
% 2.14/1.02      | m1_orders_2(X1_48,sK1,X0_48) != iProver_top
% 2.14/1.02      | m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.14/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_1020]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2257,plain,
% 2.14/1.02      ( k3_orders_2(sK1,sK4,sK0(sK1,sK4,X0_48)) = X0_48
% 2.14/1.02      | sK4 = k1_xboole_0
% 2.14/1.02      | m1_orders_2(X0_48,sK1,sK4) != iProver_top
% 2.14/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.14/1.02      inference(superposition,[status(thm)],[c_1377,c_1386]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2427,plain,
% 2.14/1.02      ( k3_orders_2(sK1,sK4,sK0(sK1,sK4,sK5)) = sK5
% 2.14/1.02      | sK4 = k1_xboole_0
% 2.14/1.02      | m1_orders_2(sK5,sK1,sK4) != iProver_top ),
% 2.14/1.02      inference(superposition,[status(thm)],[c_1376,c_2257]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_11,negated_conjecture,
% 2.14/1.02      ( m1_orders_2(sK5,sK1,sK4) ),
% 2.14/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_36,plain,
% 2.14/1.02      ( m1_orders_2(sK5,sK1,sK4) = iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2444,plain,
% 2.14/1.02      ( sK4 = k1_xboole_0 | k3_orders_2(sK1,sK4,sK0(sK1,sK4,sK5)) = sK5 ),
% 2.14/1.02      inference(global_propositional_subsumption,
% 2.14/1.02                [status(thm)],
% 2.14/1.02                [c_2427,c_36]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2445,plain,
% 2.14/1.02      ( k3_orders_2(sK1,sK4,sK0(sK1,sK4,sK5)) = sK5 | sK4 = k1_xboole_0 ),
% 2.14/1.02      inference(renaming,[status(thm)],[c_2444]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_9,plain,
% 2.14/1.02      ( r2_orders_2(X0,X1,X2)
% 2.14/1.02      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 2.14/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.14/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.14/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.14/1.02      | v2_struct_0(X0)
% 2.14/1.02      | ~ v3_orders_2(X0)
% 2.14/1.02      | ~ v4_orders_2(X0)
% 2.14/1.02      | ~ v5_orders_2(X0)
% 2.14/1.02      | ~ l1_orders_2(X0) ),
% 2.14/1.02      inference(cnf_transformation,[],[f33]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_249,plain,
% 2.14/1.02      ( r2_orders_2(X0,X1,X2)
% 2.14/1.02      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 2.14/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.14/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.14/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.14/1.02      | v2_struct_0(X0)
% 2.14/1.02      | ~ v4_orders_2(X0)
% 2.14/1.02      | ~ v5_orders_2(X0)
% 2.14/1.02      | ~ l1_orders_2(X0)
% 2.14/1.02      | sK1 != X0 ),
% 2.14/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_250,plain,
% 2.14/1.02      ( r2_orders_2(sK1,X0,X1)
% 2.14/1.02      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.14/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.14/1.02      | v2_struct_0(sK1)
% 2.14/1.02      | ~ v4_orders_2(sK1)
% 2.14/1.02      | ~ v5_orders_2(sK1)
% 2.14/1.02      | ~ l1_orders_2(sK1) ),
% 2.14/1.02      inference(unflattening,[status(thm)],[c_249]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_254,plain,
% 2.14/1.02      ( r2_orders_2(sK1,X0,X1)
% 2.14/1.02      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.14/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 2.14/1.02      inference(global_propositional_subsumption,
% 2.14/1.02                [status(thm)],
% 2.14/1.02                [c_250,c_23,c_21,c_20,c_19]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_255,plain,
% 2.14/1.02      ( r2_orders_2(sK1,X0,X1)
% 2.14/1.02      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.14/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.14/1.02      inference(renaming,[status(thm)],[c_254]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1026,plain,
% 2.14/1.02      ( r2_orders_2(sK1,X0_48,X1_48)
% 2.14/1.02      | ~ r2_hidden(X0_48,k3_orders_2(sK1,X2_48,X1_48))
% 2.14/1.02      | ~ m1_subset_1(X2_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(X0_48,u1_struct_0(sK1)) ),
% 2.14/1.02      inference(subtyping,[status(esa)],[c_255]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1380,plain,
% 2.14/1.02      ( r2_orders_2(sK1,X0_48,X1_48) = iProver_top
% 2.14/1.02      | r2_hidden(X0_48,k3_orders_2(sK1,X2_48,X1_48)) != iProver_top
% 2.14/1.02      | m1_subset_1(X2_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.14/1.02      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 2.14/1.02      | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_1026]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2451,plain,
% 2.14/1.02      ( sK4 = k1_xboole_0
% 2.14/1.02      | r2_orders_2(sK1,X0_48,sK0(sK1,sK4,sK5)) = iProver_top
% 2.14/1.02      | r2_hidden(X0_48,sK5) != iProver_top
% 2.14/1.02      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 2.14/1.02      | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1)) != iProver_top
% 2.14/1.02      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.14/1.02      inference(superposition,[status(thm)],[c_2445,c_1380]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_31,plain,
% 2.14/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_32,plain,
% 2.14/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1037,plain,( X0_48 = X0_48 ),theory(equality) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1755,plain,
% 2.14/1.02      ( sK4 = sK4 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_1037]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_5,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0,X1,X2)
% 2.14/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.02      | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
% 2.14/1.02      | v2_struct_0(X1)
% 2.14/1.02      | ~ v3_orders_2(X1)
% 2.14/1.02      | ~ v4_orders_2(X1)
% 2.14/1.02      | ~ v5_orders_2(X1)
% 2.14/1.02      | ~ l1_orders_2(X1)
% 2.14/1.02      | k1_xboole_0 = X2 ),
% 2.14/1.02      inference(cnf_transformation,[],[f26]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_350,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0,X1,X2)
% 2.14/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.02      | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
% 2.14/1.02      | v2_struct_0(X1)
% 2.14/1.02      | ~ v4_orders_2(X1)
% 2.14/1.02      | ~ v5_orders_2(X1)
% 2.14/1.02      | ~ l1_orders_2(X1)
% 2.14/1.02      | sK1 != X1
% 2.14/1.02      | k1_xboole_0 = X2 ),
% 2.14/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_22]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_351,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0,sK1,X1)
% 2.14/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
% 2.14/1.02      | v2_struct_0(sK1)
% 2.14/1.02      | ~ v4_orders_2(sK1)
% 2.14/1.02      | ~ v5_orders_2(sK1)
% 2.14/1.02      | ~ l1_orders_2(sK1)
% 2.14/1.02      | k1_xboole_0 = X1 ),
% 2.14/1.02      inference(unflattening,[status(thm)],[c_350]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_355,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0,sK1,X1)
% 2.14/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
% 2.14/1.02      | k1_xboole_0 = X1 ),
% 2.14/1.02      inference(global_propositional_subsumption,
% 2.14/1.02                [status(thm)],
% 2.14/1.02                [c_351,c_23,c_21,c_20,c_19]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1022,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0_48,sK1,X1_48)
% 2.14/1.02      | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | m1_subset_1(sK0(sK1,X1_48,X0_48),u1_struct_0(sK1))
% 2.14/1.02      | k1_xboole_0 = X1_48 ),
% 2.14/1.02      inference(subtyping,[status(esa)],[c_355]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1739,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0_48,sK1,sK4)
% 2.14/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | m1_subset_1(sK0(sK1,sK4,X0_48),u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | k1_xboole_0 = sK4 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_1022]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2238,plain,
% 2.14/1.02      ( ~ m1_orders_2(sK5,sK1,sK4)
% 2.14/1.02      | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | k1_xboole_0 = sK4 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_1739]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2239,plain,
% 2.14/1.02      ( k1_xboole_0 = sK4
% 2.14/1.02      | m1_orders_2(sK5,sK1,sK4) != iProver_top
% 2.14/1.02      | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1)) = iProver_top
% 2.14/1.02      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.14/1.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_2238]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1038,plain,
% 2.14/1.02      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 2.14/1.02      theory(equality) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1874,plain,
% 2.14/1.02      ( X0_48 != X1_48 | sK4 != X1_48 | sK4 = X0_48 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_1038]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2299,plain,
% 2.14/1.02      ( X0_48 != sK4 | sK4 = X0_48 | sK4 != sK4 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_1874]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2300,plain,
% 2.14/1.02      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_2299]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2608,plain,
% 2.14/1.02      ( sK4 = k1_xboole_0
% 2.14/1.02      | r2_orders_2(sK1,X0_48,sK0(sK1,sK4,sK5)) = iProver_top
% 2.14/1.02      | r2_hidden(X0_48,sK5) != iProver_top
% 2.14/1.02      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top ),
% 2.14/1.02      inference(global_propositional_subsumption,
% 2.14/1.02                [status(thm)],
% 2.14/1.02                [c_2451,c_31,c_32,c_36,c_1755,c_2239,c_2300]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_6,plain,
% 2.14/1.02      ( ~ r2_orders_2(X0,X1,X2)
% 2.14/1.02      | ~ r2_orders_2(X0,X3,X1)
% 2.14/1.02      | r2_orders_2(X0,X3,X2)
% 2.14/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.14/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.14/1.02      | ~ v4_orders_2(X0)
% 2.14/1.02      | ~ v5_orders_2(X0)
% 2.14/1.02      | ~ l1_orders_2(X0) ),
% 2.14/1.02      inference(cnf_transformation,[],[f32]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_534,plain,
% 2.14/1.02      ( ~ r2_orders_2(X0,X1,X2)
% 2.14/1.02      | ~ r2_orders_2(X0,X3,X1)
% 2.14/1.02      | r2_orders_2(X0,X3,X2)
% 2.14/1.02      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.14/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.14/1.02      | ~ v4_orders_2(X0)
% 2.14/1.02      | ~ v5_orders_2(X0)
% 2.14/1.02      | sK1 != X0 ),
% 2.14/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_19]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_535,plain,
% 2.14/1.02      ( ~ r2_orders_2(sK1,X0,X1)
% 2.14/1.02      | ~ r2_orders_2(sK1,X2,X0)
% 2.14/1.02      | r2_orders_2(sK1,X2,X1)
% 2.14/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.14/1.02      | ~ v4_orders_2(sK1)
% 2.14/1.02      | ~ v5_orders_2(sK1) ),
% 2.14/1.02      inference(unflattening,[status(thm)],[c_534]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_537,plain,
% 2.14/1.02      ( ~ r2_orders_2(sK1,X0,X1)
% 2.14/1.02      | ~ r2_orders_2(sK1,X2,X0)
% 2.14/1.02      | r2_orders_2(sK1,X2,X1)
% 2.14/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ),
% 2.14/1.02      inference(global_propositional_subsumption,
% 2.14/1.02                [status(thm)],
% 2.14/1.02                [c_535,c_21,c_20]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_538,plain,
% 2.14/1.02      ( ~ r2_orders_2(sK1,X0,X1)
% 2.14/1.02      | ~ r2_orders_2(sK1,X2,X0)
% 2.14/1.02      | r2_orders_2(sK1,X2,X1)
% 2.14/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.14/1.02      inference(renaming,[status(thm)],[c_537]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1017,plain,
% 2.14/1.02      ( ~ r2_orders_2(sK1,X0_48,X1_48)
% 2.14/1.02      | ~ r2_orders_2(sK1,X2_48,X0_48)
% 2.14/1.02      | r2_orders_2(sK1,X2_48,X1_48)
% 2.14/1.02      | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(X2_48,u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(X0_48,u1_struct_0(sK1)) ),
% 2.14/1.02      inference(subtyping,[status(esa)],[c_538]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1389,plain,
% 2.14/1.02      ( r2_orders_2(sK1,X0_48,X1_48) != iProver_top
% 2.14/1.02      | r2_orders_2(sK1,X2_48,X0_48) != iProver_top
% 2.14/1.02      | r2_orders_2(sK1,X2_48,X1_48) = iProver_top
% 2.14/1.02      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 2.14/1.02      | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top
% 2.14/1.02      | m1_subset_1(X2_48,u1_struct_0(sK1)) != iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_1017]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2618,plain,
% 2.14/1.02      ( sK4 = k1_xboole_0
% 2.14/1.02      | r2_orders_2(sK1,X0_48,X1_48) != iProver_top
% 2.14/1.02      | r2_orders_2(sK1,X0_48,sK0(sK1,sK4,sK5)) = iProver_top
% 2.14/1.02      | r2_hidden(X1_48,sK5) != iProver_top
% 2.14/1.02      | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top
% 2.14/1.02      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 2.14/1.02      | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1)) != iProver_top ),
% 2.14/1.02      inference(superposition,[status(thm)],[c_2608,c_1389]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_3246,plain,
% 2.14/1.02      ( m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 2.14/1.02      | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top
% 2.14/1.02      | r2_hidden(X1_48,sK5) != iProver_top
% 2.14/1.02      | r2_orders_2(sK1,X0_48,sK0(sK1,sK4,sK5)) = iProver_top
% 2.14/1.02      | r2_orders_2(sK1,X0_48,X1_48) != iProver_top
% 2.14/1.02      | sK4 = k1_xboole_0 ),
% 2.14/1.02      inference(global_propositional_subsumption,
% 2.14/1.02                [status(thm)],
% 2.14/1.02                [c_2618,c_31,c_32,c_36,c_1755,c_2239,c_2300]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_3247,plain,
% 2.14/1.02      ( sK4 = k1_xboole_0
% 2.14/1.02      | r2_orders_2(sK1,X0_48,X1_48) != iProver_top
% 2.14/1.02      | r2_orders_2(sK1,X0_48,sK0(sK1,sK4,sK5)) = iProver_top
% 2.14/1.02      | r2_hidden(X1_48,sK5) != iProver_top
% 2.14/1.02      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 2.14/1.02      | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top ),
% 2.14/1.02      inference(renaming,[status(thm)],[c_3246]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_3256,plain,
% 2.14/1.02      ( sK4 = k1_xboole_0
% 2.14/1.02      | r2_orders_2(sK1,sK2,sK0(sK1,sK4,sK5)) = iProver_top
% 2.14/1.02      | r2_hidden(sK3,sK5) != iProver_top
% 2.14/1.02      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.14/1.02      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.14/1.02      inference(superposition,[status(thm)],[c_1375,c_3247]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_18,negated_conjecture,
% 2.14/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.14/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_29,plain,
% 2.14/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_17,negated_conjecture,
% 2.14/1.02      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.14/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_30,plain,
% 2.14/1.02      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_12,negated_conjecture,
% 2.14/1.02      ( r2_hidden(sK3,sK5) ),
% 2.14/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_35,plain,
% 2.14/1.02      ( r2_hidden(sK3,sK5) = iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_3276,plain,
% 2.14/1.02      ( r2_orders_2(sK1,sK2,sK0(sK1,sK4,sK5)) = iProver_top
% 2.14/1.02      | sK4 = k1_xboole_0 ),
% 2.14/1.02      inference(global_propositional_subsumption,
% 2.14/1.02                [status(thm)],
% 2.14/1.02                [c_3256,c_29,c_30,c_35]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_3277,plain,
% 2.14/1.02      ( sK4 = k1_xboole_0
% 2.14/1.02      | r2_orders_2(sK1,sK2,sK0(sK1,sK4,sK5)) = iProver_top ),
% 2.14/1.02      inference(renaming,[status(thm)],[c_3276]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_7,plain,
% 2.14/1.02      ( ~ r2_orders_2(X0,X1,X2)
% 2.14/1.02      | ~ r2_hidden(X1,X3)
% 2.14/1.02      | r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 2.14/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.14/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.14/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.14/1.02      | v2_struct_0(X0)
% 2.14/1.02      | ~ v3_orders_2(X0)
% 2.14/1.02      | ~ v4_orders_2(X0)
% 2.14/1.02      | ~ v5_orders_2(X0)
% 2.14/1.02      | ~ l1_orders_2(X0) ),
% 2.14/1.02      inference(cnf_transformation,[],[f35]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_276,plain,
% 2.14/1.02      ( ~ r2_orders_2(X0,X1,X2)
% 2.14/1.02      | ~ r2_hidden(X1,X3)
% 2.14/1.02      | r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 2.14/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.14/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.14/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.14/1.02      | v2_struct_0(X0)
% 2.14/1.02      | ~ v4_orders_2(X0)
% 2.14/1.02      | ~ v5_orders_2(X0)
% 2.14/1.02      | ~ l1_orders_2(X0)
% 2.14/1.02      | sK1 != X0 ),
% 2.14/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_277,plain,
% 2.14/1.02      ( ~ r2_orders_2(sK1,X0,X1)
% 2.14/1.02      | ~ r2_hidden(X0,X2)
% 2.14/1.02      | r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.14/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.14/1.02      | v2_struct_0(sK1)
% 2.14/1.02      | ~ v4_orders_2(sK1)
% 2.14/1.02      | ~ v5_orders_2(sK1)
% 2.14/1.02      | ~ l1_orders_2(sK1) ),
% 2.14/1.02      inference(unflattening,[status(thm)],[c_276]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_281,plain,
% 2.14/1.02      ( ~ r2_orders_2(sK1,X0,X1)
% 2.14/1.02      | ~ r2_hidden(X0,X2)
% 2.14/1.02      | r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.14/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 2.14/1.02      inference(global_propositional_subsumption,
% 2.14/1.02                [status(thm)],
% 2.14/1.02                [c_277,c_23,c_21,c_20,c_19]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_282,plain,
% 2.14/1.02      ( ~ r2_orders_2(sK1,X0,X1)
% 2.14/1.02      | ~ r2_hidden(X0,X2)
% 2.14/1.02      | r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.14/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.14/1.02      inference(renaming,[status(thm)],[c_281]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1025,plain,
% 2.14/1.02      ( ~ r2_orders_2(sK1,X0_48,X1_48)
% 2.14/1.02      | ~ r2_hidden(X0_48,X2_48)
% 2.14/1.02      | r2_hidden(X0_48,k3_orders_2(sK1,X2_48,X1_48))
% 2.14/1.02      | ~ m1_subset_1(X2_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
% 2.14/1.02      | ~ m1_subset_1(X0_48,u1_struct_0(sK1)) ),
% 2.14/1.02      inference(subtyping,[status(esa)],[c_282]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1381,plain,
% 2.14/1.02      ( r2_orders_2(sK1,X0_48,X1_48) != iProver_top
% 2.14/1.02      | r2_hidden(X0_48,X2_48) != iProver_top
% 2.14/1.02      | r2_hidden(X0_48,k3_orders_2(sK1,X2_48,X1_48)) = iProver_top
% 2.14/1.02      | m1_subset_1(X2_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.14/1.02      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 2.14/1.02      | m1_subset_1(X1_48,u1_struct_0(sK1)) != iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_1025]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2450,plain,
% 2.14/1.02      ( sK4 = k1_xboole_0
% 2.14/1.02      | r2_orders_2(sK1,X0_48,sK0(sK1,sK4,sK5)) != iProver_top
% 2.14/1.02      | r2_hidden(X0_48,sK4) != iProver_top
% 2.14/1.02      | r2_hidden(X0_48,sK5) = iProver_top
% 2.14/1.02      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top
% 2.14/1.02      | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1)) != iProver_top
% 2.14/1.02      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.14/1.02      inference(superposition,[status(thm)],[c_2445,c_1381]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2815,plain,
% 2.14/1.02      ( sK4 = k1_xboole_0
% 2.14/1.02      | r2_orders_2(sK1,X0_48,sK0(sK1,sK4,sK5)) != iProver_top
% 2.14/1.02      | r2_hidden(X0_48,sK4) != iProver_top
% 2.14/1.02      | r2_hidden(X0_48,sK5) = iProver_top
% 2.14/1.02      | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top ),
% 2.14/1.02      inference(global_propositional_subsumption,
% 2.14/1.02                [status(thm)],
% 2.14/1.02                [c_2450,c_31,c_32,c_36,c_1755,c_2239,c_2300]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_3284,plain,
% 2.14/1.02      ( sK4 = k1_xboole_0
% 2.14/1.02      | r2_hidden(sK2,sK4) != iProver_top
% 2.14/1.02      | r2_hidden(sK2,sK5) = iProver_top
% 2.14/1.02      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.14/1.02      inference(superposition,[status(thm)],[c_3277,c_2815]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_13,negated_conjecture,
% 2.14/1.02      ( r2_hidden(sK2,sK4) ),
% 2.14/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_34,plain,
% 2.14/1.02      ( r2_hidden(sK2,sK4) = iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_10,negated_conjecture,
% 2.14/1.02      ( ~ r2_hidden(sK2,sK5) ),
% 2.14/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_37,plain,
% 2.14/1.02      ( r2_hidden(sK2,sK5) != iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_3329,plain,
% 2.14/1.02      ( sK4 = k1_xboole_0 ),
% 2.14/1.02      inference(global_propositional_subsumption,
% 2.14/1.02                [status(thm)],
% 2.14/1.02                [c_3284,c_29,c_34,c_37]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_3339,plain,
% 2.14/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.14/1.02      inference(demodulation,[status(thm)],[c_3329,c_1377]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0,X1,k1_xboole_0)
% 2.14/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.02      | v2_struct_0(X1)
% 2.14/1.02      | ~ v3_orders_2(X1)
% 2.14/1.02      | ~ v4_orders_2(X1)
% 2.14/1.02      | ~ v5_orders_2(X1)
% 2.14/1.02      | ~ l1_orders_2(X1)
% 2.14/1.02      | k1_xboole_0 = X0 ),
% 2.14/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_431,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0,X1,k1_xboole_0)
% 2.14/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.02      | v2_struct_0(X1)
% 2.14/1.02      | ~ v4_orders_2(X1)
% 2.14/1.02      | ~ v5_orders_2(X1)
% 2.14/1.02      | ~ l1_orders_2(X1)
% 2.14/1.02      | sK1 != X1
% 2.14/1.02      | k1_xboole_0 = X0 ),
% 2.14/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_22]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_432,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0,sK1,k1_xboole_0)
% 2.14/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | v2_struct_0(sK1)
% 2.14/1.02      | ~ v4_orders_2(sK1)
% 2.14/1.02      | ~ v5_orders_2(sK1)
% 2.14/1.02      | ~ l1_orders_2(sK1)
% 2.14/1.02      | k1_xboole_0 = X0 ),
% 2.14/1.02      inference(unflattening,[status(thm)],[c_431]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_436,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0,sK1,k1_xboole_0)
% 2.14/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | k1_xboole_0 = X0 ),
% 2.14/1.02      inference(global_propositional_subsumption,
% 2.14/1.02                [status(thm)],
% 2.14/1.02                [c_432,c_23,c_21,c_20,c_19]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1019,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0_48,sK1,k1_xboole_0)
% 2.14/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | k1_xboole_0 = X0_48 ),
% 2.14/1.02      inference(subtyping,[status(esa)],[c_436]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1387,plain,
% 2.14/1.02      ( k1_xboole_0 = X0_48
% 2.14/1.02      | m1_orders_2(X0_48,sK1,k1_xboole_0) != iProver_top
% 2.14/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.14/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_1019]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_3415,plain,
% 2.14/1.02      ( k1_xboole_0 = X0_48
% 2.14/1.02      | m1_orders_2(X0_48,sK1,k1_xboole_0) != iProver_top
% 2.14/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.14/1.02      inference(superposition,[status(thm)],[c_3339,c_1387]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_3556,plain,
% 2.14/1.02      ( sK5 = k1_xboole_0
% 2.14/1.02      | m1_orders_2(sK5,sK1,k1_xboole_0) != iProver_top ),
% 2.14/1.02      inference(superposition,[status(thm)],[c_1376,c_3415]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1050,plain,
% 2.14/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_1037]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1040,plain,
% 2.14/1.02      ( ~ m1_subset_1(X0_48,X0_49)
% 2.14/1.02      | m1_subset_1(X1_48,X0_49)
% 2.14/1.02      | X1_48 != X0_48 ),
% 2.14/1.02      theory(equality) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1593,plain,
% 2.14/1.02      ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | X0_48 != sK4 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_1040]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1595,plain,
% 2.14/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | k1_xboole_0 != sK4 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_1593]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1649,plain,
% 2.14/1.02      ( ~ m1_orders_2(sK5,sK1,k1_xboole_0)
% 2.14/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.02      | k1_xboole_0 = sK5 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_1019]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1675,plain,
% 2.14/1.02      ( X0_48 != X1_48 | X0_48 = sK4 | sK4 != X1_48 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_1038]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1676,plain,
% 2.14/1.02      ( sK4 != k1_xboole_0
% 2.14/1.02      | k1_xboole_0 = sK4
% 2.14/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_1675]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1872,plain,
% 2.14/1.02      ( X0_48 != X1_48 | sK5 != X1_48 | sK5 = X0_48 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_1038]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2292,plain,
% 2.14/1.02      ( X0_48 != sK5 | sK5 = X0_48 | sK5 != sK5 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_1872]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2294,plain,
% 2.14/1.02      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_2292]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2293,plain,
% 2.14/1.02      ( sK5 = sK5 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_1037]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1039,plain,
% 2.14/1.02      ( ~ m1_orders_2(X0_48,X0_47,X1_48)
% 2.14/1.02      | m1_orders_2(X2_48,X0_47,X3_48)
% 2.14/1.02      | X2_48 != X0_48
% 2.14/1.02      | X3_48 != X1_48 ),
% 2.14/1.02      theory(equality) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1622,plain,
% 2.14/1.02      ( m1_orders_2(X0_48,sK1,X1_48)
% 2.14/1.02      | ~ m1_orders_2(sK5,sK1,sK4)
% 2.14/1.02      | X1_48 != sK4
% 2.14/1.02      | X0_48 != sK5 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_1039]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_2682,plain,
% 2.14/1.02      ( ~ m1_orders_2(sK5,sK1,sK4)
% 2.14/1.02      | m1_orders_2(sK5,sK1,k1_xboole_0)
% 2.14/1.02      | sK5 != sK5
% 2.14/1.02      | k1_xboole_0 != sK4 ),
% 2.14/1.02      inference(instantiation,[status(thm)],[c_1622]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_3564,plain,
% 2.14/1.02      ( sK5 = k1_xboole_0 ),
% 2.14/1.02      inference(global_propositional_subsumption,
% 2.14/1.02                [status(thm)],
% 2.14/1.02                [c_3556,c_29,c_16,c_15,c_34,c_11,c_37,c_1050,c_1595,
% 2.14/1.02                 c_1649,c_1676,c_2294,c_2293,c_2682,c_3284]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1035,negated_conjecture,
% 2.14/1.02      ( ~ r2_hidden(sK2,sK5) ),
% 2.14/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1371,plain,
% 2.14/1.02      ( r2_hidden(sK2,sK5) != iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_1035]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_3571,plain,
% 2.14/1.02      ( r2_hidden(sK2,k1_xboole_0) != iProver_top ),
% 2.14/1.02      inference(demodulation,[status(thm)],[c_3564,c_1371]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1032,negated_conjecture,
% 2.14/1.02      ( r2_hidden(sK2,sK4) ),
% 2.14/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_1374,plain,
% 2.14/1.02      ( r2_hidden(sK2,sK4) = iProver_top ),
% 2.14/1.02      inference(predicate_to_equality,[status(thm)],[c_1032]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(c_3341,plain,
% 2.14/1.02      ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 2.14/1.02      inference(demodulation,[status(thm)],[c_3329,c_1374]) ).
% 2.14/1.02  
% 2.14/1.02  cnf(contradiction,plain,
% 2.14/1.02      ( $false ),
% 2.14/1.02      inference(minisat,[status(thm)],[c_3571,c_3341]) ).
% 2.14/1.02  
% 2.14/1.02  
% 2.14/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.14/1.02  
% 2.14/1.02  ------                               Statistics
% 2.14/1.02  
% 2.14/1.02  ------ General
% 2.14/1.02  
% 2.14/1.02  abstr_ref_over_cycles:                  0
% 2.14/1.02  abstr_ref_under_cycles:                 0
% 2.14/1.02  gc_basic_clause_elim:                   0
% 2.14/1.02  forced_gc_time:                         0
% 2.14/1.02  parsing_time:                           0.022
% 2.14/1.02  unif_index_cands_time:                  0.
% 2.14/1.02  unif_index_add_time:                    0.
% 2.14/1.02  orderings_time:                         0.
% 2.14/1.02  out_proof_time:                         0.012
% 2.14/1.02  total_time:                             0.187
% 2.14/1.02  num_of_symbols:                         50
% 2.14/1.02  num_of_terms:                           2465
% 2.14/1.02  
% 2.14/1.02  ------ Preprocessing
% 2.14/1.02  
% 2.14/1.02  num_of_splits:                          0
% 2.14/1.02  num_of_split_atoms:                     0
% 2.14/1.02  num_of_reused_defs:                     0
% 2.14/1.02  num_eq_ax_congr_red:                    18
% 2.14/1.02  num_of_sem_filtered_clauses:            1
% 2.14/1.02  num_of_subtypes:                        3
% 2.14/1.02  monotx_restored_types:                  0
% 2.14/1.02  sat_num_of_epr_types:                   0
% 2.14/1.02  sat_num_of_non_cyclic_types:            0
% 2.14/1.02  sat_guarded_non_collapsed_types:        1
% 2.14/1.02  num_pure_diseq_elim:                    0
% 2.14/1.02  simp_replaced_by:                       0
% 2.14/1.02  res_preprocessed:                       96
% 2.14/1.02  prep_upred:                             0
% 2.14/1.02  prep_unflattend:                        54
% 2.14/1.02  smt_new_axioms:                         0
% 2.14/1.02  pred_elim_cands:                        4
% 2.14/1.02  pred_elim:                              5
% 2.14/1.02  pred_elim_cl:                           5
% 2.14/1.02  pred_elim_cycles:                       7
% 2.14/1.02  merged_defs:                            0
% 2.14/1.02  merged_defs_ncl:                        0
% 2.14/1.02  bin_hyper_res:                          0
% 2.14/1.02  prep_cycles:                            4
% 2.14/1.02  pred_elim_time:                         0.022
% 2.14/1.02  splitting_time:                         0.
% 2.14/1.02  sem_filter_time:                        0.
% 2.14/1.02  monotx_time:                            0.
% 2.14/1.02  subtype_inf_time:                       0.
% 2.14/1.02  
% 2.14/1.02  ------ Problem properties
% 2.14/1.02  
% 2.14/1.02  clauses:                                19
% 2.14/1.02  conjectures:                            9
% 2.14/1.02  epr:                                    5
% 2.14/1.02  horn:                                   15
% 2.14/1.02  ground:                                 10
% 2.14/1.02  unary:                                  9
% 2.14/1.02  binary:                                 1
% 2.14/1.02  lits:                                   58
% 2.14/1.02  lits_eq:                                6
% 2.14/1.02  fd_pure:                                0
% 2.14/1.02  fd_pseudo:                              0
% 2.14/1.02  fd_cond:                                4
% 2.14/1.02  fd_pseudo_cond:                         0
% 2.14/1.02  ac_symbols:                             0
% 2.14/1.02  
% 2.14/1.02  ------ Propositional Solver
% 2.14/1.02  
% 2.14/1.02  prop_solver_calls:                      28
% 2.14/1.02  prop_fast_solver_calls:                 1124
% 2.14/1.02  smt_solver_calls:                       0
% 2.14/1.02  smt_fast_solver_calls:                  0
% 2.14/1.02  prop_num_of_clauses:                    1015
% 2.14/1.02  prop_preprocess_simplified:             3436
% 2.14/1.02  prop_fo_subsumed:                       79
% 2.14/1.02  prop_solver_time:                       0.
% 2.14/1.02  smt_solver_time:                        0.
% 2.14/1.02  smt_fast_solver_time:                   0.
% 2.14/1.02  prop_fast_solver_time:                  0.
% 2.14/1.02  prop_unsat_core_time:                   0.
% 2.14/1.02  
% 2.14/1.02  ------ QBF
% 2.14/1.02  
% 2.14/1.02  qbf_q_res:                              0
% 2.14/1.02  qbf_num_tautologies:                    0
% 2.14/1.02  qbf_prep_cycles:                        0
% 2.14/1.02  
% 2.14/1.02  ------ BMC1
% 2.14/1.02  
% 2.14/1.02  bmc1_current_bound:                     -1
% 2.14/1.02  bmc1_last_solved_bound:                 -1
% 2.14/1.02  bmc1_unsat_core_size:                   -1
% 2.14/1.02  bmc1_unsat_core_parents_size:           -1
% 2.14/1.02  bmc1_merge_next_fun:                    0
% 2.14/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.14/1.02  
% 2.14/1.02  ------ Instantiation
% 2.14/1.02  
% 2.14/1.02  inst_num_of_clauses:                    245
% 2.14/1.02  inst_num_in_passive:                    45
% 2.14/1.02  inst_num_in_active:                     193
% 2.14/1.02  inst_num_in_unprocessed:                7
% 2.14/1.02  inst_num_of_loops:                      250
% 2.14/1.02  inst_num_of_learning_restarts:          0
% 2.14/1.02  inst_num_moves_active_passive:          53
% 2.14/1.02  inst_lit_activity:                      0
% 2.14/1.02  inst_lit_activity_moves:                0
% 2.14/1.02  inst_num_tautologies:                   0
% 2.14/1.02  inst_num_prop_implied:                  0
% 2.14/1.02  inst_num_existing_simplified:           0
% 2.14/1.02  inst_num_eq_res_simplified:             0
% 2.14/1.02  inst_num_child_elim:                    0
% 2.14/1.02  inst_num_of_dismatching_blockings:      33
% 2.14/1.02  inst_num_of_non_proper_insts:           246
% 2.14/1.02  inst_num_of_duplicates:                 0
% 2.14/1.02  inst_inst_num_from_inst_to_res:         0
% 2.14/1.02  inst_dismatching_checking_time:         0.
% 2.14/1.02  
% 2.14/1.02  ------ Resolution
% 2.14/1.02  
% 2.14/1.02  res_num_of_clauses:                     0
% 2.14/1.02  res_num_in_passive:                     0
% 2.14/1.02  res_num_in_active:                      0
% 2.14/1.02  res_num_of_loops:                       100
% 2.14/1.02  res_forward_subset_subsumed:            34
% 2.14/1.02  res_backward_subset_subsumed:           0
% 2.14/1.02  res_forward_subsumed:                   0
% 2.14/1.02  res_backward_subsumed:                  0
% 2.14/1.02  res_forward_subsumption_resolution:     0
% 2.14/1.02  res_backward_subsumption_resolution:    0
% 2.14/1.02  res_clause_to_clause_subsumption:       149
% 2.14/1.02  res_orphan_elimination:                 0
% 2.14/1.02  res_tautology_del:                      27
% 2.14/1.02  res_num_eq_res_simplified:              0
% 2.14/1.02  res_num_sel_changes:                    0
% 2.14/1.02  res_moves_from_active_to_pass:          0
% 2.14/1.02  
% 2.14/1.02  ------ Superposition
% 2.14/1.02  
% 2.14/1.02  sup_time_total:                         0.
% 2.14/1.02  sup_time_generating:                    0.
% 2.14/1.02  sup_time_sim_full:                      0.
% 2.14/1.02  sup_time_sim_immed:                     0.
% 2.14/1.02  
% 2.14/1.02  sup_num_of_clauses:                     29
% 2.14/1.02  sup_num_in_active:                      21
% 2.14/1.02  sup_num_in_passive:                     8
% 2.14/1.02  sup_num_of_loops:                       49
% 2.14/1.02  sup_fw_superposition:                   28
% 2.14/1.02  sup_bw_superposition:                   17
% 2.14/1.02  sup_immediate_simplified:               5
% 2.14/1.02  sup_given_eliminated:                   1
% 2.14/1.02  comparisons_done:                       0
% 2.14/1.02  comparisons_avoided:                    13
% 2.14/1.02  
% 2.14/1.02  ------ Simplifications
% 2.14/1.02  
% 2.14/1.02  
% 2.14/1.02  sim_fw_subset_subsumed:                 4
% 2.14/1.02  sim_bw_subset_subsumed:                 13
% 2.14/1.02  sim_fw_subsumed:                        1
% 2.14/1.02  sim_bw_subsumed:                        2
% 2.14/1.02  sim_fw_subsumption_res:                 0
% 2.14/1.02  sim_bw_subsumption_res:                 0
% 2.14/1.02  sim_tautology_del:                      3
% 2.14/1.02  sim_eq_tautology_del:                   9
% 2.14/1.02  sim_eq_res_simp:                        0
% 2.14/1.02  sim_fw_demodulated:                     0
% 2.14/1.02  sim_bw_demodulated:                     16
% 2.14/1.02  sim_light_normalised:                   0
% 2.14/1.02  sim_joinable_taut:                      0
% 2.14/1.02  sim_joinable_simp:                      0
% 2.14/1.02  sim_ac_normalised:                      0
% 2.14/1.02  sim_smt_subsumption:                    0
% 2.14/1.02  
%------------------------------------------------------------------------------
