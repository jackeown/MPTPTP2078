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
% DateTime   : Thu Dec  3 12:12:41 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  163 (1228 expanded)
%              Number of clauses        :  112 ( 269 expanded)
%              Number of leaves         :   16 ( 522 expanded)
%              Depth                    :   25
%              Number of atoms          :  955 (14696 expanded)
%              Number of equality atoms :  228 ( 597 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   28 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
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

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f28,plain,(
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

fof(f27,plain,(
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

fof(f26,plain,(
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

fof(f25,plain,(
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

fof(f24,plain,
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

fof(f29,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f15,f28,f27,f26,f25,f24])).

fof(f53,plain,(
    r2_orders_2(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
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

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    m1_orders_2(sK5,sK1,sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
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
                 => ( ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ( ( ~ r2_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ( ( ~ r2_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    r2_hidden(sK3,sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ~ r2_hidden(sK2,sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f37,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
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
    inference(equality_resolution,[],[f37])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f23])).

cnf(c_18,negated_conjecture,
    ( r2_orders_2(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1139,negated_conjecture,
    ( r2_orders_2(sK1,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1499,plain,
    ( r2_orders_2(sK1,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1138,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1500,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1138])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1137,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1501,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1137])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f35])).

cnf(c_26,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_489,plain,
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
    inference(resolution_lifted,[status(thm)],[c_6,c_26])).

cnf(c_490,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_25,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_23,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_494,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_490,c_27,c_25,c_24,c_23])).

cnf(c_1128,plain,
    ( ~ m1_orders_2(X0_49,sK1,X1_49)
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,X1_49,sK0(sK1,X1_49,X0_49)) = X0_49
    | k1_xboole_0 = X1_49 ),
    inference(subtyping,[status(esa)],[c_494])).

cnf(c_1510,plain,
    ( k3_orders_2(sK1,X0_49,sK0(sK1,X0_49,X1_49)) = X1_49
    | k1_xboole_0 = X0_49
    | m1_orders_2(X1_49,sK1,X0_49) != iProver_top
    | m1_subset_1(X1_49,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1128])).

cnf(c_2486,plain,
    ( k3_orders_2(sK1,sK4,sK0(sK1,sK4,X0_49)) = X0_49
    | sK4 = k1_xboole_0
    | m1_orders_2(X0_49,sK1,sK4) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1501,c_1510])).

cnf(c_2654,plain,
    ( k3_orders_2(sK1,sK4,sK0(sK1,sK4,sK5)) = sK5
    | sK4 = k1_xboole_0
    | m1_orders_2(sK5,sK1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1500,c_2486])).

cnf(c_15,negated_conjecture,
    ( m1_orders_2(sK5,sK1,sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_40,plain,
    ( m1_orders_2(sK5,sK1,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2686,plain,
    ( sK4 = k1_xboole_0
    | k3_orders_2(sK1,sK4,sK0(sK1,sK4,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2654,c_40])).

cnf(c_2687,plain,
    ( k3_orders_2(sK1,sK4,sK0(sK1,sK4,sK5)) = sK5
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2686])).

cnf(c_13,plain,
    ( r2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_334,plain,
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
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_335,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_339,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_27,c_25,c_24,c_23])).

cnf(c_340,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_339])).

cnf(c_1134,plain,
    ( r2_orders_2(sK1,X0_49,X1_49)
    | ~ r2_hidden(X0_49,k3_orders_2(sK1,X2_49,X1_49))
    | ~ m1_subset_1(X2_49,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_340])).

cnf(c_1504,plain,
    ( r2_orders_2(sK1,X0_49,X1_49) = iProver_top
    | r2_hidden(X0_49,k3_orders_2(sK1,X2_49,X1_49)) != iProver_top
    | m1_subset_1(X2_49,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1134])).

cnf(c_2693,plain,
    ( sK4 = k1_xboole_0
    | r2_orders_2(sK1,X0_49,sK0(sK1,sK4,sK5)) = iProver_top
    | r2_hidden(X0_49,sK5) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2687,c_1504])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_36,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1145,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_1896,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f33])).

cnf(c_435,plain,
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
    inference(resolution_lifted,[status(thm)],[c_8,c_26])).

cnf(c_436,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_440,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_27,c_25,c_24,c_23])).

cnf(c_1130,plain,
    ( ~ m1_orders_2(X0_49,sK1,X1_49)
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X1_49,X0_49),u1_struct_0(sK1))
    | k1_xboole_0 = X1_49 ),
    inference(subtyping,[status(esa)],[c_440])).

cnf(c_1880,plain,
    ( ~ m1_orders_2(X0_49,sK1,sK4)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,sK4,X0_49),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1130])).

cnf(c_2343,plain,
    ( ~ m1_orders_2(sK5,sK1,sK4)
    | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1880])).

cnf(c_2344,plain,
    ( k1_xboole_0 = sK4
    | m1_orders_2(sK5,sK1,sK4) != iProver_top
    | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2343])).

cnf(c_1146,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_2026,plain,
    ( X0_49 != X1_49
    | sK4 != X1_49
    | sK4 = X0_49 ),
    inference(instantiation,[status(thm)],[c_1146])).

cnf(c_2364,plain,
    ( X0_49 != sK4
    | sK4 = X0_49
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2026])).

cnf(c_2365,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2364])).

cnf(c_2893,plain,
    ( sK4 = k1_xboole_0
    | r2_orders_2(sK1,X0_49,sK0(sK1,sK4,sK5)) = iProver_top
    | r2_hidden(X0_49,sK5) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2693,c_35,c_36,c_40,c_1896,c_2344,c_2365])).

cnf(c_2,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_10,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X3,X1)
    | r2_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_291,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X3,X1)
    | r2_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_2,c_10])).

cnf(c_619,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X3,X1)
    | r2_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_291,c_24])).

cnf(c_620,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X2,X0)
    | r2_orders_2(sK1,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ v4_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_622,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X2,X0)
    | r2_orders_2(sK1,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_620,c_25,c_23])).

cnf(c_623,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X2,X0)
    | r2_orders_2(sK1,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_622])).

cnf(c_1125,plain,
    ( ~ r2_orders_2(sK1,X0_49,X1_49)
    | ~ r2_orders_2(sK1,X2_49,X0_49)
    | r2_orders_2(sK1,X2_49,X1_49)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_49,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_623])).

cnf(c_1513,plain,
    ( r2_orders_2(sK1,X0_49,X1_49) != iProver_top
    | r2_orders_2(sK1,X2_49,X0_49) != iProver_top
    | r2_orders_2(sK1,X2_49,X1_49) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2_49,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(c_2903,plain,
    ( sK4 = k1_xboole_0
    | r2_orders_2(sK1,X0_49,X1_49) != iProver_top
    | r2_orders_2(sK1,X0_49,sK0(sK1,sK4,sK5)) = iProver_top
    | r2_hidden(X1_49,sK5) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2893,c_1513])).

cnf(c_3296,plain,
    ( m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X1_49,sK5) != iProver_top
    | r2_orders_2(sK1,X0_49,sK0(sK1,sK4,sK5)) = iProver_top
    | r2_orders_2(sK1,X0_49,X1_49) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2903,c_35,c_36,c_40,c_1896,c_2344,c_2365])).

cnf(c_3297,plain,
    ( sK4 = k1_xboole_0
    | r2_orders_2(sK1,X0_49,X1_49) != iProver_top
    | r2_orders_2(sK1,X0_49,sK0(sK1,sK4,sK5)) = iProver_top
    | r2_hidden(X1_49,sK5) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3296])).

cnf(c_3306,plain,
    ( sK4 = k1_xboole_0
    | r2_orders_2(sK1,sK2,sK0(sK1,sK4,sK5)) = iProver_top
    | r2_hidden(sK3,sK5) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1499,c_3297])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK3,sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_39,plain,
    ( r2_hidden(sK3,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(sK2,sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1158,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_1148,plain,
    ( ~ m1_subset_1(X0_49,X0_50)
    | m1_subset_1(X1_49,X0_50)
    | X1_49 != X0_49 ),
    theory(equality)).

cnf(c_1738,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_49 != sK4 ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_1740,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_4,plain,
    ( ~ m1_orders_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_516,plain,
    ( ~ m1_orders_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_26])).

cnf(c_517,plain,
    ( ~ m1_orders_2(X0,sK1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_521,plain,
    ( ~ m1_orders_2(X0,sK1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_27,c_25,c_24,c_23])).

cnf(c_1127,plain,
    ( ~ m1_orders_2(X0_49,sK1,k1_xboole_0)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0_49 ),
    inference(subtyping,[status(esa)],[c_521])).

cnf(c_1779,plain,
    ( ~ m1_orders_2(sK5,sK1,k1_xboole_0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_1805,plain,
    ( X0_49 != X1_49
    | X0_49 = sK4
    | sK4 != X1_49 ),
    inference(instantiation,[status(thm)],[c_1146])).

cnf(c_1806,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1805])).

cnf(c_2024,plain,
    ( X0_49 != X1_49
    | sK5 != X1_49
    | sK5 = X0_49 ),
    inference(instantiation,[status(thm)],[c_1146])).

cnf(c_2281,plain,
    ( X0_49 != sK5
    | sK5 = X0_49
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2024])).

cnf(c_2283,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2281])).

cnf(c_2282,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_2544,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_1149,plain,
    ( ~ m1_orders_2(X0_49,X0_48,X1_49)
    | m1_orders_2(X2_49,X0_48,X3_49)
    | X2_49 != X0_49
    | X3_49 != X1_49 ),
    theory(equality)).

cnf(c_1768,plain,
    ( m1_orders_2(X0_49,sK1,X1_49)
    | ~ m1_orders_2(sK5,sK1,sK4)
    | X1_49 != sK4
    | X0_49 != sK5 ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_2772,plain,
    ( ~ m1_orders_2(sK5,sK1,sK4)
    | m1_orders_2(sK5,sK1,k1_xboole_0)
    | sK5 != sK5
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1768])).

cnf(c_3013,plain,
    ( sK4 != X0_49
    | sK5 != X0_49
    | sK5 = sK4 ),
    inference(instantiation,[status(thm)],[c_1805])).

cnf(c_3016,plain,
    ( sK4 != k1_xboole_0
    | sK5 = sK4
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3013])).

cnf(c_1151,plain,
    ( ~ r2_hidden(X0_49,X1_49)
    | r2_hidden(X2_49,X3_49)
    | X2_49 != X0_49
    | X3_49 != X1_49 ),
    theory(equality)).

cnf(c_1758,plain,
    ( r2_hidden(X0_49,X1_49)
    | ~ r2_hidden(sK2,sK4)
    | X1_49 != sK4
    | X0_49 != sK2 ),
    inference(instantiation,[status(thm)],[c_1151])).

cnf(c_2952,plain,
    ( r2_hidden(sK2,X0_49)
    | ~ r2_hidden(sK2,sK4)
    | X0_49 != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1758])).

cnf(c_3331,plain,
    ( ~ r2_hidden(sK2,sK4)
    | r2_hidden(sK2,sK5)
    | sK5 != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2952])).

cnf(c_3402,plain,
    ( r2_orders_2(sK1,sK2,sK0(sK1,sK4,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3306,c_33,c_34,c_20,c_19,c_17,c_39,c_15,c_14,c_1158,c_1740,c_1779,c_1806,c_2283,c_2282,c_2544,c_2772,c_3016,c_3331])).

cnf(c_11,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X1,k3_orders_2(X0,X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_361,plain,
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
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_362,plain,
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
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_366,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_362,c_27,c_25,c_24,c_23])).

cnf(c_367,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_366])).

cnf(c_1133,plain,
    ( ~ r2_orders_2(sK1,X0_49,X1_49)
    | ~ r2_hidden(X0_49,X2_49)
    | r2_hidden(X0_49,k3_orders_2(sK1,X2_49,X1_49))
    | ~ m1_subset_1(X2_49,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_49,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_49,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_367])).

cnf(c_1505,plain,
    ( r2_orders_2(sK1,X0_49,X1_49) != iProver_top
    | r2_hidden(X0_49,X2_49) != iProver_top
    | r2_hidden(X0_49,k3_orders_2(sK1,X2_49,X1_49)) = iProver_top
    | m1_subset_1(X2_49,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_49,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1133])).

cnf(c_2692,plain,
    ( sK4 = k1_xboole_0
    | r2_orders_2(sK1,X0_49,sK0(sK1,sK4,sK5)) != iProver_top
    | r2_hidden(X0_49,sK4) != iProver_top
    | r2_hidden(X0_49,sK5) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2687,c_1505])).

cnf(c_3282,plain,
    ( sK4 = k1_xboole_0
    | r2_orders_2(sK1,X0_49,sK0(sK1,sK4,sK5)) != iProver_top
    | r2_hidden(X0_49,sK4) != iProver_top
    | r2_hidden(X0_49,sK5) = iProver_top
    | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2692,c_35,c_36,c_40,c_1896,c_2344,c_2365])).

cnf(c_3409,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2,sK4) != iProver_top
    | r2_hidden(sK2,sK5) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3402,c_3282])).

cnf(c_41,plain,
    ( r2_hidden(sK2,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_38,plain,
    ( r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3409,c_3331,c_3016,c_2772,c_2544,c_2282,c_2283,c_1806,c_1779,c_1740,c_1158,c_41,c_14,c_15,c_38,c_17,c_19,c_20,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  % Running in FOF mode
% 2.44/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.44/1.00  
% 2.44/1.00  ------  iProver source info
% 2.44/1.00  
% 2.44/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.44/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.44/1.00  git: non_committed_changes: false
% 2.44/1.00  git: last_make_outside_of_git: false
% 2.44/1.00  
% 2.44/1.00  ------ 
% 2.44/1.00  
% 2.44/1.00  ------ Input Options
% 2.44/1.00  
% 2.44/1.00  --out_options                           all
% 2.44/1.00  --tptp_safe_out                         true
% 2.44/1.00  --problem_path                          ""
% 2.44/1.00  --include_path                          ""
% 2.44/1.00  --clausifier                            res/vclausify_rel
% 2.44/1.00  --clausifier_options                    --mode clausify
% 2.44/1.00  --stdin                                 false
% 2.44/1.00  --stats_out                             all
% 2.44/1.00  
% 2.44/1.00  ------ General Options
% 2.44/1.00  
% 2.44/1.00  --fof                                   false
% 2.44/1.00  --time_out_real                         305.
% 2.44/1.00  --time_out_virtual                      -1.
% 2.44/1.00  --symbol_type_check                     false
% 2.44/1.00  --clausify_out                          false
% 2.44/1.00  --sig_cnt_out                           false
% 2.44/1.00  --trig_cnt_out                          false
% 2.44/1.00  --trig_cnt_out_tolerance                1.
% 2.44/1.00  --trig_cnt_out_sk_spl                   false
% 2.44/1.00  --abstr_cl_out                          false
% 2.44/1.00  
% 2.44/1.00  ------ Global Options
% 2.44/1.00  
% 2.44/1.00  --schedule                              default
% 2.44/1.00  --add_important_lit                     false
% 2.44/1.00  --prop_solver_per_cl                    1000
% 2.44/1.00  --min_unsat_core                        false
% 2.44/1.00  --soft_assumptions                      false
% 2.44/1.00  --soft_lemma_size                       3
% 2.44/1.00  --prop_impl_unit_size                   0
% 2.44/1.00  --prop_impl_unit                        []
% 2.44/1.00  --share_sel_clauses                     true
% 2.44/1.00  --reset_solvers                         false
% 2.44/1.00  --bc_imp_inh                            [conj_cone]
% 2.44/1.00  --conj_cone_tolerance                   3.
% 2.44/1.00  --extra_neg_conj                        none
% 2.44/1.00  --large_theory_mode                     true
% 2.44/1.00  --prolific_symb_bound                   200
% 2.44/1.00  --lt_threshold                          2000
% 2.44/1.00  --clause_weak_htbl                      true
% 2.44/1.00  --gc_record_bc_elim                     false
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing Options
% 2.44/1.00  
% 2.44/1.00  --preprocessing_flag                    true
% 2.44/1.00  --time_out_prep_mult                    0.1
% 2.44/1.00  --splitting_mode                        input
% 2.44/1.00  --splitting_grd                         true
% 2.44/1.00  --splitting_cvd                         false
% 2.44/1.00  --splitting_cvd_svl                     false
% 2.44/1.00  --splitting_nvd                         32
% 2.44/1.00  --sub_typing                            true
% 2.44/1.00  --prep_gs_sim                           true
% 2.44/1.00  --prep_unflatten                        true
% 2.44/1.00  --prep_res_sim                          true
% 2.44/1.00  --prep_upred                            true
% 2.44/1.00  --prep_sem_filter                       exhaustive
% 2.44/1.00  --prep_sem_filter_out                   false
% 2.44/1.00  --pred_elim                             true
% 2.44/1.00  --res_sim_input                         true
% 2.44/1.00  --eq_ax_congr_red                       true
% 2.44/1.00  --pure_diseq_elim                       true
% 2.44/1.00  --brand_transform                       false
% 2.44/1.00  --non_eq_to_eq                          false
% 2.44/1.00  --prep_def_merge                        true
% 2.44/1.00  --prep_def_merge_prop_impl              false
% 2.44/1.00  --prep_def_merge_mbd                    true
% 2.44/1.00  --prep_def_merge_tr_red                 false
% 2.44/1.00  --prep_def_merge_tr_cl                  false
% 2.44/1.00  --smt_preprocessing                     true
% 2.44/1.00  --smt_ac_axioms                         fast
% 2.44/1.00  --preprocessed_out                      false
% 2.44/1.00  --preprocessed_stats                    false
% 2.44/1.00  
% 2.44/1.00  ------ Abstraction refinement Options
% 2.44/1.00  
% 2.44/1.00  --abstr_ref                             []
% 2.44/1.00  --abstr_ref_prep                        false
% 2.44/1.00  --abstr_ref_until_sat                   false
% 2.44/1.00  --abstr_ref_sig_restrict                funpre
% 2.44/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/1.00  --abstr_ref_under                       []
% 2.44/1.00  
% 2.44/1.00  ------ SAT Options
% 2.44/1.00  
% 2.44/1.00  --sat_mode                              false
% 2.44/1.00  --sat_fm_restart_options                ""
% 2.44/1.00  --sat_gr_def                            false
% 2.44/1.00  --sat_epr_types                         true
% 2.44/1.00  --sat_non_cyclic_types                  false
% 2.44/1.00  --sat_finite_models                     false
% 2.44/1.00  --sat_fm_lemmas                         false
% 2.44/1.00  --sat_fm_prep                           false
% 2.44/1.00  --sat_fm_uc_incr                        true
% 2.44/1.00  --sat_out_model                         small
% 2.44/1.00  --sat_out_clauses                       false
% 2.44/1.00  
% 2.44/1.00  ------ QBF Options
% 2.44/1.00  
% 2.44/1.00  --qbf_mode                              false
% 2.44/1.00  --qbf_elim_univ                         false
% 2.44/1.00  --qbf_dom_inst                          none
% 2.44/1.00  --qbf_dom_pre_inst                      false
% 2.44/1.00  --qbf_sk_in                             false
% 2.44/1.00  --qbf_pred_elim                         true
% 2.44/1.00  --qbf_split                             512
% 2.44/1.00  
% 2.44/1.00  ------ BMC1 Options
% 2.44/1.00  
% 2.44/1.00  --bmc1_incremental                      false
% 2.44/1.00  --bmc1_axioms                           reachable_all
% 2.44/1.00  --bmc1_min_bound                        0
% 2.44/1.00  --bmc1_max_bound                        -1
% 2.44/1.00  --bmc1_max_bound_default                -1
% 2.44/1.00  --bmc1_symbol_reachability              true
% 2.44/1.00  --bmc1_property_lemmas                  false
% 2.44/1.00  --bmc1_k_induction                      false
% 2.44/1.00  --bmc1_non_equiv_states                 false
% 2.44/1.00  --bmc1_deadlock                         false
% 2.44/1.00  --bmc1_ucm                              false
% 2.44/1.00  --bmc1_add_unsat_core                   none
% 2.44/1.00  --bmc1_unsat_core_children              false
% 2.44/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/1.00  --bmc1_out_stat                         full
% 2.44/1.00  --bmc1_ground_init                      false
% 2.44/1.00  --bmc1_pre_inst_next_state              false
% 2.44/1.00  --bmc1_pre_inst_state                   false
% 2.44/1.00  --bmc1_pre_inst_reach_state             false
% 2.44/1.00  --bmc1_out_unsat_core                   false
% 2.44/1.00  --bmc1_aig_witness_out                  false
% 2.44/1.00  --bmc1_verbose                          false
% 2.44/1.00  --bmc1_dump_clauses_tptp                false
% 2.44/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.44/1.00  --bmc1_dump_file                        -
% 2.44/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.44/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.44/1.00  --bmc1_ucm_extend_mode                  1
% 2.44/1.00  --bmc1_ucm_init_mode                    2
% 2.44/1.00  --bmc1_ucm_cone_mode                    none
% 2.44/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.44/1.00  --bmc1_ucm_relax_model                  4
% 2.44/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.44/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/1.00  --bmc1_ucm_layered_model                none
% 2.44/1.00  --bmc1_ucm_max_lemma_size               10
% 2.44/1.00  
% 2.44/1.00  ------ AIG Options
% 2.44/1.00  
% 2.44/1.00  --aig_mode                              false
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation Options
% 2.44/1.00  
% 2.44/1.00  --instantiation_flag                    true
% 2.44/1.00  --inst_sos_flag                         false
% 2.44/1.00  --inst_sos_phase                        true
% 2.44/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel_side                     num_symb
% 2.44/1.00  --inst_solver_per_active                1400
% 2.44/1.00  --inst_solver_calls_frac                1.
% 2.44/1.00  --inst_passive_queue_type               priority_queues
% 2.44/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/1.00  --inst_passive_queues_freq              [25;2]
% 2.44/1.00  --inst_dismatching                      true
% 2.44/1.00  --inst_eager_unprocessed_to_passive     true
% 2.44/1.00  --inst_prop_sim_given                   true
% 2.44/1.00  --inst_prop_sim_new                     false
% 2.44/1.00  --inst_subs_new                         false
% 2.44/1.00  --inst_eq_res_simp                      false
% 2.44/1.00  --inst_subs_given                       false
% 2.44/1.00  --inst_orphan_elimination               true
% 2.44/1.00  --inst_learning_loop_flag               true
% 2.44/1.00  --inst_learning_start                   3000
% 2.44/1.00  --inst_learning_factor                  2
% 2.44/1.00  --inst_start_prop_sim_after_learn       3
% 2.44/1.00  --inst_sel_renew                        solver
% 2.44/1.00  --inst_lit_activity_flag                true
% 2.44/1.00  --inst_restr_to_given                   false
% 2.44/1.00  --inst_activity_threshold               500
% 2.44/1.00  --inst_out_proof                        true
% 2.44/1.00  
% 2.44/1.00  ------ Resolution Options
% 2.44/1.00  
% 2.44/1.00  --resolution_flag                       true
% 2.44/1.00  --res_lit_sel                           adaptive
% 2.44/1.00  --res_lit_sel_side                      none
% 2.44/1.00  --res_ordering                          kbo
% 2.44/1.00  --res_to_prop_solver                    active
% 2.44/1.00  --res_prop_simpl_new                    false
% 2.44/1.00  --res_prop_simpl_given                  true
% 2.44/1.00  --res_passive_queue_type                priority_queues
% 2.44/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/1.00  --res_passive_queues_freq               [15;5]
% 2.44/1.00  --res_forward_subs                      full
% 2.44/1.00  --res_backward_subs                     full
% 2.44/1.00  --res_forward_subs_resolution           true
% 2.44/1.00  --res_backward_subs_resolution          true
% 2.44/1.00  --res_orphan_elimination                true
% 2.44/1.00  --res_time_limit                        2.
% 2.44/1.00  --res_out_proof                         true
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Options
% 2.44/1.00  
% 2.44/1.00  --superposition_flag                    true
% 2.44/1.00  --sup_passive_queue_type                priority_queues
% 2.44/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.44/1.00  --demod_completeness_check              fast
% 2.44/1.00  --demod_use_ground                      true
% 2.44/1.00  --sup_to_prop_solver                    passive
% 2.44/1.00  --sup_prop_simpl_new                    true
% 2.44/1.00  --sup_prop_simpl_given                  true
% 2.44/1.00  --sup_fun_splitting                     false
% 2.44/1.00  --sup_smt_interval                      50000
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Simplification Setup
% 2.44/1.00  
% 2.44/1.00  --sup_indices_passive                   []
% 2.44/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_full_bw                           [BwDemod]
% 2.44/1.00  --sup_immed_triv                        [TrivRules]
% 2.44/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_immed_bw_main                     []
% 2.44/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  
% 2.44/1.00  ------ Combination Options
% 2.44/1.00  
% 2.44/1.00  --comb_res_mult                         3
% 2.44/1.00  --comb_sup_mult                         2
% 2.44/1.00  --comb_inst_mult                        10
% 2.44/1.00  
% 2.44/1.00  ------ Debug Options
% 2.44/1.00  
% 2.44/1.00  --dbg_backtrace                         false
% 2.44/1.00  --dbg_dump_prop_clauses                 false
% 2.44/1.00  --dbg_dump_prop_clauses_file            -
% 2.44/1.00  --dbg_out_stat                          false
% 2.44/1.00  ------ Parsing...
% 2.44/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.44/1.00  ------ Proving...
% 2.44/1.00  ------ Problem Properties 
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  clauses                                 20
% 2.44/1.00  conjectures                             9
% 2.44/1.00  EPR                                     5
% 2.44/1.00  Horn                                    16
% 2.44/1.00  unary                                   9
% 2.44/1.00  binary                                  2
% 2.44/1.00  lits                                    60
% 2.44/1.00  lits eq                                 6
% 2.44/1.00  fd_pure                                 0
% 2.44/1.00  fd_pseudo                               0
% 2.44/1.00  fd_cond                                 4
% 2.44/1.00  fd_pseudo_cond                          0
% 2.44/1.00  AC symbols                              0
% 2.44/1.00  
% 2.44/1.00  ------ Schedule dynamic 5 is on 
% 2.44/1.00  
% 2.44/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  ------ 
% 2.44/1.00  Current options:
% 2.44/1.00  ------ 
% 2.44/1.00  
% 2.44/1.00  ------ Input Options
% 2.44/1.00  
% 2.44/1.00  --out_options                           all
% 2.44/1.00  --tptp_safe_out                         true
% 2.44/1.00  --problem_path                          ""
% 2.44/1.00  --include_path                          ""
% 2.44/1.00  --clausifier                            res/vclausify_rel
% 2.44/1.00  --clausifier_options                    --mode clausify
% 2.44/1.00  --stdin                                 false
% 2.44/1.00  --stats_out                             all
% 2.44/1.00  
% 2.44/1.00  ------ General Options
% 2.44/1.00  
% 2.44/1.00  --fof                                   false
% 2.44/1.00  --time_out_real                         305.
% 2.44/1.00  --time_out_virtual                      -1.
% 2.44/1.00  --symbol_type_check                     false
% 2.44/1.00  --clausify_out                          false
% 2.44/1.00  --sig_cnt_out                           false
% 2.44/1.00  --trig_cnt_out                          false
% 2.44/1.00  --trig_cnt_out_tolerance                1.
% 2.44/1.00  --trig_cnt_out_sk_spl                   false
% 2.44/1.00  --abstr_cl_out                          false
% 2.44/1.00  
% 2.44/1.00  ------ Global Options
% 2.44/1.00  
% 2.44/1.00  --schedule                              default
% 2.44/1.00  --add_important_lit                     false
% 2.44/1.00  --prop_solver_per_cl                    1000
% 2.44/1.00  --min_unsat_core                        false
% 2.44/1.00  --soft_assumptions                      false
% 2.44/1.00  --soft_lemma_size                       3
% 2.44/1.00  --prop_impl_unit_size                   0
% 2.44/1.00  --prop_impl_unit                        []
% 2.44/1.00  --share_sel_clauses                     true
% 2.44/1.00  --reset_solvers                         false
% 2.44/1.00  --bc_imp_inh                            [conj_cone]
% 2.44/1.00  --conj_cone_tolerance                   3.
% 2.44/1.00  --extra_neg_conj                        none
% 2.44/1.00  --large_theory_mode                     true
% 2.44/1.00  --prolific_symb_bound                   200
% 2.44/1.00  --lt_threshold                          2000
% 2.44/1.00  --clause_weak_htbl                      true
% 2.44/1.00  --gc_record_bc_elim                     false
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing Options
% 2.44/1.00  
% 2.44/1.00  --preprocessing_flag                    true
% 2.44/1.00  --time_out_prep_mult                    0.1
% 2.44/1.00  --splitting_mode                        input
% 2.44/1.00  --splitting_grd                         true
% 2.44/1.00  --splitting_cvd                         false
% 2.44/1.00  --splitting_cvd_svl                     false
% 2.44/1.00  --splitting_nvd                         32
% 2.44/1.00  --sub_typing                            true
% 2.44/1.00  --prep_gs_sim                           true
% 2.44/1.00  --prep_unflatten                        true
% 2.44/1.00  --prep_res_sim                          true
% 2.44/1.00  --prep_upred                            true
% 2.44/1.00  --prep_sem_filter                       exhaustive
% 2.44/1.00  --prep_sem_filter_out                   false
% 2.44/1.00  --pred_elim                             true
% 2.44/1.00  --res_sim_input                         true
% 2.44/1.00  --eq_ax_congr_red                       true
% 2.44/1.00  --pure_diseq_elim                       true
% 2.44/1.00  --brand_transform                       false
% 2.44/1.00  --non_eq_to_eq                          false
% 2.44/1.00  --prep_def_merge                        true
% 2.44/1.00  --prep_def_merge_prop_impl              false
% 2.44/1.00  --prep_def_merge_mbd                    true
% 2.44/1.00  --prep_def_merge_tr_red                 false
% 2.44/1.00  --prep_def_merge_tr_cl                  false
% 2.44/1.00  --smt_preprocessing                     true
% 2.44/1.00  --smt_ac_axioms                         fast
% 2.44/1.00  --preprocessed_out                      false
% 2.44/1.00  --preprocessed_stats                    false
% 2.44/1.00  
% 2.44/1.00  ------ Abstraction refinement Options
% 2.44/1.00  
% 2.44/1.00  --abstr_ref                             []
% 2.44/1.00  --abstr_ref_prep                        false
% 2.44/1.00  --abstr_ref_until_sat                   false
% 2.44/1.00  --abstr_ref_sig_restrict                funpre
% 2.44/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/1.00  --abstr_ref_under                       []
% 2.44/1.00  
% 2.44/1.00  ------ SAT Options
% 2.44/1.00  
% 2.44/1.00  --sat_mode                              false
% 2.44/1.00  --sat_fm_restart_options                ""
% 2.44/1.00  --sat_gr_def                            false
% 2.44/1.00  --sat_epr_types                         true
% 2.44/1.00  --sat_non_cyclic_types                  false
% 2.44/1.00  --sat_finite_models                     false
% 2.44/1.00  --sat_fm_lemmas                         false
% 2.44/1.00  --sat_fm_prep                           false
% 2.44/1.00  --sat_fm_uc_incr                        true
% 2.44/1.00  --sat_out_model                         small
% 2.44/1.00  --sat_out_clauses                       false
% 2.44/1.00  
% 2.44/1.00  ------ QBF Options
% 2.44/1.00  
% 2.44/1.00  --qbf_mode                              false
% 2.44/1.00  --qbf_elim_univ                         false
% 2.44/1.00  --qbf_dom_inst                          none
% 2.44/1.00  --qbf_dom_pre_inst                      false
% 2.44/1.00  --qbf_sk_in                             false
% 2.44/1.00  --qbf_pred_elim                         true
% 2.44/1.00  --qbf_split                             512
% 2.44/1.00  
% 2.44/1.00  ------ BMC1 Options
% 2.44/1.00  
% 2.44/1.00  --bmc1_incremental                      false
% 2.44/1.00  --bmc1_axioms                           reachable_all
% 2.44/1.00  --bmc1_min_bound                        0
% 2.44/1.00  --bmc1_max_bound                        -1
% 2.44/1.00  --bmc1_max_bound_default                -1
% 2.44/1.00  --bmc1_symbol_reachability              true
% 2.44/1.00  --bmc1_property_lemmas                  false
% 2.44/1.00  --bmc1_k_induction                      false
% 2.44/1.00  --bmc1_non_equiv_states                 false
% 2.44/1.00  --bmc1_deadlock                         false
% 2.44/1.00  --bmc1_ucm                              false
% 2.44/1.00  --bmc1_add_unsat_core                   none
% 2.44/1.00  --bmc1_unsat_core_children              false
% 2.44/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/1.00  --bmc1_out_stat                         full
% 2.44/1.00  --bmc1_ground_init                      false
% 2.44/1.00  --bmc1_pre_inst_next_state              false
% 2.44/1.00  --bmc1_pre_inst_state                   false
% 2.44/1.00  --bmc1_pre_inst_reach_state             false
% 2.44/1.00  --bmc1_out_unsat_core                   false
% 2.44/1.00  --bmc1_aig_witness_out                  false
% 2.44/1.00  --bmc1_verbose                          false
% 2.44/1.00  --bmc1_dump_clauses_tptp                false
% 2.44/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.44/1.00  --bmc1_dump_file                        -
% 2.44/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.44/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.44/1.00  --bmc1_ucm_extend_mode                  1
% 2.44/1.00  --bmc1_ucm_init_mode                    2
% 2.44/1.00  --bmc1_ucm_cone_mode                    none
% 2.44/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.44/1.00  --bmc1_ucm_relax_model                  4
% 2.44/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.44/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/1.00  --bmc1_ucm_layered_model                none
% 2.44/1.00  --bmc1_ucm_max_lemma_size               10
% 2.44/1.00  
% 2.44/1.00  ------ AIG Options
% 2.44/1.00  
% 2.44/1.00  --aig_mode                              false
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation Options
% 2.44/1.00  
% 2.44/1.00  --instantiation_flag                    true
% 2.44/1.00  --inst_sos_flag                         false
% 2.44/1.00  --inst_sos_phase                        true
% 2.44/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel_side                     none
% 2.44/1.00  --inst_solver_per_active                1400
% 2.44/1.00  --inst_solver_calls_frac                1.
% 2.44/1.00  --inst_passive_queue_type               priority_queues
% 2.44/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/1.00  --inst_passive_queues_freq              [25;2]
% 2.44/1.00  --inst_dismatching                      true
% 2.44/1.00  --inst_eager_unprocessed_to_passive     true
% 2.44/1.00  --inst_prop_sim_given                   true
% 2.44/1.00  --inst_prop_sim_new                     false
% 2.44/1.00  --inst_subs_new                         false
% 2.44/1.00  --inst_eq_res_simp                      false
% 2.44/1.00  --inst_subs_given                       false
% 2.44/1.00  --inst_orphan_elimination               true
% 2.44/1.00  --inst_learning_loop_flag               true
% 2.44/1.00  --inst_learning_start                   3000
% 2.44/1.00  --inst_learning_factor                  2
% 2.44/1.00  --inst_start_prop_sim_after_learn       3
% 2.44/1.00  --inst_sel_renew                        solver
% 2.44/1.00  --inst_lit_activity_flag                true
% 2.44/1.00  --inst_restr_to_given                   false
% 2.44/1.00  --inst_activity_threshold               500
% 2.44/1.00  --inst_out_proof                        true
% 2.44/1.00  
% 2.44/1.00  ------ Resolution Options
% 2.44/1.00  
% 2.44/1.00  --resolution_flag                       false
% 2.44/1.00  --res_lit_sel                           adaptive
% 2.44/1.00  --res_lit_sel_side                      none
% 2.44/1.00  --res_ordering                          kbo
% 2.44/1.00  --res_to_prop_solver                    active
% 2.44/1.00  --res_prop_simpl_new                    false
% 2.44/1.00  --res_prop_simpl_given                  true
% 2.44/1.00  --res_passive_queue_type                priority_queues
% 2.44/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/1.00  --res_passive_queues_freq               [15;5]
% 2.44/1.00  --res_forward_subs                      full
% 2.44/1.00  --res_backward_subs                     full
% 2.44/1.00  --res_forward_subs_resolution           true
% 2.44/1.00  --res_backward_subs_resolution          true
% 2.44/1.00  --res_orphan_elimination                true
% 2.44/1.00  --res_time_limit                        2.
% 2.44/1.00  --res_out_proof                         true
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Options
% 2.44/1.00  
% 2.44/1.00  --superposition_flag                    true
% 2.44/1.00  --sup_passive_queue_type                priority_queues
% 2.44/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.44/1.00  --demod_completeness_check              fast
% 2.44/1.00  --demod_use_ground                      true
% 2.44/1.00  --sup_to_prop_solver                    passive
% 2.44/1.00  --sup_prop_simpl_new                    true
% 2.44/1.00  --sup_prop_simpl_given                  true
% 2.44/1.00  --sup_fun_splitting                     false
% 2.44/1.00  --sup_smt_interval                      50000
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Simplification Setup
% 2.44/1.00  
% 2.44/1.00  --sup_indices_passive                   []
% 2.44/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_full_bw                           [BwDemod]
% 2.44/1.00  --sup_immed_triv                        [TrivRules]
% 2.44/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_immed_bw_main                     []
% 2.44/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  
% 2.44/1.00  ------ Combination Options
% 2.44/1.00  
% 2.44/1.00  --comb_res_mult                         3
% 2.44/1.00  --comb_sup_mult                         2
% 2.44/1.00  --comb_inst_mult                        10
% 2.44/1.00  
% 2.44/1.00  ------ Debug Options
% 2.44/1.00  
% 2.44/1.00  --dbg_backtrace                         false
% 2.44/1.00  --dbg_dump_prop_clauses                 false
% 2.44/1.00  --dbg_dump_prop_clauses_file            -
% 2.44/1.00  --dbg_out_stat                          false
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  ------ Proving...
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  % SZS status Theorem for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  fof(f5,conjecture,(
% 2.44/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f6,negated_conjecture,(
% 2.44/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 2.44/1.00    inference(negated_conjecture,[],[f5])).
% 2.44/1.00  
% 2.44/1.00  fof(f14,plain,(
% 2.44/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_hidden(X1,X4) & (m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f6])).
% 2.44/1.00  
% 2.44/1.00  fof(f15,plain,(
% 2.44/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f14])).
% 2.44/1.00  
% 2.44/1.00  fof(f28,plain,(
% 2.44/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(X1,sK5) & m1_orders_2(sK5,X0,X3) & r2_hidden(X2,sK5) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f27,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,sK4) & r2_hidden(X2,X4) & r2_hidden(X1,sK4) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f26,plain,(
% 2.44/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(sK3,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,sK3) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f25,plain,(
% 2.44/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(sK2,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(sK2,X3) & r2_orders_2(X0,sK2,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f24,plain,(
% 2.44/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,sK1,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(sK1,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f29,plain,(
% 2.44/1.00    ((((~r2_hidden(sK2,sK5) & m1_orders_2(sK5,sK1,sK4) & r2_hidden(sK3,sK5) & r2_hidden(sK2,sK4) & r2_orders_2(sK1,sK2,sK3) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 2.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f15,f28,f27,f26,f25,f24])).
% 2.44/1.00  
% 2.44/1.00  fof(f53,plain,(
% 2.44/1.00    r2_orders_2(sK1,sK2,sK3)),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f52,plain,(
% 2.44/1.00    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f51,plain,(
% 2.44/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f2,axiom,(
% 2.44/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f8,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f2])).
% 2.44/1.00  
% 2.44/1.00  fof(f9,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f8])).
% 2.44/1.00  
% 2.44/1.00  fof(f18,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(nnf_transformation,[],[f9])).
% 2.44/1.00  
% 2.44/1.00  fof(f19,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(rectify,[],[f18])).
% 2.44/1.00  
% 2.44/1.00  fof(f20,plain,(
% 2.44/1.00    ! [X2,X1,X0] : (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2 & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f21,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2 & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 2.44/1.00  
% 2.44/1.00  fof(f35,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f21])).
% 2.44/1.00  
% 2.44/1.00  fof(f45,plain,(
% 2.44/1.00    v3_orders_2(sK1)),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f44,plain,(
% 2.44/1.00    ~v2_struct_0(sK1)),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f46,plain,(
% 2.44/1.00    v4_orders_2(sK1)),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f47,plain,(
% 2.44/1.00    v5_orders_2(sK1)),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f48,plain,(
% 2.44/1.00    l1_orders_2(sK1)),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f56,plain,(
% 2.44/1.00    m1_orders_2(sK5,sK1,sK4)),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f4,axiom,(
% 2.44/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f12,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f4])).
% 2.44/1.00  
% 2.44/1.00  fof(f13,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f12])).
% 2.44/1.00  
% 2.44/1.00  fof(f22,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(nnf_transformation,[],[f13])).
% 2.44/1.00  
% 2.44/1.00  fof(f23,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f22])).
% 2.44/1.00  
% 2.44/1.00  fof(f41,plain,(
% 2.44/1.00    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f23])).
% 2.44/1.00  
% 2.44/1.00  fof(f33,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f21])).
% 2.44/1.00  
% 2.44/1.00  fof(f1,axiom,(
% 2.44/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f7,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.44/1.00    inference(ennf_transformation,[],[f1])).
% 2.44/1.00  
% 2.44/1.00  fof(f16,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.44/1.00    inference(nnf_transformation,[],[f7])).
% 2.44/1.00  
% 2.44/1.00  fof(f17,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.44/1.00    inference(flattening,[],[f16])).
% 2.44/1.00  
% 2.44/1.00  fof(f30,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f17])).
% 2.44/1.00  
% 2.44/1.00  fof(f3,axiom,(
% 2.44/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) => r2_orders_2(X0,X1,X3))))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f10,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_orders_2(X0,X1,X3) | ((~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2)))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f3])).
% 2.44/1.00  
% 2.44/1.00  fof(f11,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_orders_2(X0,X1,X3) | ((~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0))),
% 2.44/1.00    inference(flattening,[],[f10])).
% 2.44/1.00  
% 2.44/1.00  fof(f39,plain,(
% 2.44/1.00    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f11])).
% 2.44/1.00  
% 2.44/1.00  fof(f49,plain,(
% 2.44/1.00    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f50,plain,(
% 2.44/1.00    m1_subset_1(sK3,u1_struct_0(sK1))),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f54,plain,(
% 2.44/1.00    r2_hidden(sK2,sK4)),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f55,plain,(
% 2.44/1.00    r2_hidden(sK3,sK5)),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f57,plain,(
% 2.44/1.00    ~r2_hidden(sK2,sK5)),
% 2.44/1.00    inference(cnf_transformation,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f37,plain,(
% 2.44/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f21])).
% 2.44/1.00  
% 2.44/1.00  fof(f61,plain,(
% 2.44/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(equality_resolution,[],[f37])).
% 2.44/1.00  
% 2.44/1.00  fof(f43,plain,(
% 2.44/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f23])).
% 2.44/1.00  
% 2.44/1.00  cnf(c_18,negated_conjecture,
% 2.44/1.00      ( r2_orders_2(sK1,sK2,sK3) ),
% 2.44/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1139,negated_conjecture,
% 2.44/1.00      ( r2_orders_2(sK1,sK2,sK3) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1499,plain,
% 2.44/1.00      ( r2_orders_2(sK1,sK2,sK3) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1139]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_19,negated_conjecture,
% 2.44/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.44/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1138,negated_conjecture,
% 2.44/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1500,plain,
% 2.44/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1138]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_20,negated_conjecture,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.44/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1137,negated_conjecture,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1501,plain,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1137]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_6,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ v3_orders_2(X1)
% 2.44/1.00      | ~ v4_orders_2(X1)
% 2.44/1.00      | ~ v5_orders_2(X1)
% 2.44/1.00      | ~ l1_orders_2(X1)
% 2.44/1.00      | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
% 2.44/1.00      | k1_xboole_0 = X2 ),
% 2.44/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_26,negated_conjecture,
% 2.44/1.00      ( v3_orders_2(sK1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_489,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ v4_orders_2(X1)
% 2.44/1.00      | ~ v5_orders_2(X1)
% 2.44/1.00      | ~ l1_orders_2(X1)
% 2.44/1.00      | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
% 2.44/1.00      | sK1 != X1
% 2.44/1.00      | k1_xboole_0 = X2 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_26]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_490,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | v2_struct_0(sK1)
% 2.44/1.00      | ~ v4_orders_2(sK1)
% 2.44/1.00      | ~ v5_orders_2(sK1)
% 2.44/1.00      | ~ l1_orders_2(sK1)
% 2.44/1.00      | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
% 2.44/1.00      | k1_xboole_0 = X1 ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_489]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_27,negated_conjecture,
% 2.44/1.00      ( ~ v2_struct_0(sK1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_25,negated_conjecture,
% 2.44/1.00      ( v4_orders_2(sK1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_24,negated_conjecture,
% 2.44/1.00      ( v5_orders_2(sK1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_23,negated_conjecture,
% 2.44/1.00      ( l1_orders_2(sK1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_494,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
% 2.44/1.00      | k1_xboole_0 = X1 ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_490,c_27,c_25,c_24,c_23]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1128,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0_49,sK1,X1_49)
% 2.44/1.00      | ~ m1_subset_1(X1_49,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | k3_orders_2(sK1,X1_49,sK0(sK1,X1_49,X0_49)) = X0_49
% 2.44/1.00      | k1_xboole_0 = X1_49 ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_494]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1510,plain,
% 2.44/1.00      ( k3_orders_2(sK1,X0_49,sK0(sK1,X0_49,X1_49)) = X1_49
% 2.44/1.00      | k1_xboole_0 = X0_49
% 2.44/1.00      | m1_orders_2(X1_49,sK1,X0_49) != iProver_top
% 2.44/1.00      | m1_subset_1(X1_49,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.44/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1128]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2486,plain,
% 2.44/1.00      ( k3_orders_2(sK1,sK4,sK0(sK1,sK4,X0_49)) = X0_49
% 2.44/1.00      | sK4 = k1_xboole_0
% 2.44/1.00      | m1_orders_2(X0_49,sK1,sK4) != iProver_top
% 2.44/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1501,c_1510]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2654,plain,
% 2.44/1.00      ( k3_orders_2(sK1,sK4,sK0(sK1,sK4,sK5)) = sK5
% 2.44/1.00      | sK4 = k1_xboole_0
% 2.44/1.00      | m1_orders_2(sK5,sK1,sK4) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1500,c_2486]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_15,negated_conjecture,
% 2.44/1.00      ( m1_orders_2(sK5,sK1,sK4) ),
% 2.44/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_40,plain,
% 2.44/1.00      ( m1_orders_2(sK5,sK1,sK4) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2686,plain,
% 2.44/1.00      ( sK4 = k1_xboole_0 | k3_orders_2(sK1,sK4,sK0(sK1,sK4,sK5)) = sK5 ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_2654,c_40]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2687,plain,
% 2.44/1.00      ( k3_orders_2(sK1,sK4,sK0(sK1,sK4,sK5)) = sK5 | sK4 = k1_xboole_0 ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_2686]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_13,plain,
% 2.44/1.00      ( r2_orders_2(X0,X1,X2)
% 2.44/1.00      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 2.44/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ v3_orders_2(X0)
% 2.44/1.00      | ~ v4_orders_2(X0)
% 2.44/1.00      | ~ v5_orders_2(X0)
% 2.44/1.00      | ~ l1_orders_2(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_334,plain,
% 2.44/1.00      ( r2_orders_2(X0,X1,X2)
% 2.44/1.00      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 2.44/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ v4_orders_2(X0)
% 2.44/1.00      | ~ v5_orders_2(X0)
% 2.44/1.00      | ~ l1_orders_2(X0)
% 2.44/1.00      | sK1 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_335,plain,
% 2.44/1.00      ( r2_orders_2(sK1,X0,X1)
% 2.44/1.00      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.44/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.44/1.00      | v2_struct_0(sK1)
% 2.44/1.00      | ~ v4_orders_2(sK1)
% 2.44/1.00      | ~ v5_orders_2(sK1)
% 2.44/1.00      | ~ l1_orders_2(sK1) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_334]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_339,plain,
% 2.44/1.00      ( r2_orders_2(sK1,X0,X1)
% 2.44/1.00      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.44/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_335,c_27,c_25,c_24,c_23]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_340,plain,
% 2.44/1.00      ( r2_orders_2(sK1,X0,X1)
% 2.44/1.00      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.44/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_339]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1134,plain,
% 2.44/1.00      ( r2_orders_2(sK1,X0_49,X1_49)
% 2.44/1.00      | ~ r2_hidden(X0_49,k3_orders_2(sK1,X2_49,X1_49))
% 2.44/1.00      | ~ m1_subset_1(X2_49,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X0_49,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X1_49,u1_struct_0(sK1)) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_340]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1504,plain,
% 2.44/1.00      ( r2_orders_2(sK1,X0_49,X1_49) = iProver_top
% 2.44/1.00      | r2_hidden(X0_49,k3_orders_2(sK1,X2_49,X1_49)) != iProver_top
% 2.44/1.00      | m1_subset_1(X2_49,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.44/1.00      | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | m1_subset_1(X1_49,u1_struct_0(sK1)) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1134]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2693,plain,
% 2.44/1.00      ( sK4 = k1_xboole_0
% 2.44/1.00      | r2_orders_2(sK1,X0_49,sK0(sK1,sK4,sK5)) = iProver_top
% 2.44/1.00      | r2_hidden(X0_49,sK5) != iProver_top
% 2.44/1.00      | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_2687,c_1504]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_35,plain,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_36,plain,
% 2.44/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1145,plain,( X0_49 = X0_49 ),theory(equality) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1896,plain,
% 2.44/1.00      ( sK4 = sK4 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1145]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_8,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ v3_orders_2(X1)
% 2.44/1.00      | ~ v4_orders_2(X1)
% 2.44/1.00      | ~ v5_orders_2(X1)
% 2.44/1.00      | ~ l1_orders_2(X1)
% 2.44/1.00      | k1_xboole_0 = X2 ),
% 2.44/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_435,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ v4_orders_2(X1)
% 2.44/1.00      | ~ v5_orders_2(X1)
% 2.44/1.00      | ~ l1_orders_2(X1)
% 2.44/1.00      | sK1 != X1
% 2.44/1.00      | k1_xboole_0 = X2 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_26]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_436,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
% 2.44/1.00      | v2_struct_0(sK1)
% 2.44/1.00      | ~ v4_orders_2(sK1)
% 2.44/1.00      | ~ v5_orders_2(sK1)
% 2.44/1.00      | ~ l1_orders_2(sK1)
% 2.44/1.00      | k1_xboole_0 = X1 ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_435]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_440,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
% 2.44/1.00      | k1_xboole_0 = X1 ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_436,c_27,c_25,c_24,c_23]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1130,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0_49,sK1,X1_49)
% 2.44/1.00      | ~ m1_subset_1(X1_49,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | m1_subset_1(sK0(sK1,X1_49,X0_49),u1_struct_0(sK1))
% 2.44/1.00      | k1_xboole_0 = X1_49 ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_440]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1880,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0_49,sK1,sK4)
% 2.44/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | m1_subset_1(sK0(sK1,sK4,X0_49),u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | k1_xboole_0 = sK4 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1130]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2343,plain,
% 2.44/1.00      ( ~ m1_orders_2(sK5,sK1,sK4)
% 2.44/1.00      | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | k1_xboole_0 = sK4 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1880]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2344,plain,
% 2.44/1.00      ( k1_xboole_0 = sK4
% 2.44/1.00      | m1_orders_2(sK5,sK1,sK4) != iProver_top
% 2.44/1.00      | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1)) = iProver_top
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.44/1.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_2343]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1146,plain,
% 2.44/1.00      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 2.44/1.00      theory(equality) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2026,plain,
% 2.44/1.00      ( X0_49 != X1_49 | sK4 != X1_49 | sK4 = X0_49 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1146]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2364,plain,
% 2.44/1.00      ( X0_49 != sK4 | sK4 = X0_49 | sK4 != sK4 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_2026]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2365,plain,
% 2.44/1.00      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_2364]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2893,plain,
% 2.44/1.00      ( sK4 = k1_xboole_0
% 2.44/1.00      | r2_orders_2(sK1,X0_49,sK0(sK1,sK4,sK5)) = iProver_top
% 2.44/1.00      | r2_hidden(X0_49,sK5) != iProver_top
% 2.44/1.00      | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_2693,c_35,c_36,c_40,c_1896,c_2344,c_2365]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2,plain,
% 2.44/1.00      ( r1_orders_2(X0,X1,X2)
% 2.44/1.00      | ~ r2_orders_2(X0,X1,X2)
% 2.44/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.44/1.00      | ~ l1_orders_2(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f30]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_10,plain,
% 2.44/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 2.44/1.00      | ~ r2_orders_2(X0,X3,X1)
% 2.44/1.00      | r2_orders_2(X0,X3,X2)
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.44/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.44/1.00      | ~ v4_orders_2(X0)
% 2.44/1.00      | ~ v5_orders_2(X0)
% 2.44/1.00      | ~ l1_orders_2(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_291,plain,
% 2.44/1.00      ( ~ r2_orders_2(X0,X1,X2)
% 2.44/1.00      | ~ r2_orders_2(X0,X3,X1)
% 2.44/1.00      | r2_orders_2(X0,X3,X2)
% 2.44/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.44/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/1.00      | ~ v4_orders_2(X0)
% 2.44/1.00      | ~ v5_orders_2(X0)
% 2.44/1.00      | ~ l1_orders_2(X0) ),
% 2.44/1.00      inference(resolution,[status(thm)],[c_2,c_10]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_619,plain,
% 2.44/1.00      ( ~ r2_orders_2(X0,X1,X2)
% 2.44/1.00      | ~ r2_orders_2(X0,X3,X1)
% 2.44/1.00      | r2_orders_2(X0,X3,X2)
% 2.44/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.44/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/1.00      | ~ v4_orders_2(X0)
% 2.44/1.00      | ~ l1_orders_2(X0)
% 2.44/1.00      | sK1 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_291,c_24]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_620,plain,
% 2.44/1.00      ( ~ r2_orders_2(sK1,X0,X1)
% 2.44/1.00      | ~ r2_orders_2(sK1,X2,X0)
% 2.44/1.00      | r2_orders_2(sK1,X2,X1)
% 2.44/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.44/1.00      | ~ v4_orders_2(sK1)
% 2.44/1.00      | ~ l1_orders_2(sK1) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_619]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_622,plain,
% 2.44/1.00      ( ~ r2_orders_2(sK1,X0,X1)
% 2.44/1.00      | ~ r2_orders_2(sK1,X2,X0)
% 2.44/1.00      | r2_orders_2(sK1,X2,X1)
% 2.44/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_620,c_25,c_23]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_623,plain,
% 2.44/1.00      ( ~ r2_orders_2(sK1,X0,X1)
% 2.44/1.00      | ~ r2_orders_2(sK1,X2,X0)
% 2.44/1.00      | r2_orders_2(sK1,X2,X1)
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_622]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1125,plain,
% 2.44/1.00      ( ~ r2_orders_2(sK1,X0_49,X1_49)
% 2.44/1.00      | ~ r2_orders_2(sK1,X2_49,X0_49)
% 2.44/1.00      | r2_orders_2(sK1,X2_49,X1_49)
% 2.44/1.00      | ~ m1_subset_1(X0_49,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X1_49,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X2_49,u1_struct_0(sK1)) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_623]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1513,plain,
% 2.44/1.00      ( r2_orders_2(sK1,X0_49,X1_49) != iProver_top
% 2.44/1.00      | r2_orders_2(sK1,X2_49,X0_49) != iProver_top
% 2.44/1.00      | r2_orders_2(sK1,X2_49,X1_49) = iProver_top
% 2.44/1.00      | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | m1_subset_1(X1_49,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | m1_subset_1(X2_49,u1_struct_0(sK1)) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1125]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2903,plain,
% 2.44/1.00      ( sK4 = k1_xboole_0
% 2.44/1.00      | r2_orders_2(sK1,X0_49,X1_49) != iProver_top
% 2.44/1.00      | r2_orders_2(sK1,X0_49,sK0(sK1,sK4,sK5)) = iProver_top
% 2.44/1.00      | r2_hidden(X1_49,sK5) != iProver_top
% 2.44/1.00      | m1_subset_1(X1_49,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1)) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_2893,c_1513]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3296,plain,
% 2.44/1.00      ( m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | m1_subset_1(X1_49,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | r2_hidden(X1_49,sK5) != iProver_top
% 2.44/1.00      | r2_orders_2(sK1,X0_49,sK0(sK1,sK4,sK5)) = iProver_top
% 2.44/1.00      | r2_orders_2(sK1,X0_49,X1_49) != iProver_top
% 2.44/1.00      | sK4 = k1_xboole_0 ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_2903,c_35,c_36,c_40,c_1896,c_2344,c_2365]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3297,plain,
% 2.44/1.00      ( sK4 = k1_xboole_0
% 2.44/1.00      | r2_orders_2(sK1,X0_49,X1_49) != iProver_top
% 2.44/1.00      | r2_orders_2(sK1,X0_49,sK0(sK1,sK4,sK5)) = iProver_top
% 2.44/1.00      | r2_hidden(X1_49,sK5) != iProver_top
% 2.44/1.00      | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | m1_subset_1(X1_49,u1_struct_0(sK1)) != iProver_top ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_3296]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3306,plain,
% 2.44/1.00      ( sK4 = k1_xboole_0
% 2.44/1.00      | r2_orders_2(sK1,sK2,sK0(sK1,sK4,sK5)) = iProver_top
% 2.44/1.00      | r2_hidden(sK3,sK5) != iProver_top
% 2.44/1.00      | m1_subset_1(sK3,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_1499,c_3297]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_22,negated_conjecture,
% 2.44/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.44/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_33,plain,
% 2.44/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_21,negated_conjecture,
% 2.44/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.44/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_34,plain,
% 2.44/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_17,negated_conjecture,
% 2.44/1.00      ( r2_hidden(sK2,sK4) ),
% 2.44/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_16,negated_conjecture,
% 2.44/1.00      ( r2_hidden(sK3,sK5) ),
% 2.44/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_39,plain,
% 2.44/1.00      ( r2_hidden(sK3,sK5) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_14,negated_conjecture,
% 2.44/1.00      ( ~ r2_hidden(sK2,sK5) ),
% 2.44/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1158,plain,
% 2.44/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1145]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1148,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0_49,X0_50)
% 2.44/1.00      | m1_subset_1(X1_49,X0_50)
% 2.44/1.00      | X1_49 != X0_49 ),
% 2.44/1.00      theory(equality) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1738,plain,
% 2.44/1.00      ( m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | X0_49 != sK4 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1148]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1740,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | k1_xboole_0 != sK4 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1738]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0,X1,k1_xboole_0)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ v3_orders_2(X1)
% 2.44/1.00      | ~ v4_orders_2(X1)
% 2.44/1.00      | ~ v5_orders_2(X1)
% 2.44/1.00      | ~ l1_orders_2(X1)
% 2.44/1.00      | k1_xboole_0 = X0 ),
% 2.44/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_516,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0,X1,k1_xboole_0)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ v4_orders_2(X1)
% 2.44/1.00      | ~ v5_orders_2(X1)
% 2.44/1.00      | ~ l1_orders_2(X1)
% 2.44/1.00      | sK1 != X1
% 2.44/1.00      | k1_xboole_0 = X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_26]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_517,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0,sK1,k1_xboole_0)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | v2_struct_0(sK1)
% 2.44/1.00      | ~ v4_orders_2(sK1)
% 2.44/1.00      | ~ v5_orders_2(sK1)
% 2.44/1.00      | ~ l1_orders_2(sK1)
% 2.44/1.00      | k1_xboole_0 = X0 ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_516]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_521,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0,sK1,k1_xboole_0)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | k1_xboole_0 = X0 ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_517,c_27,c_25,c_24,c_23]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1127,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0_49,sK1,k1_xboole_0)
% 2.44/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | k1_xboole_0 = X0_49 ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_521]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1779,plain,
% 2.44/1.00      ( ~ m1_orders_2(sK5,sK1,k1_xboole_0)
% 2.44/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | k1_xboole_0 = sK5 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1127]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1805,plain,
% 2.44/1.00      ( X0_49 != X1_49 | X0_49 = sK4 | sK4 != X1_49 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1146]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1806,plain,
% 2.44/1.00      ( sK4 != k1_xboole_0
% 2.44/1.00      | k1_xboole_0 = sK4
% 2.44/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1805]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2024,plain,
% 2.44/1.00      ( X0_49 != X1_49 | sK5 != X1_49 | sK5 = X0_49 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1146]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2281,plain,
% 2.44/1.00      ( X0_49 != sK5 | sK5 = X0_49 | sK5 != sK5 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_2024]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2283,plain,
% 2.44/1.00      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_2281]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2282,plain,
% 2.44/1.00      ( sK5 = sK5 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1145]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2544,plain,
% 2.44/1.00      ( sK2 = sK2 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1145]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1149,plain,
% 2.44/1.00      ( ~ m1_orders_2(X0_49,X0_48,X1_49)
% 2.44/1.00      | m1_orders_2(X2_49,X0_48,X3_49)
% 2.44/1.00      | X2_49 != X0_49
% 2.44/1.00      | X3_49 != X1_49 ),
% 2.44/1.00      theory(equality) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1768,plain,
% 2.44/1.00      ( m1_orders_2(X0_49,sK1,X1_49)
% 2.44/1.00      | ~ m1_orders_2(sK5,sK1,sK4)
% 2.44/1.00      | X1_49 != sK4
% 2.44/1.00      | X0_49 != sK5 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1149]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2772,plain,
% 2.44/1.00      ( ~ m1_orders_2(sK5,sK1,sK4)
% 2.44/1.00      | m1_orders_2(sK5,sK1,k1_xboole_0)
% 2.44/1.00      | sK5 != sK5
% 2.44/1.00      | k1_xboole_0 != sK4 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1768]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3013,plain,
% 2.44/1.00      ( sK4 != X0_49 | sK5 != X0_49 | sK5 = sK4 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1805]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3016,plain,
% 2.44/1.00      ( sK4 != k1_xboole_0 | sK5 = sK4 | sK5 != k1_xboole_0 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_3013]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1151,plain,
% 2.44/1.00      ( ~ r2_hidden(X0_49,X1_49)
% 2.44/1.00      | r2_hidden(X2_49,X3_49)
% 2.44/1.00      | X2_49 != X0_49
% 2.44/1.00      | X3_49 != X1_49 ),
% 2.44/1.00      theory(equality) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1758,plain,
% 2.44/1.00      ( r2_hidden(X0_49,X1_49)
% 2.44/1.00      | ~ r2_hidden(sK2,sK4)
% 2.44/1.00      | X1_49 != sK4
% 2.44/1.00      | X0_49 != sK2 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1151]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2952,plain,
% 2.44/1.00      ( r2_hidden(sK2,X0_49)
% 2.44/1.00      | ~ r2_hidden(sK2,sK4)
% 2.44/1.00      | X0_49 != sK4
% 2.44/1.00      | sK2 != sK2 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1758]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3331,plain,
% 2.44/1.00      ( ~ r2_hidden(sK2,sK4)
% 2.44/1.00      | r2_hidden(sK2,sK5)
% 2.44/1.00      | sK5 != sK4
% 2.44/1.00      | sK2 != sK2 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_2952]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3402,plain,
% 2.44/1.00      ( r2_orders_2(sK1,sK2,sK0(sK1,sK4,sK5)) = iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_3306,c_33,c_34,c_20,c_19,c_17,c_39,c_15,c_14,c_1158,
% 2.44/1.00                 c_1740,c_1779,c_1806,c_2283,c_2282,c_2544,c_2772,c_3016,
% 2.44/1.00                 c_3331]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_11,plain,
% 2.44/1.00      ( ~ r2_orders_2(X0,X1,X2)
% 2.44/1.00      | ~ r2_hidden(X1,X3)
% 2.44/1.00      | r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 2.44/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ v3_orders_2(X0)
% 2.44/1.00      | ~ v4_orders_2(X0)
% 2.44/1.00      | ~ v5_orders_2(X0)
% 2.44/1.00      | ~ l1_orders_2(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_361,plain,
% 2.44/1.00      ( ~ r2_orders_2(X0,X1,X2)
% 2.44/1.00      | ~ r2_hidden(X1,X3)
% 2.44/1.00      | r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 2.44/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.44/1.00      | v2_struct_0(X0)
% 2.44/1.00      | ~ v4_orders_2(X0)
% 2.44/1.00      | ~ v5_orders_2(X0)
% 2.44/1.00      | ~ l1_orders_2(X0)
% 2.44/1.00      | sK1 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_362,plain,
% 2.44/1.00      ( ~ r2_orders_2(sK1,X0,X1)
% 2.44/1.00      | ~ r2_hidden(X0,X2)
% 2.44/1.00      | r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.44/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.44/1.00      | v2_struct_0(sK1)
% 2.44/1.00      | ~ v4_orders_2(sK1)
% 2.44/1.00      | ~ v5_orders_2(sK1)
% 2.44/1.00      | ~ l1_orders_2(sK1) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_361]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_366,plain,
% 2.44/1.00      ( ~ r2_orders_2(sK1,X0,X1)
% 2.44/1.00      | ~ r2_hidden(X0,X2)
% 2.44/1.00      | r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.44/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_362,c_27,c_25,c_24,c_23]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_367,plain,
% 2.44/1.00      ( ~ r2_orders_2(sK1,X0,X1)
% 2.44/1.00      | ~ r2_hidden(X0,X2)
% 2.44/1.00      | r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.44/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_366]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1133,plain,
% 2.44/1.00      ( ~ r2_orders_2(sK1,X0_49,X1_49)
% 2.44/1.00      | ~ r2_hidden(X0_49,X2_49)
% 2.44/1.00      | r2_hidden(X0_49,k3_orders_2(sK1,X2_49,X1_49))
% 2.44/1.00      | ~ m1_subset_1(X2_49,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.44/1.00      | ~ m1_subset_1(X0_49,u1_struct_0(sK1))
% 2.44/1.00      | ~ m1_subset_1(X1_49,u1_struct_0(sK1)) ),
% 2.44/1.00      inference(subtyping,[status(esa)],[c_367]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1505,plain,
% 2.44/1.00      ( r2_orders_2(sK1,X0_49,X1_49) != iProver_top
% 2.44/1.00      | r2_hidden(X0_49,X2_49) != iProver_top
% 2.44/1.00      | r2_hidden(X0_49,k3_orders_2(sK1,X2_49,X1_49)) = iProver_top
% 2.44/1.00      | m1_subset_1(X2_49,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.44/1.00      | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | m1_subset_1(X1_49,u1_struct_0(sK1)) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_1133]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2692,plain,
% 2.44/1.00      ( sK4 = k1_xboole_0
% 2.44/1.00      | r2_orders_2(sK1,X0_49,sK0(sK1,sK4,sK5)) != iProver_top
% 2.44/1.00      | r2_hidden(X0_49,sK4) != iProver_top
% 2.44/1.00      | r2_hidden(X0_49,sK5) = iProver_top
% 2.44/1.00      | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | m1_subset_1(sK0(sK1,sK4,sK5),u1_struct_0(sK1)) != iProver_top
% 2.44/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_2687,c_1505]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3282,plain,
% 2.44/1.00      ( sK4 = k1_xboole_0
% 2.44/1.00      | r2_orders_2(sK1,X0_49,sK0(sK1,sK4,sK5)) != iProver_top
% 2.44/1.00      | r2_hidden(X0_49,sK4) != iProver_top
% 2.44/1.00      | r2_hidden(X0_49,sK5) = iProver_top
% 2.44/1.00      | m1_subset_1(X0_49,u1_struct_0(sK1)) != iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_2692,c_35,c_36,c_40,c_1896,c_2344,c_2365]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3409,plain,
% 2.44/1.00      ( sK4 = k1_xboole_0
% 2.44/1.00      | r2_hidden(sK2,sK4) != iProver_top
% 2.44/1.00      | r2_hidden(sK2,sK5) = iProver_top
% 2.44/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_3402,c_3282]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_41,plain,
% 2.44/1.00      ( r2_hidden(sK2,sK5) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_38,plain,
% 2.44/1.00      ( r2_hidden(sK2,sK4) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(contradiction,plain,
% 2.44/1.00      ( $false ),
% 2.44/1.00      inference(minisat,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_3409,c_3331,c_3016,c_2772,c_2544,c_2282,c_2283,c_1806,
% 2.44/1.00                 c_1779,c_1740,c_1158,c_41,c_14,c_15,c_38,c_17,c_19,c_20,
% 2.44/1.00                 c_33]) ).
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  ------                               Statistics
% 2.44/1.00  
% 2.44/1.00  ------ General
% 2.44/1.00  
% 2.44/1.00  abstr_ref_over_cycles:                  0
% 2.44/1.00  abstr_ref_under_cycles:                 0
% 2.44/1.00  gc_basic_clause_elim:                   0
% 2.44/1.00  forced_gc_time:                         0
% 2.44/1.00  parsing_time:                           0.013
% 2.44/1.00  unif_index_cands_time:                  0.
% 2.44/1.00  unif_index_add_time:                    0.
% 2.44/1.00  orderings_time:                         0.
% 2.44/1.00  out_proof_time:                         0.015
% 2.44/1.00  total_time:                             0.167
% 2.44/1.00  num_of_symbols:                         51
% 2.44/1.00  num_of_terms:                           2315
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing
% 2.44/1.00  
% 2.44/1.00  num_of_splits:                          0
% 2.44/1.00  num_of_split_atoms:                     0
% 2.44/1.00  num_of_reused_defs:                     0
% 2.44/1.00  num_eq_ax_congr_red:                    21
% 2.44/1.00  num_of_sem_filtered_clauses:            1
% 2.44/1.00  num_of_subtypes:                        3
% 2.44/1.00  monotx_restored_types:                  0
% 2.44/1.00  sat_num_of_epr_types:                   0
% 2.44/1.00  sat_num_of_non_cyclic_types:            0
% 2.44/1.00  sat_guarded_non_collapsed_types:        1
% 2.44/1.00  num_pure_diseq_elim:                    0
% 2.44/1.00  simp_replaced_by:                       0
% 2.44/1.00  res_preprocessed:                       103
% 2.44/1.00  prep_upred:                             0
% 2.44/1.00  prep_unflattend:                        55
% 2.44/1.00  smt_new_axioms:                         0
% 2.44/1.00  pred_elim_cands:                        4
% 2.44/1.00  pred_elim:                              6
% 2.44/1.00  pred_elim_cl:                           8
% 2.44/1.00  pred_elim_cycles:                       8
% 2.44/1.00  merged_defs:                            0
% 2.44/1.00  merged_defs_ncl:                        0
% 2.44/1.00  bin_hyper_res:                          0
% 2.44/1.00  prep_cycles:                            4
% 2.44/1.00  pred_elim_time:                         0.018
% 2.44/1.00  splitting_time:                         0.
% 2.44/1.00  sem_filter_time:                        0.
% 2.44/1.00  monotx_time:                            0.
% 2.44/1.00  subtype_inf_time:                       0.
% 2.44/1.00  
% 2.44/1.00  ------ Problem properties
% 2.44/1.00  
% 2.44/1.00  clauses:                                20
% 2.44/1.00  conjectures:                            9
% 2.44/1.00  epr:                                    5
% 2.44/1.00  horn:                                   16
% 2.44/1.00  ground:                                 10
% 2.44/1.00  unary:                                  9
% 2.44/1.00  binary:                                 2
% 2.44/1.00  lits:                                   60
% 2.44/1.00  lits_eq:                                6
% 2.44/1.00  fd_pure:                                0
% 2.44/1.00  fd_pseudo:                              0
% 2.44/1.00  fd_cond:                                4
% 2.44/1.00  fd_pseudo_cond:                         0
% 2.44/1.00  ac_symbols:                             0
% 2.44/1.00  
% 2.44/1.00  ------ Propositional Solver
% 2.44/1.00  
% 2.44/1.00  prop_solver_calls:                      27
% 2.44/1.00  prop_fast_solver_calls:                 1159
% 2.44/1.00  smt_solver_calls:                       0
% 2.44/1.00  smt_fast_solver_calls:                  0
% 2.44/1.00  prop_num_of_clauses:                    948
% 2.44/1.00  prop_preprocess_simplified:             3440
% 2.44/1.00  prop_fo_subsumed:                       78
% 2.44/1.00  prop_solver_time:                       0.
% 2.44/1.00  smt_solver_time:                        0.
% 2.44/1.00  smt_fast_solver_time:                   0.
% 2.44/1.00  prop_fast_solver_time:                  0.
% 2.44/1.00  prop_unsat_core_time:                   0.
% 2.44/1.00  
% 2.44/1.00  ------ QBF
% 2.44/1.00  
% 2.44/1.00  qbf_q_res:                              0
% 2.44/1.00  qbf_num_tautologies:                    0
% 2.44/1.00  qbf_prep_cycles:                        0
% 2.44/1.00  
% 2.44/1.00  ------ BMC1
% 2.44/1.00  
% 2.44/1.00  bmc1_current_bound:                     -1
% 2.44/1.00  bmc1_last_solved_bound:                 -1
% 2.44/1.00  bmc1_unsat_core_size:                   -1
% 2.44/1.00  bmc1_unsat_core_parents_size:           -1
% 2.44/1.00  bmc1_merge_next_fun:                    0
% 2.44/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation
% 2.44/1.00  
% 2.44/1.00  inst_num_of_clauses:                    231
% 2.44/1.00  inst_num_in_passive:                    33
% 2.44/1.00  inst_num_in_active:                     171
% 2.44/1.00  inst_num_in_unprocessed:                27
% 2.44/1.00  inst_num_of_loops:                      220
% 2.44/1.00  inst_num_of_learning_restarts:          0
% 2.44/1.00  inst_num_moves_active_passive:          45
% 2.44/1.00  inst_lit_activity:                      0
% 2.44/1.00  inst_lit_activity_moves:                0
% 2.44/1.00  inst_num_tautologies:                   0
% 2.44/1.00  inst_num_prop_implied:                  0
% 2.44/1.00  inst_num_existing_simplified:           0
% 2.44/1.00  inst_num_eq_res_simplified:             0
% 2.44/1.00  inst_num_child_elim:                    0
% 2.44/1.00  inst_num_of_dismatching_blockings:      31
% 2.44/1.00  inst_num_of_non_proper_insts:           205
% 2.44/1.00  inst_num_of_duplicates:                 0
% 2.44/1.00  inst_inst_num_from_inst_to_res:         0
% 2.44/1.00  inst_dismatching_checking_time:         0.
% 2.44/1.00  
% 2.44/1.00  ------ Resolution
% 2.44/1.00  
% 2.44/1.00  res_num_of_clauses:                     0
% 2.44/1.00  res_num_in_passive:                     0
% 2.44/1.00  res_num_in_active:                      0
% 2.44/1.00  res_num_of_loops:                       107
% 2.44/1.00  res_forward_subset_subsumed:            34
% 2.44/1.00  res_backward_subset_subsumed:           0
% 2.44/1.00  res_forward_subsumed:                   1
% 2.44/1.00  res_backward_subsumed:                  0
% 2.44/1.00  res_forward_subsumption_resolution:     0
% 2.44/1.00  res_backward_subsumption_resolution:    0
% 2.44/1.00  res_clause_to_clause_subsumption:       174
% 2.44/1.00  res_orphan_elimination:                 0
% 2.44/1.00  res_tautology_del:                      25
% 2.44/1.00  res_num_eq_res_simplified:              0
% 2.44/1.00  res_num_sel_changes:                    0
% 2.44/1.00  res_moves_from_active_to_pass:          0
% 2.44/1.00  
% 2.44/1.00  ------ Superposition
% 2.44/1.00  
% 2.44/1.00  sup_time_total:                         0.
% 2.44/1.00  sup_time_generating:                    0.
% 2.44/1.00  sup_time_sim_full:                      0.
% 2.44/1.00  sup_time_sim_immed:                     0.
% 2.44/1.00  
% 2.44/1.00  sup_num_of_clauses:                     48
% 2.44/1.00  sup_num_in_active:                      42
% 2.44/1.00  sup_num_in_passive:                     6
% 2.44/1.00  sup_num_of_loops:                       42
% 2.44/1.00  sup_fw_superposition:                   21
% 2.44/1.00  sup_bw_superposition:                   15
% 2.44/1.00  sup_immediate_simplified:               5
% 2.44/1.00  sup_given_eliminated:                   1
% 2.44/1.00  comparisons_done:                       0
% 2.44/1.00  comparisons_avoided:                    13
% 2.44/1.00  
% 2.44/1.00  ------ Simplifications
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  sim_fw_subset_subsumed:                 4
% 2.44/1.00  sim_bw_subset_subsumed:                 0
% 2.44/1.00  sim_fw_subsumed:                        1
% 2.44/1.00  sim_bw_subsumed:                        2
% 2.44/1.00  sim_fw_subsumption_res:                 0
% 2.44/1.00  sim_bw_subsumption_res:                 0
% 2.44/1.00  sim_tautology_del:                      2
% 2.44/1.00  sim_eq_tautology_del:                   0
% 2.44/1.00  sim_eq_res_simp:                        0
% 2.44/1.00  sim_fw_demodulated:                     0
% 2.44/1.00  sim_bw_demodulated:                     0
% 2.44/1.00  sim_light_normalised:                   0
% 2.44/1.00  sim_joinable_taut:                      0
% 2.44/1.00  sim_joinable_simp:                      0
% 2.44/1.00  sim_ac_normalised:                      0
% 2.44/1.00  sim_smt_subsumption:                    0
% 2.44/1.00  
%------------------------------------------------------------------------------
