%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:40 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :  143 (1529 expanded)
%              Number of clauses        :  103 ( 332 expanded)
%              Number of leaves         :   13 ( 524 expanded)
%              Depth                    :   21
%              Number of atoms          :  805 (13667 expanded)
%              Number of equality atoms :  190 (2151 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f46,plain,(
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
    inference(equality_resolution,[],[f28])).

fof(f4,conjecture,(
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
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( m1_orders_2(X2,X0,X1)
                    & m1_orders_2(X1,X0,X2)
                    & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( m1_orders_2(X2,X0,X1)
          & m1_orders_2(X1,X0,X2)
          & k1_xboole_0 != X1
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( m1_orders_2(sK3,X0,X1)
        & m1_orders_2(X1,X0,sK3)
        & k1_xboole_0 != X1
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( m1_orders_2(X2,X0,sK2)
            & m1_orders_2(sK2,X0,X2)
            & k1_xboole_0 != sK2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( m1_orders_2(X2,X0,X1)
                & m1_orders_2(X1,X0,X2)
                & k1_xboole_0 != X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,sK1,X1)
              & m1_orders_2(X1,sK1,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( m1_orders_2(sK3,sK1,sK2)
    & m1_orders_2(sK2,sK1,sK3)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f22,f21,f20])).

fof(f38,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f26,plain,(
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

fof(f42,plain,(
    m1_orders_2(sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f23])).

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
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ r2_hidden(X1,k3_orders_2(X0,X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
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
              ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
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

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

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
    inference(nnf_transformation,[],[f9])).

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

fof(f31,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
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

fof(f43,plain,(
    m1_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1041,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_2581,plain,
    ( sK0(sK1,sK3,sK2) = sK0(sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_1046,plain,
    ( ~ r2_hidden(X0_45,X1_45)
    | r2_hidden(X2_45,X3_45)
    | X2_45 != X0_45
    | X3_45 != X1_45 ),
    theory(equality)).

cnf(c_1749,plain,
    ( r2_hidden(X0_45,X1_45)
    | ~ r2_hidden(sK0(sK1,sK3,sK2),sK3)
    | X0_45 != sK0(sK1,sK3,sK2)
    | X1_45 != sK3 ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_2148,plain,
    ( r2_hidden(X0_45,k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK3)))
    | ~ r2_hidden(sK0(sK1,sK3,sK2),sK3)
    | X0_45 != sK0(sK1,sK3,sK2)
    | k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_1749])).

cnf(c_2580,plain,
    ( r2_hidden(sK0(sK1,sK3,sK2),k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK3)))
    | ~ r2_hidden(sK0(sK1,sK3,sK2),sK3)
    | sK0(sK1,sK3,sK2) != sK0(sK1,sK3,sK2)
    | k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_2148])).

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
    inference(cnf_transformation,[],[f46])).

cnf(c_15,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_388,plain,
    ( ~ m1_orders_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_389,plain,
    ( ~ m1_orders_2(X0,sK1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_18,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_17,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_16,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_393,plain,
    ( ~ m1_orders_2(X0,sK1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_19,c_18,c_17,c_16])).

cnf(c_1028,plain,
    ( ~ m1_orders_2(X0_45,sK1,k1_xboole_0)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0_45 ),
    inference(subtyping,[status(esa)],[c_393])).

cnf(c_2456,plain,
    ( ~ m1_orders_2(k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)),sK1,k1_xboole_0)
    | ~ m1_subset_1(k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1035,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1279,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1035])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1036,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1278,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1036])).

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
    inference(cnf_transformation,[],[f26])).

cnf(c_361,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_362,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_366,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_362,c_19,c_18,c_17,c_16])).

cnf(c_367,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_366])).

cnf(c_1029,plain,
    ( ~ m1_orders_2(X0_45,sK1,X1_45)
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,X1_45,sK0(sK1,X1_45,X0_45)) = X0_45
    | k1_xboole_0 = X1_45 ),
    inference(subtyping,[status(esa)],[c_367])).

cnf(c_1285,plain,
    ( k3_orders_2(sK1,X0_45,sK0(sK1,X0_45,X1_45)) = X1_45
    | k1_xboole_0 = X0_45
    | m1_orders_2(X1_45,sK1,X0_45) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1029])).

cnf(c_1820,plain,
    ( k3_orders_2(sK1,sK3,sK0(sK1,sK3,X0_45)) = X0_45
    | sK3 = k1_xboole_0
    | m1_orders_2(X0_45,sK1,sK3) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1278,c_1285])).

cnf(c_26,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,negated_conjecture,
    ( m1_orders_2(sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1037,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1412,plain,
    ( ~ m1_orders_2(sK2,sK1,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_1044,plain,
    ( ~ m1_subset_1(X0_45,X0_47)
    | m1_subset_1(X1_45,X0_47)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_1440,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_45 != sK3 ),
    inference(instantiation,[status(thm)],[c_1044])).

cnf(c_1442,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1440])).

cnf(c_1485,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_1540,plain,
    ( ~ m1_orders_2(X0_45,sK1,sK3)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,sK3,sK0(sK1,sK3,X0_45)) = X0_45
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_1551,plain,
    ( k3_orders_2(sK1,sK3,sK0(sK1,sK3,X0_45)) = X0_45
    | k1_xboole_0 = sK3
    | m1_orders_2(X0_45,sK1,sK3) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1540])).

cnf(c_1043,plain,
    ( ~ m1_orders_2(X0_45,X0_46,X1_45)
    | m1_orders_2(X2_45,X0_46,X3_45)
    | X2_45 != X0_45
    | X3_45 != X1_45 ),
    theory(equality)).

cnf(c_1451,plain,
    ( m1_orders_2(X0_45,sK1,X1_45)
    | ~ m1_orders_2(sK2,sK1,sK3)
    | X0_45 != sK2
    | X1_45 != sK3 ),
    inference(instantiation,[status(thm)],[c_1043])).

cnf(c_1557,plain,
    ( m1_orders_2(sK2,sK1,X0_45)
    | ~ m1_orders_2(sK2,sK1,sK3)
    | X0_45 != sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_1560,plain,
    ( ~ m1_orders_2(sK2,sK1,sK3)
    | m1_orders_2(sK2,sK1,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1557])).

cnf(c_1940,plain,
    ( k3_orders_2(sK1,sK3,sK0(sK1,sK3,X0_45)) = X0_45
    | m1_orders_2(X0_45,sK1,sK3) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1820,c_14,c_13,c_26,c_11,c_1037,c_1412,c_1442,c_1485,c_1551,c_1560])).

cnf(c_1950,plain,
    ( k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)) = sK2
    | m1_orders_2(sK2,sK1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1940])).

cnf(c_1729,plain,
    ( ~ m1_orders_2(sK2,sK1,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)) = sK2
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1540])).

cnf(c_2048,plain,
    ( k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1950,c_14,c_13,c_11,c_1037,c_1412,c_1442,c_1485,c_1560,c_1729])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k3_orders_2(X1,X2,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_286,plain,
    ( ~ r2_hidden(X0,k3_orders_2(X1,X2,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_287,plain,
    ( ~ r2_hidden(X0,k3_orders_2(sK1,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_291,plain,
    ( ~ r2_hidden(X0,k3_orders_2(sK1,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_287,c_19,c_18,c_17,c_16])).

cnf(c_1032,plain,
    ( ~ r2_hidden(X0_45,k3_orders_2(sK1,X1_45,X0_45))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_45,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_291])).

cnf(c_1282,plain,
    ( r2_hidden(X0_45,k3_orders_2(sK1,X1_45,X0_45)) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1032])).

cnf(c_2053,plain,
    ( r2_hidden(sK0(sK1,sK3,sK2),sK2) != iProver_top
    | m1_subset_1(sK0(sK1,sK3,sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2048,c_1282])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_27,plain,
    ( m1_orders_2(sK2,sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

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
    inference(cnf_transformation,[],[f24])).

cnf(c_307,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_308,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_312,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_308,c_19,c_18,c_17,c_16])).

cnf(c_313,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_312])).

cnf(c_1031,plain,
    ( ~ m1_orders_2(X0_45,sK1,X1_45)
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X1_45,X0_45),u1_struct_0(sK1))
    | k1_xboole_0 = X1_45 ),
    inference(subtyping,[status(esa)],[c_313])).

cnf(c_1542,plain,
    ( ~ m1_orders_2(X0_45,sK1,sK3)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,sK3,X0_45),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_1700,plain,
    ( ~ m1_orders_2(sK2,sK1,sK3)
    | m1_subset_1(sK0(sK1,sK3,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1542])).

cnf(c_1701,plain,
    ( k1_xboole_0 = sK3
    | m1_orders_2(sK2,sK1,sK3) != iProver_top
    | m1_subset_1(sK0(sK1,sK3,sK2),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1700])).

cnf(c_2315,plain,
    ( r2_hidden(sK0(sK1,sK3,sK2),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2053,c_14,c_25,c_13,c_26,c_11,c_27,c_1037,c_1412,c_1442,c_1485,c_1560,c_1701])).

cnf(c_2317,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,sK2),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2315])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_441,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_442,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_444,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_442,c_19,c_18,c_17,c_16])).

cnf(c_445,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_444])).

cnf(c_1026,plain,
    ( r2_hidden(X0_45,X1_45)
    | ~ r2_hidden(X0_45,k3_orders_2(sK1,X1_45,X2_45))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2_45,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_45,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_445])).

cnf(c_1507,plain,
    ( r2_hidden(X0_45,X1_45)
    | ~ r2_hidden(X0_45,k3_orders_2(sK1,X1_45,sK0(sK1,sK2,sK3)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_45,u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK1,sK2,sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_1765,plain,
    ( r2_hidden(sK0(sK1,sK3,sK2),X0_45)
    | ~ r2_hidden(sK0(sK1,sK3,sK2),k3_orders_2(sK1,X0_45,sK0(sK1,sK2,sK3)))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK1,sK3,sK2),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_2124,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,sK2),k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK3)))
    | r2_hidden(sK0(sK1,sK3,sK2),sK2)
    | ~ m1_subset_1(sK0(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK1,sK3,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1765])).

cnf(c_1042,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_1438,plain,
    ( sK2 != X0_45
    | k1_xboole_0 != X0_45
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1042])).

cnf(c_1895,plain,
    ( sK2 != k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2))
    | k1_xboole_0 != k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1438])).

cnf(c_1459,plain,
    ( X0_45 != X1_45
    | sK2 != X1_45
    | sK2 = X0_45 ),
    inference(instantiation,[status(thm)],[c_1042])).

cnf(c_1609,plain,
    ( X0_45 != sK2
    | sK2 = X0_45
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_1783,plain,
    ( k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)) != sK2
    | sK2 = k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1609])).

cnf(c_1784,plain,
    ( m1_orders_2(k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)),sK1,X0_45)
    | ~ m1_orders_2(sK2,sK1,sK3)
    | X0_45 != sK3
    | k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_1789,plain,
    ( m1_orders_2(k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)),sK1,k1_xboole_0)
    | ~ m1_orders_2(sK2,sK1,sK3)
    | k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)) != sK2
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1784])).

cnf(c_1445,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_45 != sK2 ),
    inference(instantiation,[status(thm)],[c_1044])).

cnf(c_1785,plain,
    ( m1_subset_1(k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_4,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | r2_hidden(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_334,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | r2_hidden(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_335,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | r2_hidden(sK0(sK1,X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_339,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | r2_hidden(sK0(sK1,X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_19,c_18,c_17,c_16])).

cnf(c_340,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | r2_hidden(sK0(sK1,X1,X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_339])).

cnf(c_1030,plain,
    ( ~ m1_orders_2(X0_45,sK1,X1_45)
    | r2_hidden(sK0(sK1,X1_45,X0_45),X1_45)
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X1_45 ),
    inference(subtyping,[status(esa)],[c_340])).

cnf(c_1541,plain,
    ( ~ m1_orders_2(X0_45,sK1,sK3)
    | r2_hidden(sK0(sK1,sK3,X0_45),sK3)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_1697,plain,
    ( ~ m1_orders_2(sK2,sK1,sK3)
    | r2_hidden(sK0(sK1,sK3,sK2),sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1541])).

cnf(c_1428,plain,
    ( ~ m1_orders_2(X0_45,sK1,sK2)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,sK2,sK0(sK1,sK2,X0_45)) = X0_45
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_1499,plain,
    ( ~ m1_orders_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK3)) = sK3
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1428])).

cnf(c_10,negated_conjecture,
    ( m1_orders_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1))
    | sK2 != X0
    | sK1 != sK1
    | sK3 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_313])).

cnf(c_535,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2581,c_2580,c_2456,c_2317,c_2124,c_1950,c_1895,c_1783,c_1789,c_1785,c_1700,c_1697,c_1499,c_1485,c_1442,c_1037,c_535,c_10,c_27,c_11,c_12,c_13,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:56:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.88/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.00  
% 1.88/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.88/1.00  
% 1.88/1.00  ------  iProver source info
% 1.88/1.00  
% 1.88/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.88/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.88/1.00  git: non_committed_changes: false
% 1.88/1.00  git: last_make_outside_of_git: false
% 1.88/1.00  
% 1.88/1.00  ------ 
% 1.88/1.00  
% 1.88/1.00  ------ Input Options
% 1.88/1.00  
% 1.88/1.00  --out_options                           all
% 1.88/1.00  --tptp_safe_out                         true
% 1.88/1.00  --problem_path                          ""
% 1.88/1.00  --include_path                          ""
% 1.88/1.00  --clausifier                            res/vclausify_rel
% 1.88/1.00  --clausifier_options                    --mode clausify
% 1.88/1.00  --stdin                                 false
% 1.88/1.00  --stats_out                             all
% 1.88/1.00  
% 1.88/1.00  ------ General Options
% 1.88/1.00  
% 1.88/1.00  --fof                                   false
% 1.88/1.00  --time_out_real                         305.
% 1.88/1.00  --time_out_virtual                      -1.
% 1.88/1.00  --symbol_type_check                     false
% 1.88/1.00  --clausify_out                          false
% 1.88/1.00  --sig_cnt_out                           false
% 1.88/1.00  --trig_cnt_out                          false
% 1.88/1.00  --trig_cnt_out_tolerance                1.
% 1.88/1.00  --trig_cnt_out_sk_spl                   false
% 1.88/1.00  --abstr_cl_out                          false
% 1.88/1.00  
% 1.88/1.00  ------ Global Options
% 1.88/1.00  
% 1.88/1.00  --schedule                              default
% 1.88/1.00  --add_important_lit                     false
% 1.88/1.00  --prop_solver_per_cl                    1000
% 1.88/1.00  --min_unsat_core                        false
% 1.88/1.00  --soft_assumptions                      false
% 1.88/1.00  --soft_lemma_size                       3
% 1.88/1.00  --prop_impl_unit_size                   0
% 1.88/1.00  --prop_impl_unit                        []
% 1.88/1.00  --share_sel_clauses                     true
% 1.88/1.00  --reset_solvers                         false
% 1.88/1.00  --bc_imp_inh                            [conj_cone]
% 1.88/1.00  --conj_cone_tolerance                   3.
% 1.88/1.00  --extra_neg_conj                        none
% 1.88/1.00  --large_theory_mode                     true
% 1.88/1.00  --prolific_symb_bound                   200
% 1.88/1.00  --lt_threshold                          2000
% 1.88/1.00  --clause_weak_htbl                      true
% 1.88/1.00  --gc_record_bc_elim                     false
% 1.88/1.00  
% 1.88/1.00  ------ Preprocessing Options
% 1.88/1.00  
% 1.88/1.00  --preprocessing_flag                    true
% 1.88/1.00  --time_out_prep_mult                    0.1
% 1.88/1.00  --splitting_mode                        input
% 1.88/1.00  --splitting_grd                         true
% 1.88/1.00  --splitting_cvd                         false
% 1.88/1.00  --splitting_cvd_svl                     false
% 1.88/1.00  --splitting_nvd                         32
% 1.88/1.00  --sub_typing                            true
% 1.88/1.00  --prep_gs_sim                           true
% 1.88/1.00  --prep_unflatten                        true
% 1.88/1.00  --prep_res_sim                          true
% 1.88/1.00  --prep_upred                            true
% 1.88/1.00  --prep_sem_filter                       exhaustive
% 1.88/1.00  --prep_sem_filter_out                   false
% 1.88/1.00  --pred_elim                             true
% 1.88/1.00  --res_sim_input                         true
% 1.88/1.00  --eq_ax_congr_red                       true
% 1.88/1.00  --pure_diseq_elim                       true
% 1.88/1.00  --brand_transform                       false
% 1.88/1.00  --non_eq_to_eq                          false
% 1.88/1.00  --prep_def_merge                        true
% 1.88/1.00  --prep_def_merge_prop_impl              false
% 1.88/1.00  --prep_def_merge_mbd                    true
% 1.88/1.00  --prep_def_merge_tr_red                 false
% 1.88/1.00  --prep_def_merge_tr_cl                  false
% 1.88/1.00  --smt_preprocessing                     true
% 1.88/1.00  --smt_ac_axioms                         fast
% 1.88/1.00  --preprocessed_out                      false
% 1.88/1.00  --preprocessed_stats                    false
% 1.88/1.00  
% 1.88/1.00  ------ Abstraction refinement Options
% 1.88/1.00  
% 1.88/1.00  --abstr_ref                             []
% 1.88/1.00  --abstr_ref_prep                        false
% 1.88/1.00  --abstr_ref_until_sat                   false
% 1.88/1.00  --abstr_ref_sig_restrict                funpre
% 1.88/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.88/1.00  --abstr_ref_under                       []
% 1.88/1.00  
% 1.88/1.00  ------ SAT Options
% 1.88/1.00  
% 1.88/1.00  --sat_mode                              false
% 1.88/1.00  --sat_fm_restart_options                ""
% 1.88/1.00  --sat_gr_def                            false
% 1.88/1.00  --sat_epr_types                         true
% 1.88/1.00  --sat_non_cyclic_types                  false
% 1.88/1.00  --sat_finite_models                     false
% 1.88/1.00  --sat_fm_lemmas                         false
% 1.88/1.00  --sat_fm_prep                           false
% 1.88/1.00  --sat_fm_uc_incr                        true
% 1.88/1.00  --sat_out_model                         small
% 1.88/1.00  --sat_out_clauses                       false
% 1.88/1.00  
% 1.88/1.00  ------ QBF Options
% 1.88/1.00  
% 1.88/1.00  --qbf_mode                              false
% 1.88/1.00  --qbf_elim_univ                         false
% 1.88/1.00  --qbf_dom_inst                          none
% 1.88/1.00  --qbf_dom_pre_inst                      false
% 1.88/1.00  --qbf_sk_in                             false
% 1.88/1.00  --qbf_pred_elim                         true
% 1.88/1.00  --qbf_split                             512
% 1.88/1.00  
% 1.88/1.00  ------ BMC1 Options
% 1.88/1.00  
% 1.88/1.00  --bmc1_incremental                      false
% 1.88/1.00  --bmc1_axioms                           reachable_all
% 1.88/1.00  --bmc1_min_bound                        0
% 1.88/1.00  --bmc1_max_bound                        -1
% 1.88/1.00  --bmc1_max_bound_default                -1
% 1.88/1.00  --bmc1_symbol_reachability              true
% 1.88/1.00  --bmc1_property_lemmas                  false
% 1.88/1.00  --bmc1_k_induction                      false
% 1.88/1.00  --bmc1_non_equiv_states                 false
% 1.88/1.00  --bmc1_deadlock                         false
% 1.88/1.00  --bmc1_ucm                              false
% 1.88/1.00  --bmc1_add_unsat_core                   none
% 1.88/1.00  --bmc1_unsat_core_children              false
% 1.88/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.88/1.00  --bmc1_out_stat                         full
% 1.88/1.00  --bmc1_ground_init                      false
% 1.88/1.00  --bmc1_pre_inst_next_state              false
% 1.88/1.00  --bmc1_pre_inst_state                   false
% 1.88/1.00  --bmc1_pre_inst_reach_state             false
% 1.88/1.00  --bmc1_out_unsat_core                   false
% 1.88/1.00  --bmc1_aig_witness_out                  false
% 1.88/1.00  --bmc1_verbose                          false
% 1.88/1.00  --bmc1_dump_clauses_tptp                false
% 1.88/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.88/1.00  --bmc1_dump_file                        -
% 1.88/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.88/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.88/1.00  --bmc1_ucm_extend_mode                  1
% 1.88/1.00  --bmc1_ucm_init_mode                    2
% 1.88/1.00  --bmc1_ucm_cone_mode                    none
% 1.88/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.88/1.00  --bmc1_ucm_relax_model                  4
% 1.88/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.88/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.88/1.00  --bmc1_ucm_layered_model                none
% 1.88/1.00  --bmc1_ucm_max_lemma_size               10
% 1.88/1.00  
% 1.88/1.00  ------ AIG Options
% 1.88/1.00  
% 1.88/1.00  --aig_mode                              false
% 1.88/1.00  
% 1.88/1.00  ------ Instantiation Options
% 1.88/1.00  
% 1.88/1.00  --instantiation_flag                    true
% 1.88/1.00  --inst_sos_flag                         false
% 1.88/1.00  --inst_sos_phase                        true
% 1.88/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.88/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.88/1.00  --inst_lit_sel_side                     num_symb
% 1.88/1.00  --inst_solver_per_active                1400
% 1.88/1.00  --inst_solver_calls_frac                1.
% 1.88/1.00  --inst_passive_queue_type               priority_queues
% 1.88/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.88/1.00  --inst_passive_queues_freq              [25;2]
% 1.88/1.00  --inst_dismatching                      true
% 1.88/1.00  --inst_eager_unprocessed_to_passive     true
% 1.88/1.00  --inst_prop_sim_given                   true
% 1.88/1.00  --inst_prop_sim_new                     false
% 1.88/1.00  --inst_subs_new                         false
% 1.88/1.00  --inst_eq_res_simp                      false
% 1.88/1.00  --inst_subs_given                       false
% 1.88/1.00  --inst_orphan_elimination               true
% 1.88/1.00  --inst_learning_loop_flag               true
% 1.88/1.00  --inst_learning_start                   3000
% 1.88/1.00  --inst_learning_factor                  2
% 1.88/1.00  --inst_start_prop_sim_after_learn       3
% 1.88/1.00  --inst_sel_renew                        solver
% 1.88/1.00  --inst_lit_activity_flag                true
% 1.88/1.00  --inst_restr_to_given                   false
% 1.88/1.00  --inst_activity_threshold               500
% 1.88/1.00  --inst_out_proof                        true
% 1.88/1.00  
% 1.88/1.00  ------ Resolution Options
% 1.88/1.00  
% 1.88/1.00  --resolution_flag                       true
% 1.88/1.00  --res_lit_sel                           adaptive
% 1.88/1.00  --res_lit_sel_side                      none
% 1.88/1.00  --res_ordering                          kbo
% 1.88/1.00  --res_to_prop_solver                    active
% 1.88/1.00  --res_prop_simpl_new                    false
% 1.88/1.00  --res_prop_simpl_given                  true
% 1.88/1.00  --res_passive_queue_type                priority_queues
% 1.88/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.88/1.00  --res_passive_queues_freq               [15;5]
% 1.88/1.00  --res_forward_subs                      full
% 1.88/1.00  --res_backward_subs                     full
% 1.88/1.00  --res_forward_subs_resolution           true
% 1.88/1.00  --res_backward_subs_resolution          true
% 1.88/1.00  --res_orphan_elimination                true
% 1.88/1.00  --res_time_limit                        2.
% 1.88/1.00  --res_out_proof                         true
% 1.88/1.00  
% 1.88/1.00  ------ Superposition Options
% 1.88/1.00  
% 1.88/1.00  --superposition_flag                    true
% 1.88/1.00  --sup_passive_queue_type                priority_queues
% 1.88/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.88/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.88/1.00  --demod_completeness_check              fast
% 1.88/1.00  --demod_use_ground                      true
% 1.88/1.00  --sup_to_prop_solver                    passive
% 1.88/1.00  --sup_prop_simpl_new                    true
% 1.88/1.00  --sup_prop_simpl_given                  true
% 1.88/1.00  --sup_fun_splitting                     false
% 1.88/1.00  --sup_smt_interval                      50000
% 1.88/1.00  
% 1.88/1.00  ------ Superposition Simplification Setup
% 1.88/1.00  
% 1.88/1.00  --sup_indices_passive                   []
% 1.88/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.88/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.00  --sup_full_bw                           [BwDemod]
% 1.88/1.00  --sup_immed_triv                        [TrivRules]
% 1.88/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.88/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.00  --sup_immed_bw_main                     []
% 1.88/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.88/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.00  
% 1.88/1.00  ------ Combination Options
% 1.88/1.00  
% 1.88/1.00  --comb_res_mult                         3
% 1.88/1.00  --comb_sup_mult                         2
% 1.88/1.00  --comb_inst_mult                        10
% 1.88/1.00  
% 1.88/1.00  ------ Debug Options
% 1.88/1.00  
% 1.88/1.00  --dbg_backtrace                         false
% 1.88/1.00  --dbg_dump_prop_clauses                 false
% 1.88/1.00  --dbg_dump_prop_clauses_file            -
% 1.88/1.00  --dbg_out_stat                          false
% 1.88/1.00  ------ Parsing...
% 1.88/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.88/1.00  
% 1.88/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.88/1.00  
% 1.88/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.88/1.00  
% 1.88/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.88/1.00  ------ Proving...
% 1.88/1.00  ------ Problem Properties 
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  clauses                                 14
% 1.88/1.00  conjectures                             5
% 1.88/1.00  EPR                                     3
% 1.88/1.00  Horn                                    10
% 1.88/1.00  unary                                   5
% 1.88/1.00  binary                                  1
% 1.88/1.00  lits                                    47
% 1.88/1.00  lits eq                                 7
% 1.88/1.00  fd_pure                                 0
% 1.88/1.00  fd_pseudo                               0
% 1.88/1.00  fd_cond                                 4
% 1.88/1.00  fd_pseudo_cond                          0
% 1.88/1.00  AC symbols                              0
% 1.88/1.00  
% 1.88/1.00  ------ Schedule dynamic 5 is on 
% 1.88/1.00  
% 1.88/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  ------ 
% 1.88/1.00  Current options:
% 1.88/1.00  ------ 
% 1.88/1.00  
% 1.88/1.00  ------ Input Options
% 1.88/1.00  
% 1.88/1.00  --out_options                           all
% 1.88/1.00  --tptp_safe_out                         true
% 1.88/1.00  --problem_path                          ""
% 1.88/1.00  --include_path                          ""
% 1.88/1.00  --clausifier                            res/vclausify_rel
% 1.88/1.00  --clausifier_options                    --mode clausify
% 1.88/1.00  --stdin                                 false
% 1.88/1.00  --stats_out                             all
% 1.88/1.00  
% 1.88/1.00  ------ General Options
% 1.88/1.00  
% 1.88/1.00  --fof                                   false
% 1.88/1.00  --time_out_real                         305.
% 1.88/1.00  --time_out_virtual                      -1.
% 1.88/1.00  --symbol_type_check                     false
% 1.88/1.00  --clausify_out                          false
% 1.88/1.00  --sig_cnt_out                           false
% 1.88/1.00  --trig_cnt_out                          false
% 1.88/1.00  --trig_cnt_out_tolerance                1.
% 1.88/1.00  --trig_cnt_out_sk_spl                   false
% 1.88/1.00  --abstr_cl_out                          false
% 1.88/1.00  
% 1.88/1.00  ------ Global Options
% 1.88/1.00  
% 1.88/1.00  --schedule                              default
% 1.88/1.00  --add_important_lit                     false
% 1.88/1.00  --prop_solver_per_cl                    1000
% 1.88/1.00  --min_unsat_core                        false
% 1.88/1.00  --soft_assumptions                      false
% 1.88/1.00  --soft_lemma_size                       3
% 1.88/1.00  --prop_impl_unit_size                   0
% 1.88/1.00  --prop_impl_unit                        []
% 1.88/1.00  --share_sel_clauses                     true
% 1.88/1.00  --reset_solvers                         false
% 1.88/1.00  --bc_imp_inh                            [conj_cone]
% 1.88/1.00  --conj_cone_tolerance                   3.
% 1.88/1.00  --extra_neg_conj                        none
% 1.88/1.00  --large_theory_mode                     true
% 1.88/1.00  --prolific_symb_bound                   200
% 1.88/1.00  --lt_threshold                          2000
% 1.88/1.00  --clause_weak_htbl                      true
% 1.88/1.00  --gc_record_bc_elim                     false
% 1.88/1.00  
% 1.88/1.00  ------ Preprocessing Options
% 1.88/1.00  
% 1.88/1.00  --preprocessing_flag                    true
% 1.88/1.00  --time_out_prep_mult                    0.1
% 1.88/1.00  --splitting_mode                        input
% 1.88/1.00  --splitting_grd                         true
% 1.88/1.00  --splitting_cvd                         false
% 1.88/1.00  --splitting_cvd_svl                     false
% 1.88/1.00  --splitting_nvd                         32
% 1.88/1.00  --sub_typing                            true
% 1.88/1.00  --prep_gs_sim                           true
% 1.88/1.00  --prep_unflatten                        true
% 1.88/1.00  --prep_res_sim                          true
% 1.88/1.00  --prep_upred                            true
% 1.88/1.00  --prep_sem_filter                       exhaustive
% 1.88/1.00  --prep_sem_filter_out                   false
% 1.88/1.00  --pred_elim                             true
% 1.88/1.00  --res_sim_input                         true
% 1.88/1.00  --eq_ax_congr_red                       true
% 1.88/1.00  --pure_diseq_elim                       true
% 1.88/1.00  --brand_transform                       false
% 1.88/1.00  --non_eq_to_eq                          false
% 1.88/1.00  --prep_def_merge                        true
% 1.88/1.00  --prep_def_merge_prop_impl              false
% 1.88/1.00  --prep_def_merge_mbd                    true
% 1.88/1.00  --prep_def_merge_tr_red                 false
% 1.88/1.00  --prep_def_merge_tr_cl                  false
% 1.88/1.00  --smt_preprocessing                     true
% 1.88/1.00  --smt_ac_axioms                         fast
% 1.88/1.00  --preprocessed_out                      false
% 1.88/1.00  --preprocessed_stats                    false
% 1.88/1.00  
% 1.88/1.00  ------ Abstraction refinement Options
% 1.88/1.00  
% 1.88/1.00  --abstr_ref                             []
% 1.88/1.00  --abstr_ref_prep                        false
% 1.88/1.00  --abstr_ref_until_sat                   false
% 1.88/1.00  --abstr_ref_sig_restrict                funpre
% 1.88/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.88/1.00  --abstr_ref_under                       []
% 1.88/1.00  
% 1.88/1.00  ------ SAT Options
% 1.88/1.00  
% 1.88/1.00  --sat_mode                              false
% 1.88/1.00  --sat_fm_restart_options                ""
% 1.88/1.00  --sat_gr_def                            false
% 1.88/1.00  --sat_epr_types                         true
% 1.88/1.00  --sat_non_cyclic_types                  false
% 1.88/1.00  --sat_finite_models                     false
% 1.88/1.00  --sat_fm_lemmas                         false
% 1.88/1.00  --sat_fm_prep                           false
% 1.88/1.00  --sat_fm_uc_incr                        true
% 1.88/1.00  --sat_out_model                         small
% 1.88/1.00  --sat_out_clauses                       false
% 1.88/1.00  
% 1.88/1.00  ------ QBF Options
% 1.88/1.00  
% 1.88/1.00  --qbf_mode                              false
% 1.88/1.00  --qbf_elim_univ                         false
% 1.88/1.00  --qbf_dom_inst                          none
% 1.88/1.00  --qbf_dom_pre_inst                      false
% 1.88/1.00  --qbf_sk_in                             false
% 1.88/1.00  --qbf_pred_elim                         true
% 1.88/1.00  --qbf_split                             512
% 1.88/1.00  
% 1.88/1.00  ------ BMC1 Options
% 1.88/1.00  
% 1.88/1.00  --bmc1_incremental                      false
% 1.88/1.00  --bmc1_axioms                           reachable_all
% 1.88/1.00  --bmc1_min_bound                        0
% 1.88/1.00  --bmc1_max_bound                        -1
% 1.88/1.00  --bmc1_max_bound_default                -1
% 1.88/1.00  --bmc1_symbol_reachability              true
% 1.88/1.00  --bmc1_property_lemmas                  false
% 1.88/1.00  --bmc1_k_induction                      false
% 1.88/1.00  --bmc1_non_equiv_states                 false
% 1.88/1.00  --bmc1_deadlock                         false
% 1.88/1.00  --bmc1_ucm                              false
% 1.88/1.00  --bmc1_add_unsat_core                   none
% 1.88/1.00  --bmc1_unsat_core_children              false
% 1.88/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.88/1.00  --bmc1_out_stat                         full
% 1.88/1.00  --bmc1_ground_init                      false
% 1.88/1.00  --bmc1_pre_inst_next_state              false
% 1.88/1.00  --bmc1_pre_inst_state                   false
% 1.88/1.00  --bmc1_pre_inst_reach_state             false
% 1.88/1.00  --bmc1_out_unsat_core                   false
% 1.88/1.00  --bmc1_aig_witness_out                  false
% 1.88/1.00  --bmc1_verbose                          false
% 1.88/1.00  --bmc1_dump_clauses_tptp                false
% 1.88/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.88/1.00  --bmc1_dump_file                        -
% 1.88/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.88/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.88/1.00  --bmc1_ucm_extend_mode                  1
% 1.88/1.00  --bmc1_ucm_init_mode                    2
% 1.88/1.00  --bmc1_ucm_cone_mode                    none
% 1.88/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.88/1.00  --bmc1_ucm_relax_model                  4
% 1.88/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.88/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.88/1.00  --bmc1_ucm_layered_model                none
% 1.88/1.00  --bmc1_ucm_max_lemma_size               10
% 1.88/1.00  
% 1.88/1.00  ------ AIG Options
% 1.88/1.00  
% 1.88/1.00  --aig_mode                              false
% 1.88/1.00  
% 1.88/1.00  ------ Instantiation Options
% 1.88/1.00  
% 1.88/1.00  --instantiation_flag                    true
% 1.88/1.00  --inst_sos_flag                         false
% 1.88/1.00  --inst_sos_phase                        true
% 1.88/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.88/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.88/1.00  --inst_lit_sel_side                     none
% 1.88/1.00  --inst_solver_per_active                1400
% 1.88/1.00  --inst_solver_calls_frac                1.
% 1.88/1.00  --inst_passive_queue_type               priority_queues
% 1.88/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.88/1.00  --inst_passive_queues_freq              [25;2]
% 1.88/1.00  --inst_dismatching                      true
% 1.88/1.00  --inst_eager_unprocessed_to_passive     true
% 1.88/1.00  --inst_prop_sim_given                   true
% 1.88/1.00  --inst_prop_sim_new                     false
% 1.88/1.00  --inst_subs_new                         false
% 1.88/1.00  --inst_eq_res_simp                      false
% 1.88/1.00  --inst_subs_given                       false
% 1.88/1.00  --inst_orphan_elimination               true
% 1.88/1.00  --inst_learning_loop_flag               true
% 1.88/1.00  --inst_learning_start                   3000
% 1.88/1.00  --inst_learning_factor                  2
% 1.88/1.00  --inst_start_prop_sim_after_learn       3
% 1.88/1.00  --inst_sel_renew                        solver
% 1.88/1.00  --inst_lit_activity_flag                true
% 1.88/1.00  --inst_restr_to_given                   false
% 1.88/1.00  --inst_activity_threshold               500
% 1.88/1.00  --inst_out_proof                        true
% 1.88/1.00  
% 1.88/1.00  ------ Resolution Options
% 1.88/1.00  
% 1.88/1.00  --resolution_flag                       false
% 1.88/1.00  --res_lit_sel                           adaptive
% 1.88/1.00  --res_lit_sel_side                      none
% 1.88/1.00  --res_ordering                          kbo
% 1.88/1.00  --res_to_prop_solver                    active
% 1.88/1.00  --res_prop_simpl_new                    false
% 1.88/1.00  --res_prop_simpl_given                  true
% 1.88/1.00  --res_passive_queue_type                priority_queues
% 1.88/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.88/1.00  --res_passive_queues_freq               [15;5]
% 1.88/1.00  --res_forward_subs                      full
% 1.88/1.00  --res_backward_subs                     full
% 1.88/1.00  --res_forward_subs_resolution           true
% 1.88/1.00  --res_backward_subs_resolution          true
% 1.88/1.00  --res_orphan_elimination                true
% 1.88/1.00  --res_time_limit                        2.
% 1.88/1.00  --res_out_proof                         true
% 1.88/1.00  
% 1.88/1.00  ------ Superposition Options
% 1.88/1.00  
% 1.88/1.00  --superposition_flag                    true
% 1.88/1.00  --sup_passive_queue_type                priority_queues
% 1.88/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.88/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.88/1.00  --demod_completeness_check              fast
% 1.88/1.00  --demod_use_ground                      true
% 1.88/1.00  --sup_to_prop_solver                    passive
% 1.88/1.00  --sup_prop_simpl_new                    true
% 1.88/1.00  --sup_prop_simpl_given                  true
% 1.88/1.00  --sup_fun_splitting                     false
% 1.88/1.00  --sup_smt_interval                      50000
% 1.88/1.00  
% 1.88/1.00  ------ Superposition Simplification Setup
% 1.88/1.00  
% 1.88/1.00  --sup_indices_passive                   []
% 1.88/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.88/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.00  --sup_full_bw                           [BwDemod]
% 1.88/1.00  --sup_immed_triv                        [TrivRules]
% 1.88/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.88/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.00  --sup_immed_bw_main                     []
% 1.88/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.88/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.00  
% 1.88/1.00  ------ Combination Options
% 1.88/1.00  
% 1.88/1.00  --comb_res_mult                         3
% 1.88/1.00  --comb_sup_mult                         2
% 1.88/1.00  --comb_inst_mult                        10
% 1.88/1.00  
% 1.88/1.00  ------ Debug Options
% 1.88/1.00  
% 1.88/1.00  --dbg_backtrace                         false
% 1.88/1.00  --dbg_dump_prop_clauses                 false
% 1.88/1.00  --dbg_dump_prop_clauses_file            -
% 1.88/1.00  --dbg_out_stat                          false
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  ------ Proving...
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  % SZS status Theorem for theBenchmark.p
% 1.88/1.00  
% 1.88/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.88/1.00  
% 1.88/1.00  fof(f1,axiom,(
% 1.88/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 1.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f6,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.88/1.00    inference(ennf_transformation,[],[f1])).
% 1.88/1.00  
% 1.88/1.00  fof(f7,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.88/1.00    inference(flattening,[],[f6])).
% 1.88/1.00  
% 1.88/1.00  fof(f14,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.88/1.00    inference(nnf_transformation,[],[f7])).
% 1.88/1.00  
% 1.88/1.00  fof(f15,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.88/1.00    inference(rectify,[],[f14])).
% 1.88/1.00  
% 1.88/1.00  fof(f16,plain,(
% 1.88/1.00    ! [X2,X1,X0] : (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2 & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.88/1.00    introduced(choice_axiom,[])).
% 1.88/1.00  
% 1.88/1.00  fof(f17,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2 & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.88/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 1.88/1.00  
% 1.88/1.00  fof(f28,plain,(
% 1.88/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f17])).
% 1.88/1.00  
% 1.88/1.00  fof(f46,plain,(
% 1.88/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.88/1.00    inference(equality_resolution,[],[f28])).
% 1.88/1.00  
% 1.88/1.00  fof(f4,conjecture,(
% 1.88/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 1.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f5,negated_conjecture,(
% 1.88/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 1.88/1.00    inference(negated_conjecture,[],[f4])).
% 1.88/1.00  
% 1.88/1.00  fof(f12,plain,(
% 1.88/1.00    ? [X0] : (? [X1] : (? [X2] : ((m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.88/1.00    inference(ennf_transformation,[],[f5])).
% 1.88/1.00  
% 1.88/1.00  fof(f13,plain,(
% 1.88/1.00    ? [X0] : (? [X1] : (? [X2] : (m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.88/1.00    inference(flattening,[],[f12])).
% 1.88/1.00  
% 1.88/1.00  fof(f22,plain,(
% 1.88/1.00    ( ! [X0,X1] : (? [X2] : (m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (m1_orders_2(sK3,X0,X1) & m1_orders_2(X1,X0,sK3) & k1_xboole_0 != X1 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.88/1.00    introduced(choice_axiom,[])).
% 1.88/1.00  
% 1.88/1.00  fof(f21,plain,(
% 1.88/1.00    ( ! [X0] : (? [X1] : (? [X2] : (m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (m1_orders_2(X2,X0,sK2) & m1_orders_2(sK2,X0,X2) & k1_xboole_0 != sK2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.88/1.00    introduced(choice_axiom,[])).
% 1.88/1.00  
% 1.88/1.00  fof(f20,plain,(
% 1.88/1.00    ? [X0] : (? [X1] : (? [X2] : (m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (m1_orders_2(X2,sK1,X1) & m1_orders_2(X1,sK1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.88/1.00    introduced(choice_axiom,[])).
% 1.88/1.00  
% 1.88/1.00  fof(f23,plain,(
% 1.88/1.00    ((m1_orders_2(sK3,sK1,sK2) & m1_orders_2(sK2,sK1,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 1.88/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f22,f21,f20])).
% 1.88/1.00  
% 1.88/1.00  fof(f38,plain,(
% 1.88/1.00    l1_orders_2(sK1)),
% 1.88/1.00    inference(cnf_transformation,[],[f23])).
% 1.88/1.00  
% 1.88/1.00  fof(f34,plain,(
% 1.88/1.00    ~v2_struct_0(sK1)),
% 1.88/1.00    inference(cnf_transformation,[],[f23])).
% 1.88/1.00  
% 1.88/1.00  fof(f35,plain,(
% 1.88/1.00    v3_orders_2(sK1)),
% 1.88/1.00    inference(cnf_transformation,[],[f23])).
% 1.88/1.00  
% 1.88/1.00  fof(f36,plain,(
% 1.88/1.00    v4_orders_2(sK1)),
% 1.88/1.00    inference(cnf_transformation,[],[f23])).
% 1.88/1.00  
% 1.88/1.00  fof(f37,plain,(
% 1.88/1.00    v5_orders_2(sK1)),
% 1.88/1.00    inference(cnf_transformation,[],[f23])).
% 1.88/1.00  
% 1.88/1.00  fof(f39,plain,(
% 1.88/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.88/1.00    inference(cnf_transformation,[],[f23])).
% 1.88/1.00  
% 1.88/1.00  fof(f40,plain,(
% 1.88/1.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.88/1.00    inference(cnf_transformation,[],[f23])).
% 1.88/1.00  
% 1.88/1.00  fof(f26,plain,(
% 1.88/1.00    ( ! [X2,X0,X1] : (k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f17])).
% 1.88/1.00  
% 1.88/1.00  fof(f42,plain,(
% 1.88/1.00    m1_orders_2(sK2,sK1,sK3)),
% 1.88/1.00    inference(cnf_transformation,[],[f23])).
% 1.88/1.00  
% 1.88/1.00  fof(f41,plain,(
% 1.88/1.00    k1_xboole_0 != sK2),
% 1.88/1.00    inference(cnf_transformation,[],[f23])).
% 1.88/1.00  
% 1.88/1.00  fof(f3,axiom,(
% 1.88/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~r2_hidden(X1,k3_orders_2(X0,X2,X1)))))),
% 1.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f10,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k3_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.88/1.00    inference(ennf_transformation,[],[f3])).
% 1.88/1.00  
% 1.88/1.00  fof(f11,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k3_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.88/1.00    inference(flattening,[],[f10])).
% 1.88/1.00  
% 1.88/1.00  fof(f33,plain,(
% 1.88/1.00    ( ! [X2,X0,X1] : (~r2_hidden(X1,k3_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f11])).
% 1.88/1.00  
% 1.88/1.00  fof(f24,plain,(
% 1.88/1.00    ( ! [X2,X0,X1] : (m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f17])).
% 1.88/1.00  
% 1.88/1.00  fof(f2,axiom,(
% 1.88/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 1.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f8,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.88/1.00    inference(ennf_transformation,[],[f2])).
% 1.88/1.00  
% 1.88/1.00  fof(f9,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.88/1.00    inference(flattening,[],[f8])).
% 1.88/1.00  
% 1.88/1.00  fof(f18,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.88/1.00    inference(nnf_transformation,[],[f9])).
% 1.88/1.00  
% 1.88/1.00  fof(f19,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.88/1.00    inference(flattening,[],[f18])).
% 1.88/1.00  
% 1.88/1.00  fof(f31,plain,(
% 1.88/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f19])).
% 1.88/1.00  
% 1.88/1.00  fof(f25,plain,(
% 1.88/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f17])).
% 1.88/1.00  
% 1.88/1.00  fof(f43,plain,(
% 1.88/1.00    m1_orders_2(sK3,sK1,sK2)),
% 1.88/1.00    inference(cnf_transformation,[],[f23])).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1041,plain,( X0_45 = X0_45 ),theory(equality) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2581,plain,
% 1.88/1.00      ( sK0(sK1,sK3,sK2) = sK0(sK1,sK3,sK2) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1041]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1046,plain,
% 1.88/1.00      ( ~ r2_hidden(X0_45,X1_45)
% 1.88/1.00      | r2_hidden(X2_45,X3_45)
% 1.88/1.00      | X2_45 != X0_45
% 1.88/1.00      | X3_45 != X1_45 ),
% 1.88/1.00      theory(equality) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1749,plain,
% 1.88/1.00      ( r2_hidden(X0_45,X1_45)
% 1.88/1.00      | ~ r2_hidden(sK0(sK1,sK3,sK2),sK3)
% 1.88/1.00      | X0_45 != sK0(sK1,sK3,sK2)
% 1.88/1.00      | X1_45 != sK3 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1046]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2148,plain,
% 1.88/1.00      ( r2_hidden(X0_45,k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK3)))
% 1.88/1.00      | ~ r2_hidden(sK0(sK1,sK3,sK2),sK3)
% 1.88/1.00      | X0_45 != sK0(sK1,sK3,sK2)
% 1.88/1.00      | k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK3)) != sK3 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1749]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2580,plain,
% 1.88/1.00      ( r2_hidden(sK0(sK1,sK3,sK2),k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK3)))
% 1.88/1.00      | ~ r2_hidden(sK0(sK1,sK3,sK2),sK3)
% 1.88/1.00      | sK0(sK1,sK3,sK2) != sK0(sK1,sK3,sK2)
% 1.88/1.00      | k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK3)) != sK3 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_2148]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,X1,k1_xboole_0)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | ~ v3_orders_2(X1)
% 1.88/1.00      | ~ v4_orders_2(X1)
% 1.88/1.00      | ~ v5_orders_2(X1)
% 1.88/1.00      | ~ l1_orders_2(X1)
% 1.88/1.00      | k1_xboole_0 = X0 ),
% 1.88/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_15,negated_conjecture,
% 1.88/1.00      ( l1_orders_2(sK1) ),
% 1.88/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_388,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,X1,k1_xboole_0)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | ~ v3_orders_2(X1)
% 1.88/1.00      | ~ v4_orders_2(X1)
% 1.88/1.00      | ~ v5_orders_2(X1)
% 1.88/1.00      | sK1 != X1
% 1.88/1.00      | k1_xboole_0 = X0 ),
% 1.88/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_15]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_389,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,sK1,k1_xboole_0)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | v2_struct_0(sK1)
% 1.88/1.00      | ~ v3_orders_2(sK1)
% 1.88/1.00      | ~ v4_orders_2(sK1)
% 1.88/1.00      | ~ v5_orders_2(sK1)
% 1.88/1.00      | k1_xboole_0 = X0 ),
% 1.88/1.00      inference(unflattening,[status(thm)],[c_388]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_19,negated_conjecture,
% 1.88/1.00      ( ~ v2_struct_0(sK1) ),
% 1.88/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_18,negated_conjecture,
% 1.88/1.00      ( v3_orders_2(sK1) ),
% 1.88/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_17,negated_conjecture,
% 1.88/1.00      ( v4_orders_2(sK1) ),
% 1.88/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_16,negated_conjecture,
% 1.88/1.00      ( v5_orders_2(sK1) ),
% 1.88/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_393,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,sK1,k1_xboole_0)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k1_xboole_0 = X0 ),
% 1.88/1.00      inference(global_propositional_subsumption,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_389,c_19,c_18,c_17,c_16]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1028,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0_45,sK1,k1_xboole_0)
% 1.88/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k1_xboole_0 = X0_45 ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_393]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2456,plain,
% 1.88/1.00      ( ~ m1_orders_2(k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)),sK1,k1_xboole_0)
% 1.88/1.00      | ~ m1_subset_1(k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k1_xboole_0 = k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1028]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_14,negated_conjecture,
% 1.88/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.88/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1035,negated_conjecture,
% 1.88/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1279,plain,
% 1.88/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1035]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_13,negated_conjecture,
% 1.88/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.88/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1036,negated_conjecture,
% 1.88/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1278,plain,
% 1.88/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1036]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_3,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | ~ v3_orders_2(X1)
% 1.88/1.00      | ~ v4_orders_2(X1)
% 1.88/1.00      | ~ v5_orders_2(X1)
% 1.88/1.00      | ~ l1_orders_2(X1)
% 1.88/1.00      | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
% 1.88/1.00      | k1_xboole_0 = X2 ),
% 1.88/1.00      inference(cnf_transformation,[],[f26]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_361,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | ~ v3_orders_2(X1)
% 1.88/1.00      | ~ v4_orders_2(X1)
% 1.88/1.00      | ~ v5_orders_2(X1)
% 1.88/1.00      | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
% 1.88/1.00      | sK1 != X1
% 1.88/1.00      | k1_xboole_0 = X2 ),
% 1.88/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_15]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_362,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | v2_struct_0(sK1)
% 1.88/1.00      | ~ v3_orders_2(sK1)
% 1.88/1.00      | ~ v4_orders_2(sK1)
% 1.88/1.00      | ~ v5_orders_2(sK1)
% 1.88/1.00      | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
% 1.88/1.00      | k1_xboole_0 = X1 ),
% 1.88/1.00      inference(unflattening,[status(thm)],[c_361]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_366,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
% 1.88/1.00      | k1_xboole_0 = X1 ),
% 1.88/1.00      inference(global_propositional_subsumption,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_362,c_19,c_18,c_17,c_16]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_367,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
% 1.88/1.00      | k1_xboole_0 = X1 ),
% 1.88/1.00      inference(renaming,[status(thm)],[c_366]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1029,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0_45,sK1,X1_45)
% 1.88/1.00      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k3_orders_2(sK1,X1_45,sK0(sK1,X1_45,X0_45)) = X0_45
% 1.88/1.00      | k1_xboole_0 = X1_45 ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_367]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1285,plain,
% 1.88/1.00      ( k3_orders_2(sK1,X0_45,sK0(sK1,X0_45,X1_45)) = X1_45
% 1.88/1.00      | k1_xboole_0 = X0_45
% 1.88/1.00      | m1_orders_2(X1_45,sK1,X0_45) != iProver_top
% 1.88/1.00      | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.88/1.00      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1029]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1820,plain,
% 1.88/1.00      ( k3_orders_2(sK1,sK3,sK0(sK1,sK3,X0_45)) = X0_45
% 1.88/1.00      | sK3 = k1_xboole_0
% 1.88/1.00      | m1_orders_2(X0_45,sK1,sK3) != iProver_top
% 1.88/1.00      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.88/1.00      inference(superposition,[status(thm)],[c_1278,c_1285]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_26,plain,
% 1.88/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_11,negated_conjecture,
% 1.88/1.00      ( m1_orders_2(sK2,sK1,sK3) ),
% 1.88/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_12,negated_conjecture,
% 1.88/1.00      ( k1_xboole_0 != sK2 ),
% 1.88/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1037,negated_conjecture,
% 1.88/1.00      ( k1_xboole_0 != sK2 ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1412,plain,
% 1.88/1.00      ( ~ m1_orders_2(sK2,sK1,k1_xboole_0)
% 1.88/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k1_xboole_0 = sK2 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1028]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1044,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0_45,X0_47)
% 1.88/1.00      | m1_subset_1(X1_45,X0_47)
% 1.88/1.00      | X1_45 != X0_45 ),
% 1.88/1.00      theory(equality) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1440,plain,
% 1.88/1.00      ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | X0_45 != sK3 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1044]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1442,plain,
% 1.88/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k1_xboole_0 != sK3 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1440]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1485,plain,
% 1.88/1.00      ( sK2 = sK2 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1041]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1540,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0_45,sK1,sK3)
% 1.88/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k3_orders_2(sK1,sK3,sK0(sK1,sK3,X0_45)) = X0_45
% 1.88/1.00      | k1_xboole_0 = sK3 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1029]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1551,plain,
% 1.88/1.00      ( k3_orders_2(sK1,sK3,sK0(sK1,sK3,X0_45)) = X0_45
% 1.88/1.00      | k1_xboole_0 = sK3
% 1.88/1.00      | m1_orders_2(X0_45,sK1,sK3) != iProver_top
% 1.88/1.00      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.88/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1540]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1043,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0_45,X0_46,X1_45)
% 1.88/1.00      | m1_orders_2(X2_45,X0_46,X3_45)
% 1.88/1.00      | X2_45 != X0_45
% 1.88/1.00      | X3_45 != X1_45 ),
% 1.88/1.00      theory(equality) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1451,plain,
% 1.88/1.00      ( m1_orders_2(X0_45,sK1,X1_45)
% 1.88/1.00      | ~ m1_orders_2(sK2,sK1,sK3)
% 1.88/1.00      | X0_45 != sK2
% 1.88/1.00      | X1_45 != sK3 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1043]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1557,plain,
% 1.88/1.00      ( m1_orders_2(sK2,sK1,X0_45)
% 1.88/1.00      | ~ m1_orders_2(sK2,sK1,sK3)
% 1.88/1.00      | X0_45 != sK3
% 1.88/1.00      | sK2 != sK2 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1451]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1560,plain,
% 1.88/1.00      ( ~ m1_orders_2(sK2,sK1,sK3)
% 1.88/1.00      | m1_orders_2(sK2,sK1,k1_xboole_0)
% 1.88/1.00      | sK2 != sK2
% 1.88/1.00      | k1_xboole_0 != sK3 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1557]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1940,plain,
% 1.88/1.00      ( k3_orders_2(sK1,sK3,sK0(sK1,sK3,X0_45)) = X0_45
% 1.88/1.00      | m1_orders_2(X0_45,sK1,sK3) != iProver_top
% 1.88/1.00      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.88/1.00      inference(global_propositional_subsumption,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_1820,c_14,c_13,c_26,c_11,c_1037,c_1412,c_1442,c_1485,
% 1.88/1.00                 c_1551,c_1560]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1950,plain,
% 1.88/1.00      ( k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)) = sK2
% 1.88/1.00      | m1_orders_2(sK2,sK1,sK3) != iProver_top ),
% 1.88/1.00      inference(superposition,[status(thm)],[c_1279,c_1940]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1729,plain,
% 1.88/1.00      ( ~ m1_orders_2(sK2,sK1,sK3)
% 1.88/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)) = sK2
% 1.88/1.00      | k1_xboole_0 = sK3 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1540]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2048,plain,
% 1.88/1.00      ( k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)) = sK2 ),
% 1.88/1.00      inference(global_propositional_subsumption,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_1950,c_14,c_13,c_11,c_1037,c_1412,c_1442,c_1485,
% 1.88/1.00                 c_1560,c_1729]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_9,plain,
% 1.88/1.00      ( ~ r2_hidden(X0,k3_orders_2(X1,X2,X0))
% 1.88/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | ~ v3_orders_2(X1)
% 1.88/1.00      | ~ v4_orders_2(X1)
% 1.88/1.00      | ~ v5_orders_2(X1)
% 1.88/1.00      | ~ l1_orders_2(X1) ),
% 1.88/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_286,plain,
% 1.88/1.00      ( ~ r2_hidden(X0,k3_orders_2(X1,X2,X0))
% 1.88/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | ~ v3_orders_2(X1)
% 1.88/1.00      | ~ v4_orders_2(X1)
% 1.88/1.00      | ~ v5_orders_2(X1)
% 1.88/1.00      | sK1 != X1 ),
% 1.88/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_287,plain,
% 1.88/1.00      ( ~ r2_hidden(X0,k3_orders_2(sK1,X1,X0))
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.88/1.00      | v2_struct_0(sK1)
% 1.88/1.00      | ~ v3_orders_2(sK1)
% 1.88/1.00      | ~ v4_orders_2(sK1)
% 1.88/1.00      | ~ v5_orders_2(sK1) ),
% 1.88/1.00      inference(unflattening,[status(thm)],[c_286]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_291,plain,
% 1.88/1.00      ( ~ r2_hidden(X0,k3_orders_2(sK1,X1,X0))
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.88/1.00      inference(global_propositional_subsumption,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_287,c_19,c_18,c_17,c_16]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1032,plain,
% 1.88/1.00      ( ~ r2_hidden(X0_45,k3_orders_2(sK1,X1_45,X0_45))
% 1.88/1.00      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X0_45,u1_struct_0(sK1)) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_291]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1282,plain,
% 1.88/1.00      ( r2_hidden(X0_45,k3_orders_2(sK1,X1_45,X0_45)) != iProver_top
% 1.88/1.00      | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.88/1.00      | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1032]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2053,plain,
% 1.88/1.00      ( r2_hidden(sK0(sK1,sK3,sK2),sK2) != iProver_top
% 1.88/1.00      | m1_subset_1(sK0(sK1,sK3,sK2),u1_struct_0(sK1)) != iProver_top
% 1.88/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.88/1.00      inference(superposition,[status(thm)],[c_2048,c_1282]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_25,plain,
% 1.88/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_27,plain,
% 1.88/1.00      ( m1_orders_2(sK2,sK1,sK3) = iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_5,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | ~ v3_orders_2(X1)
% 1.88/1.00      | ~ v4_orders_2(X1)
% 1.88/1.00      | ~ v5_orders_2(X1)
% 1.88/1.00      | ~ l1_orders_2(X1)
% 1.88/1.00      | k1_xboole_0 = X2 ),
% 1.88/1.00      inference(cnf_transformation,[],[f24]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_307,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | ~ v3_orders_2(X1)
% 1.88/1.00      | ~ v4_orders_2(X1)
% 1.88/1.00      | ~ v5_orders_2(X1)
% 1.88/1.00      | sK1 != X1
% 1.88/1.00      | k1_xboole_0 = X2 ),
% 1.88/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_15]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_308,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
% 1.88/1.00      | v2_struct_0(sK1)
% 1.88/1.00      | ~ v3_orders_2(sK1)
% 1.88/1.00      | ~ v4_orders_2(sK1)
% 1.88/1.00      | ~ v5_orders_2(sK1)
% 1.88/1.00      | k1_xboole_0 = X1 ),
% 1.88/1.00      inference(unflattening,[status(thm)],[c_307]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_312,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
% 1.88/1.00      | k1_xboole_0 = X1 ),
% 1.88/1.00      inference(global_propositional_subsumption,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_308,c_19,c_18,c_17,c_16]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_313,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
% 1.88/1.00      | k1_xboole_0 = X1 ),
% 1.88/1.00      inference(renaming,[status(thm)],[c_312]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1031,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0_45,sK1,X1_45)
% 1.88/1.00      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | m1_subset_1(sK0(sK1,X1_45,X0_45),u1_struct_0(sK1))
% 1.88/1.00      | k1_xboole_0 = X1_45 ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_313]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1542,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0_45,sK1,sK3)
% 1.88/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | m1_subset_1(sK0(sK1,sK3,X0_45),u1_struct_0(sK1))
% 1.88/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k1_xboole_0 = sK3 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1031]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1700,plain,
% 1.88/1.00      ( ~ m1_orders_2(sK2,sK1,sK3)
% 1.88/1.00      | m1_subset_1(sK0(sK1,sK3,sK2),u1_struct_0(sK1))
% 1.88/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k1_xboole_0 = sK3 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1542]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1701,plain,
% 1.88/1.00      ( k1_xboole_0 = sK3
% 1.88/1.00      | m1_orders_2(sK2,sK1,sK3) != iProver_top
% 1.88/1.00      | m1_subset_1(sK0(sK1,sK3,sK2),u1_struct_0(sK1)) = iProver_top
% 1.88/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.88/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1700]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2315,plain,
% 1.88/1.00      ( r2_hidden(sK0(sK1,sK3,sK2),sK2) != iProver_top ),
% 1.88/1.00      inference(global_propositional_subsumption,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_2053,c_14,c_25,c_13,c_26,c_11,c_27,c_1037,c_1412,
% 1.88/1.00                 c_1442,c_1485,c_1560,c_1701]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2317,plain,
% 1.88/1.00      ( ~ r2_hidden(sK0(sK1,sK3,sK2),sK2) ),
% 1.88/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2315]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_7,plain,
% 1.88/1.00      ( r2_hidden(X0,X1)
% 1.88/1.00      | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.88/1.00      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 1.88/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.88/1.00      | v2_struct_0(X2)
% 1.88/1.00      | ~ v3_orders_2(X2)
% 1.88/1.00      | ~ v4_orders_2(X2)
% 1.88/1.00      | ~ v5_orders_2(X2)
% 1.88/1.00      | ~ l1_orders_2(X2) ),
% 1.88/1.00      inference(cnf_transformation,[],[f31]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_441,plain,
% 1.88/1.00      ( r2_hidden(X0,X1)
% 1.88/1.00      | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.88/1.00      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 1.88/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.88/1.00      | v2_struct_0(X2)
% 1.88/1.00      | ~ v3_orders_2(X2)
% 1.88/1.00      | ~ v4_orders_2(X2)
% 1.88/1.00      | ~ v5_orders_2(X2)
% 1.88/1.00      | sK1 != X2 ),
% 1.88/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_442,plain,
% 1.88/1.00      ( r2_hidden(X0,X1)
% 1.88/1.00      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.88/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.88/1.00      | v2_struct_0(sK1)
% 1.88/1.00      | ~ v3_orders_2(sK1)
% 1.88/1.00      | ~ v4_orders_2(sK1)
% 1.88/1.00      | ~ v5_orders_2(sK1) ),
% 1.88/1.00      inference(unflattening,[status(thm)],[c_441]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_444,plain,
% 1.88/1.00      ( r2_hidden(X0,X1)
% 1.88/1.00      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.88/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ),
% 1.88/1.00      inference(global_propositional_subsumption,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_442,c_19,c_18,c_17,c_16]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_445,plain,
% 1.88/1.00      ( r2_hidden(X0,X1)
% 1.88/1.00      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.88/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.88/1.00      inference(renaming,[status(thm)],[c_444]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1026,plain,
% 1.88/1.00      ( r2_hidden(X0_45,X1_45)
% 1.88/1.00      | ~ r2_hidden(X0_45,k3_orders_2(sK1,X1_45,X2_45))
% 1.88/1.00      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X2_45,u1_struct_0(sK1))
% 1.88/1.00      | ~ m1_subset_1(X0_45,u1_struct_0(sK1)) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_445]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1507,plain,
% 1.88/1.00      ( r2_hidden(X0_45,X1_45)
% 1.88/1.00      | ~ r2_hidden(X0_45,k3_orders_2(sK1,X1_45,sK0(sK1,sK2,sK3)))
% 1.88/1.00      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X0_45,u1_struct_0(sK1))
% 1.88/1.00      | ~ m1_subset_1(sK0(sK1,sK2,sK3),u1_struct_0(sK1)) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1026]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1765,plain,
% 1.88/1.00      ( r2_hidden(sK0(sK1,sK3,sK2),X0_45)
% 1.88/1.00      | ~ r2_hidden(sK0(sK1,sK3,sK2),k3_orders_2(sK1,X0_45,sK0(sK1,sK2,sK3)))
% 1.88/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(sK0(sK1,sK2,sK3),u1_struct_0(sK1))
% 1.88/1.00      | ~ m1_subset_1(sK0(sK1,sK3,sK2),u1_struct_0(sK1)) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1507]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2124,plain,
% 1.88/1.00      ( ~ r2_hidden(sK0(sK1,sK3,sK2),k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK3)))
% 1.88/1.00      | r2_hidden(sK0(sK1,sK3,sK2),sK2)
% 1.88/1.00      | ~ m1_subset_1(sK0(sK1,sK2,sK3),u1_struct_0(sK1))
% 1.88/1.00      | ~ m1_subset_1(sK0(sK1,sK3,sK2),u1_struct_0(sK1))
% 1.88/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1765]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1042,plain,
% 1.88/1.00      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 1.88/1.00      theory(equality) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1438,plain,
% 1.88/1.00      ( sK2 != X0_45 | k1_xboole_0 != X0_45 | k1_xboole_0 = sK2 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1042]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1895,plain,
% 1.88/1.00      ( sK2 != k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2))
% 1.88/1.00      | k1_xboole_0 != k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2))
% 1.88/1.00      | k1_xboole_0 = sK2 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1438]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1459,plain,
% 1.88/1.00      ( X0_45 != X1_45 | sK2 != X1_45 | sK2 = X0_45 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1042]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1609,plain,
% 1.88/1.00      ( X0_45 != sK2 | sK2 = X0_45 | sK2 != sK2 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1459]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1783,plain,
% 1.88/1.00      ( k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)) != sK2
% 1.88/1.00      | sK2 = k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2))
% 1.88/1.00      | sK2 != sK2 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1609]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1784,plain,
% 1.88/1.00      ( m1_orders_2(k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)),sK1,X0_45)
% 1.88/1.00      | ~ m1_orders_2(sK2,sK1,sK3)
% 1.88/1.00      | X0_45 != sK3
% 1.88/1.00      | k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)) != sK2 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1451]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1789,plain,
% 1.88/1.00      ( m1_orders_2(k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)),sK1,k1_xboole_0)
% 1.88/1.00      | ~ m1_orders_2(sK2,sK1,sK3)
% 1.88/1.00      | k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)) != sK2
% 1.88/1.00      | k1_xboole_0 != sK3 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1784]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1445,plain,
% 1.88/1.00      ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | X0_45 != sK2 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1044]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1785,plain,
% 1.88/1.00      ( m1_subset_1(k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k3_orders_2(sK1,sK3,sK0(sK1,sK3,sK2)) != sK2 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1445]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_4,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.88/1.00      | r2_hidden(sK0(X1,X2,X0),X2)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | ~ v3_orders_2(X1)
% 1.88/1.00      | ~ v4_orders_2(X1)
% 1.88/1.00      | ~ v5_orders_2(X1)
% 1.88/1.00      | ~ l1_orders_2(X1)
% 1.88/1.00      | k1_xboole_0 = X2 ),
% 1.88/1.00      inference(cnf_transformation,[],[f25]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_334,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,X1,X2)
% 1.88/1.00      | r2_hidden(sK0(X1,X2,X0),X2)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | ~ v3_orders_2(X1)
% 1.88/1.00      | ~ v4_orders_2(X1)
% 1.88/1.00      | ~ v5_orders_2(X1)
% 1.88/1.00      | sK1 != X1
% 1.88/1.00      | k1_xboole_0 = X2 ),
% 1.88/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_335,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 1.88/1.00      | r2_hidden(sK0(sK1,X1,X0),X1)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | v2_struct_0(sK1)
% 1.88/1.00      | ~ v3_orders_2(sK1)
% 1.88/1.00      | ~ v4_orders_2(sK1)
% 1.88/1.00      | ~ v5_orders_2(sK1)
% 1.88/1.00      | k1_xboole_0 = X1 ),
% 1.88/1.00      inference(unflattening,[status(thm)],[c_334]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_339,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 1.88/1.00      | r2_hidden(sK0(sK1,X1,X0),X1)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k1_xboole_0 = X1 ),
% 1.88/1.00      inference(global_propositional_subsumption,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_335,c_19,c_18,c_17,c_16]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_340,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0,sK1,X1)
% 1.88/1.00      | r2_hidden(sK0(sK1,X1,X0),X1)
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k1_xboole_0 = X1 ),
% 1.88/1.00      inference(renaming,[status(thm)],[c_339]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1030,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0_45,sK1,X1_45)
% 1.88/1.00      | r2_hidden(sK0(sK1,X1_45,X0_45),X1_45)
% 1.88/1.00      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k1_xboole_0 = X1_45 ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_340]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1541,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0_45,sK1,sK3)
% 1.88/1.00      | r2_hidden(sK0(sK1,sK3,X0_45),sK3)
% 1.88/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k1_xboole_0 = sK3 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1030]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1697,plain,
% 1.88/1.00      ( ~ m1_orders_2(sK2,sK1,sK3)
% 1.88/1.00      | r2_hidden(sK0(sK1,sK3,sK2),sK3)
% 1.88/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k1_xboole_0 = sK3 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1541]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1428,plain,
% 1.88/1.00      ( ~ m1_orders_2(X0_45,sK1,sK2)
% 1.88/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k3_orders_2(sK1,sK2,sK0(sK1,sK2,X0_45)) = X0_45
% 1.88/1.00      | k1_xboole_0 = sK2 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1029]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1499,plain,
% 1.88/1.00      ( ~ m1_orders_2(sK3,sK1,sK2)
% 1.88/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK3)) = sK3
% 1.88/1.00      | k1_xboole_0 = sK2 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1428]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_10,negated_conjecture,
% 1.88/1.00      ( m1_orders_2(sK3,sK1,sK2) ),
% 1.88/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_534,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1))
% 1.88/1.00      | sK2 != X0
% 1.88/1.00      | sK1 != sK1
% 1.88/1.00      | sK3 != X1
% 1.88/1.00      | k1_xboole_0 = X0 ),
% 1.88/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_313]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_535,plain,
% 1.88/1.00      ( m1_subset_1(sK0(sK1,sK2,sK3),u1_struct_0(sK1))
% 1.88/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.88/1.00      | k1_xboole_0 = sK2 ),
% 1.88/1.00      inference(unflattening,[status(thm)],[c_534]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(contradiction,plain,
% 1.88/1.00      ( $false ),
% 1.88/1.00      inference(minisat,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_2581,c_2580,c_2456,c_2317,c_2124,c_1950,c_1895,c_1783,
% 1.88/1.00                 c_1789,c_1785,c_1700,c_1697,c_1499,c_1485,c_1442,c_1037,
% 1.88/1.00                 c_535,c_10,c_27,c_11,c_12,c_13,c_14]) ).
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.88/1.00  
% 1.88/1.00  ------                               Statistics
% 1.88/1.00  
% 1.88/1.00  ------ General
% 1.88/1.00  
% 1.88/1.00  abstr_ref_over_cycles:                  0
% 1.88/1.00  abstr_ref_under_cycles:                 0
% 1.88/1.00  gc_basic_clause_elim:                   0
% 1.88/1.00  forced_gc_time:                         0
% 1.88/1.00  parsing_time:                           0.012
% 1.88/1.00  unif_index_cands_time:                  0.
% 1.88/1.00  unif_index_add_time:                    0.
% 1.88/1.00  orderings_time:                         0.
% 1.88/1.00  out_proof_time:                         0.014
% 1.88/1.00  total_time:                             0.143
% 1.88/1.00  num_of_symbols:                         48
% 1.88/1.00  num_of_terms:                           2244
% 1.88/1.00  
% 1.88/1.00  ------ Preprocessing
% 1.88/1.00  
% 1.88/1.00  num_of_splits:                          0
% 1.88/1.00  num_of_split_atoms:                     0
% 1.88/1.00  num_of_reused_defs:                     0
% 1.88/1.00  num_eq_ax_congr_red:                    20
% 1.88/1.00  num_of_sem_filtered_clauses:            1
% 1.88/1.00  num_of_subtypes:                        3
% 1.88/1.00  monotx_restored_types:                  0
% 1.88/1.00  sat_num_of_epr_types:                   0
% 1.88/1.00  sat_num_of_non_cyclic_types:            0
% 1.88/1.00  sat_guarded_non_collapsed_types:        1
% 1.88/1.00  num_pure_diseq_elim:                    0
% 1.88/1.00  simp_replaced_by:                       0
% 1.88/1.00  res_preprocessed:                       75
% 1.88/1.00  prep_upred:                             0
% 1.88/1.00  prep_unflattend:                        67
% 1.88/1.00  smt_new_axioms:                         0
% 1.88/1.00  pred_elim_cands:                        3
% 1.88/1.00  pred_elim:                              6
% 1.88/1.00  pred_elim_cl:                           6
% 1.88/1.00  pred_elim_cycles:                       8
% 1.88/1.00  merged_defs:                            0
% 1.88/1.00  merged_defs_ncl:                        0
% 1.88/1.00  bin_hyper_res:                          0
% 1.88/1.00  prep_cycles:                            4
% 1.88/1.00  pred_elim_time:                         0.016
% 1.88/1.00  splitting_time:                         0.
% 1.88/1.00  sem_filter_time:                        0.
% 1.88/1.00  monotx_time:                            0.
% 1.88/1.00  subtype_inf_time:                       0.
% 1.88/1.00  
% 1.88/1.00  ------ Problem properties
% 1.88/1.00  
% 1.88/1.00  clauses:                                14
% 1.88/1.00  conjectures:                            5
% 1.88/1.00  epr:                                    3
% 1.88/1.00  horn:                                   10
% 1.88/1.00  ground:                                 6
% 1.88/1.00  unary:                                  5
% 1.88/1.00  binary:                                 1
% 1.88/1.00  lits:                                   47
% 1.88/1.00  lits_eq:                                7
% 1.88/1.00  fd_pure:                                0
% 1.88/1.00  fd_pseudo:                              0
% 1.88/1.00  fd_cond:                                4
% 1.88/1.00  fd_pseudo_cond:                         0
% 1.88/1.00  ac_symbols:                             0
% 1.88/1.00  
% 1.88/1.00  ------ Propositional Solver
% 1.88/1.00  
% 1.88/1.00  prop_solver_calls:                      28
% 1.88/1.00  prop_fast_solver_calls:                 921
% 1.88/1.00  smt_solver_calls:                       0
% 1.88/1.00  smt_fast_solver_calls:                  0
% 1.88/1.00  prop_num_of_clauses:                    709
% 1.88/1.00  prop_preprocess_simplified:             2563
% 1.88/1.00  prop_fo_subsumed:                       82
% 1.88/1.00  prop_solver_time:                       0.
% 1.88/1.00  smt_solver_time:                        0.
% 1.88/1.00  smt_fast_solver_time:                   0.
% 1.88/1.00  prop_fast_solver_time:                  0.
% 1.88/1.00  prop_unsat_core_time:                   0.
% 1.88/1.00  
% 1.88/1.00  ------ QBF
% 1.88/1.00  
% 1.88/1.00  qbf_q_res:                              0
% 1.88/1.00  qbf_num_tautologies:                    0
% 1.88/1.00  qbf_prep_cycles:                        0
% 1.88/1.00  
% 1.88/1.00  ------ BMC1
% 1.88/1.00  
% 1.88/1.00  bmc1_current_bound:                     -1
% 1.88/1.00  bmc1_last_solved_bound:                 -1
% 1.88/1.00  bmc1_unsat_core_size:                   -1
% 1.88/1.00  bmc1_unsat_core_parents_size:           -1
% 1.88/1.00  bmc1_merge_next_fun:                    0
% 1.88/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.88/1.00  
% 1.88/1.00  ------ Instantiation
% 1.88/1.00  
% 1.88/1.00  inst_num_of_clauses:                    187
% 1.88/1.00  inst_num_in_passive:                    37
% 1.88/1.00  inst_num_in_active:                     119
% 1.88/1.00  inst_num_in_unprocessed:                30
% 1.88/1.00  inst_num_of_loops:                      129
% 1.88/1.00  inst_num_of_learning_restarts:          0
% 1.88/1.00  inst_num_moves_active_passive:          4
% 1.88/1.00  inst_lit_activity:                      0
% 1.88/1.00  inst_lit_activity_moves:                0
% 1.88/1.00  inst_num_tautologies:                   0
% 1.88/1.00  inst_num_prop_implied:                  0
% 1.88/1.00  inst_num_existing_simplified:           0
% 1.88/1.00  inst_num_eq_res_simplified:             0
% 1.88/1.00  inst_num_child_elim:                    0
% 1.88/1.00  inst_num_of_dismatching_blockings:      5
% 1.88/1.00  inst_num_of_non_proper_insts:           159
% 1.88/1.00  inst_num_of_duplicates:                 0
% 1.88/1.00  inst_inst_num_from_inst_to_res:         0
% 1.88/1.00  inst_dismatching_checking_time:         0.
% 1.88/1.00  
% 1.88/1.00  ------ Resolution
% 1.88/1.00  
% 1.88/1.00  res_num_of_clauses:                     0
% 1.88/1.00  res_num_in_passive:                     0
% 1.88/1.00  res_num_in_active:                      0
% 1.88/1.00  res_num_of_loops:                       79
% 1.88/1.00  res_forward_subset_subsumed:            28
% 1.88/1.00  res_backward_subset_subsumed:           0
% 1.88/1.00  res_forward_subsumed:                   0
% 1.88/1.00  res_backward_subsumed:                  0
% 1.88/1.00  res_forward_subsumption_resolution:     0
% 1.88/1.00  res_backward_subsumption_resolution:    0
% 1.88/1.00  res_clause_to_clause_subsumption:       183
% 1.88/1.00  res_orphan_elimination:                 0
% 1.88/1.00  res_tautology_del:                      20
% 1.88/1.00  res_num_eq_res_simplified:              0
% 1.88/1.00  res_num_sel_changes:                    0
% 1.88/1.00  res_moves_from_active_to_pass:          0
% 1.88/1.00  
% 1.88/1.00  ------ Superposition
% 1.88/1.00  
% 1.88/1.00  sup_time_total:                         0.
% 1.88/1.00  sup_time_generating:                    0.
% 1.88/1.00  sup_time_sim_full:                      0.
% 1.88/1.00  sup_time_sim_immed:                     0.
% 1.88/1.00  
% 1.88/1.00  sup_num_of_clauses:                     33
% 1.88/1.00  sup_num_in_active:                      24
% 1.88/1.00  sup_num_in_passive:                     9
% 1.88/1.00  sup_num_of_loops:                       24
% 1.88/1.00  sup_fw_superposition:                   12
% 1.88/1.00  sup_bw_superposition:                   11
% 1.88/1.00  sup_immediate_simplified:               5
% 1.88/1.00  sup_given_eliminated:                   0
% 1.88/1.00  comparisons_done:                       0
% 1.88/1.00  comparisons_avoided:                    1
% 1.88/1.00  
% 1.88/1.00  ------ Simplifications
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  sim_fw_subset_subsumed:                 0
% 1.88/1.00  sim_bw_subset_subsumed:                 0
% 1.88/1.00  sim_fw_subsumed:                        3
% 1.88/1.00  sim_bw_subsumed:                        0
% 1.88/1.00  sim_fw_subsumption_res:                 0
% 1.88/1.00  sim_bw_subsumption_res:                 0
% 1.88/1.00  sim_tautology_del:                      1
% 1.88/1.00  sim_eq_tautology_del:                   0
% 1.88/1.00  sim_eq_res_simp:                        0
% 1.88/1.00  sim_fw_demodulated:                     2
% 1.88/1.00  sim_bw_demodulated:                     0
% 1.88/1.00  sim_light_normalised:                   4
% 1.88/1.00  sim_joinable_taut:                      0
% 1.88/1.00  sim_joinable_simp:                      0
% 1.88/1.00  sim_ac_normalised:                      0
% 1.88/1.00  sim_smt_subsumption:                    0
% 1.88/1.00  
%------------------------------------------------------------------------------
