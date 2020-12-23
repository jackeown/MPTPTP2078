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
% DateTime   : Thu Dec  3 12:12:44 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 631 expanded)
%              Number of clauses        :   82 ( 128 expanded)
%              Number of leaves         :   15 ( 238 expanded)
%              Depth                    :   31
%              Number of atoms          :  769 (5086 expanded)
%              Number of equality atoms :  153 (1297 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f27])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK0(X0,X1),X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

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
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(cnf_transformation,[],[f31])).

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
              ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X2)
                 => ( k1_funct_1(X2,u1_struct_0(X0)) = X1
                   => k1_xboole_0 = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
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
                ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X2)
                   => ( k1_funct_1(X2,u1_struct_0(X0)) = X1
                     => k1_xboole_0 = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(X0)) = X1
                  & m2_orders_2(X3,X0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(X0)) = X1
                  & m2_orders_2(X3,X0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
          & k1_funct_1(X2,u1_struct_0(X0)) = X1
          & m2_orders_2(X3,X0,X2) )
     => ( k1_xboole_0 != k3_orders_2(X0,sK4,X1)
        & k1_funct_1(X2,u1_struct_0(X0)) = X1
        & m2_orders_2(sK4,X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
              & k1_funct_1(X2,u1_struct_0(X0)) = X1
              & m2_orders_2(X3,X0,X2) )
          & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
            & k1_funct_1(sK3,u1_struct_0(X0)) = X1
            & m2_orders_2(X3,X0,sK3) )
        & m1_orders_1(sK3,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(X0)) = X1
                  & m2_orders_2(X3,X0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k1_xboole_0 != k3_orders_2(X0,X3,sK2)
                & k1_funct_1(X2,u1_struct_0(X0)) = sK2
                & m2_orders_2(X3,X0,X2) )
            & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                    & k1_funct_1(X2,u1_struct_0(X0)) = X1
                    & m2_orders_2(X3,X0,X2) )
                & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(sK1,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(sK1)) = X1
                  & m2_orders_2(X3,sK1,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k1_xboole_0 != k3_orders_2(sK1,sK4,sK2)
    & k1_funct_1(sK3,u1_struct_0(sK1)) = sK2
    & m2_orders_2(sK4,sK1,sK3)
    & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f35,f34,f33,f32])).

fof(f52,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

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

fof(f39,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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
                  ( m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
                 => ! [X4] :
                      ( m2_orders_2(X4,X0,X3)
                     => ( ( k1_funct_1(X3,u1_struct_0(X0)) = X2
                          & r2_hidden(X1,X4) )
                       => r3_orders_2(X0,X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X2,X1)
                      | k1_funct_1(X3,u1_struct_0(X0)) != X2
                      | ~ r2_hidden(X1,X4)
                      | ~ m2_orders_2(X4,X0,X3) )
                  | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X2,X1)
                      | k1_funct_1(X3,u1_struct_0(X0)) != X2
                      | ~ r2_hidden(X1,X4)
                      | ~ m2_orders_2(X4,X0,X3) )
                  | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X2,X1)
      | k1_funct_1(X3,u1_struct_0(X0)) != X2
      | ~ r2_hidden(X1,X4)
      | ~ m2_orders_2(X4,X0,X3)
      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,k1_funct_1(X3,u1_struct_0(X0)),X1)
      | ~ r2_hidden(X1,X4)
      | ~ m2_orders_2(X4,X0,X3)
      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_funct_1(X3,u1_struct_0(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f55,plain,(
    m2_orders_2(sK4,sK1,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X0),X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X0_52))
    | m1_subset_1(sK0(X0_52,X0_51),X0_52)
    | k1_xboole_0 = X0_51 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_705,plain,
    ( k1_xboole_0 = X0_51
    | m1_subset_1(X0_51,k1_zfmisc_1(X0_52)) != iProver_top
    | m1_subset_1(sK0(X0_52,X0_51),X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(sK0(X1,X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_548,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X0_52))
    | r2_hidden(sK0(X0_52,X0_51),X0_51)
    | k1_xboole_0 = X0_51 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_704,plain,
    ( k1_xboole_0 = X0_51
    | m1_subset_1(X0_51,k1_zfmisc_1(X0_52)) != iProver_top
    | r2_hidden(sK0(X0_52,X0_51),X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_548])).

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
    inference(cnf_transformation,[],[f45])).

cnf(c_16,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_416,plain,
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
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_18,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_20,c_19,c_18,c_17])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK1))
    | ~ m1_subset_1(X2_51,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0_51,X2_51)
    | ~ r2_hidden(X0_51,k3_orders_2(sK1,X2_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_421])).

cnf(c_710,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0_51,X2_51) = iProver_top
    | r2_hidden(X0_51,k3_orders_2(sK1,X2_51,X1_51)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_1098,plain,
    ( k3_orders_2(sK1,X0_51,X1_51) = k1_xboole_0
    | m1_subset_1(X1_51,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_orders_2(sK1,X0_51,X1_51),k1_zfmisc_1(X0_52)) != iProver_top
    | m1_subset_1(sK0(X0_52,k3_orders_2(sK1,X0_51,X1_51)),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(X0_52,k3_orders_2(sK1,X0_51,X1_51)),X0_51) = iProver_top ),
    inference(superposition,[status(thm)],[c_704,c_710])).

cnf(c_1260,plain,
    ( k3_orders_2(sK1,X0_51,X1_51) = k1_xboole_0
    | m1_subset_1(X1_51,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_orders_2(sK1,X0_51,X1_51),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK1),k3_orders_2(sK1,X0_51,X1_51)),X0_51) = iProver_top ),
    inference(superposition,[status(thm)],[c_705,c_1098])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_16])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_20,c_19,c_18,c_17])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_orders_2(sK1,X1_51,X0_51),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_448])).

cnf(c_711,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_orders_2(sK1,X1_51,X0_51),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_1337,plain,
    ( k3_orders_2(sK1,X0_51,X1_51) = k1_xboole_0
    | m1_subset_1(X1_51,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK1),k3_orders_2(sK1,X0_51,X1_51)),X0_51) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1260,c_711])).

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
    inference(cnf_transformation,[],[f44])).

cnf(c_6,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_5,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_10,plain,
    ( r3_orders_2(X0,k1_funct_1(X1,u1_struct_0(X0)),X2)
    | ~ m2_orders_2(X3,X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(X0)),u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_13,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_224,plain,
    ( r3_orders_2(X0,k1_funct_1(X1,u1_struct_0(X0)),X2)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(X0)),u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X1
    | sK4 != X3
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_225,plain,
    ( r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
    | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK4)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_14,negated_conjecture,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_229,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_225,c_20,c_19,c_18,c_17,c_16,c_14])).

cnf(c_230,plain,
    ( r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK4) ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_256,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ r2_hidden(X3,sK4)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X3 != X2
    | k1_funct_1(sK3,u1_struct_0(sK1)) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_230])).

cnf(c_257,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK4)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_261,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_257,c_20,c_19,c_16])).

cnf(c_262,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK4) ),
    inference(renaming,[status(thm)],[c_261])).

cnf(c_285,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ r2_hidden(X3,sK4)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X3 != X1
    | k1_funct_1(sK3,u1_struct_0(sK1)) != X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_262])).

cnf(c_286,plain,
    ( ~ r2_orders_2(sK1,X0,k1_funct_1(sK3,u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK4)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_290,plain,
    ( ~ r2_orders_2(sK1,X0,k1_funct_1(sK3,u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_286,c_17,c_16])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ r2_hidden(X2,k3_orders_2(X1,X4,X0))
    | ~ r2_hidden(X3,sK4)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X3 != X2
    | k1_funct_1(sK3,u1_struct_0(sK1)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_290])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,k1_funct_1(sK3,u1_struct_0(sK1))))
    | ~ r2_hidden(X0,sK4)
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_358,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,k1_funct_1(sK3,u1_struct_0(sK1))))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_20,c_19,c_18,c_17,c_16])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,k1_funct_1(sK3,u1_struct_0(sK1))))
    | ~ r2_hidden(X0,sK4) ),
    inference(renaming,[status(thm)],[c_358])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ r2_hidden(X0_51,k3_orders_2(sK1,X1_51,k1_funct_1(sK3,u1_struct_0(sK1))))
    | ~ r2_hidden(X0_51,sK4) ),
    inference(subtyping,[status(esa)],[c_359])).

cnf(c_708,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_51,k3_orders_2(sK1,X1_51,k1_funct_1(sK3,u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(X0_51,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_12,negated_conjecture,
    ( k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_545,negated_conjecture,
    ( k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_748,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_51,k3_orders_2(sK1,X1_51,sK2)) != iProver_top
    | r2_hidden(X0_51,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_708,c_545])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_544,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_706,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_754,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(X0_51,k3_orders_2(sK1,X1_51,sK2)) != iProver_top
    | r2_hidden(X0_51,sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_748,c_706])).

cnf(c_1099,plain,
    ( k3_orders_2(sK1,X0_51,sK2) = k1_xboole_0
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_orders_2(sK1,X0_51,sK2),k1_zfmisc_1(X0_52)) != iProver_top
    | m1_subset_1(sK0(X0_52,k3_orders_2(sK1,X0_51,sK2)),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(X0_52,k3_orders_2(sK1,X0_51,sK2)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_704,c_754])).

cnf(c_1207,plain,
    ( k3_orders_2(sK1,X0_51,sK2) = k1_xboole_0
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_orders_2(sK1,X0_51,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK1),k3_orders_2(sK1,X0_51,sK2)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_705,c_1099])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_793,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_orders_2(sK1,X0_51,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_794,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_orders_2(sK1,X0_51,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_793])).

cnf(c_1212,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | k3_orders_2(sK1,X0_51,sK2) = k1_xboole_0
    | r2_hidden(sK0(u1_struct_0(sK1),k3_orders_2(sK1,X0_51,sK2)),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1207,c_26,c_794])).

cnf(c_1213,plain,
    ( k3_orders_2(sK1,X0_51,sK2) = k1_xboole_0
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK1),k3_orders_2(sK1,X0_51,sK2)),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_1212])).

cnf(c_1344,plain,
    ( k3_orders_2(sK1,sK4,sK2) = k1_xboole_0
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1213])).

cnf(c_551,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_818,plain,
    ( k3_orders_2(sK1,sK4,sK2) != X0_51
    | k1_xboole_0 != X0_51
    | k1_xboole_0 = k3_orders_2(sK1,sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_819,plain,
    ( k3_orders_2(sK1,sK4,sK2) != k1_xboole_0
    | k1_xboole_0 = k3_orders_2(sK1,sK4,sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_546,negated_conjecture,
    ( k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_550,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_559,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_3,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_213,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X0
    | sK4 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_214,plain,
    ( ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_215,plain,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v3_orders_2(sK1) != iProver_top
    | v4_orders_2(sK1) != iProver_top
    | v5_orders_2(sK1) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_214])).

cnf(c_27,plain,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_25,plain,
    ( l1_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_24,plain,
    ( v5_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_23,plain,
    ( v4_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_22,plain,
    ( v3_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1344,c_819,c_546,c_559,c_215,c_27,c_26,c_25,c_24,c_23,c_22,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:53:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.99/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/0.99  
% 1.99/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.99/0.99  
% 1.99/0.99  ------  iProver source info
% 1.99/0.99  
% 1.99/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.99/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.99/0.99  git: non_committed_changes: false
% 1.99/0.99  git: last_make_outside_of_git: false
% 1.99/0.99  
% 1.99/0.99  ------ 
% 1.99/0.99  
% 1.99/0.99  ------ Input Options
% 1.99/0.99  
% 1.99/0.99  --out_options                           all
% 1.99/0.99  --tptp_safe_out                         true
% 1.99/0.99  --problem_path                          ""
% 1.99/0.99  --include_path                          ""
% 1.99/0.99  --clausifier                            res/vclausify_rel
% 1.99/0.99  --clausifier_options                    --mode clausify
% 1.99/0.99  --stdin                                 false
% 1.99/0.99  --stats_out                             all
% 1.99/0.99  
% 1.99/0.99  ------ General Options
% 1.99/0.99  
% 1.99/0.99  --fof                                   false
% 1.99/0.99  --time_out_real                         305.
% 1.99/0.99  --time_out_virtual                      -1.
% 1.99/0.99  --symbol_type_check                     false
% 1.99/0.99  --clausify_out                          false
% 1.99/0.99  --sig_cnt_out                           false
% 1.99/0.99  --trig_cnt_out                          false
% 1.99/0.99  --trig_cnt_out_tolerance                1.
% 1.99/0.99  --trig_cnt_out_sk_spl                   false
% 1.99/0.99  --abstr_cl_out                          false
% 1.99/0.99  
% 1.99/0.99  ------ Global Options
% 1.99/0.99  
% 1.99/0.99  --schedule                              default
% 1.99/0.99  --add_important_lit                     false
% 1.99/0.99  --prop_solver_per_cl                    1000
% 1.99/0.99  --min_unsat_core                        false
% 1.99/0.99  --soft_assumptions                      false
% 1.99/0.99  --soft_lemma_size                       3
% 1.99/0.99  --prop_impl_unit_size                   0
% 1.99/0.99  --prop_impl_unit                        []
% 1.99/0.99  --share_sel_clauses                     true
% 1.99/0.99  --reset_solvers                         false
% 1.99/0.99  --bc_imp_inh                            [conj_cone]
% 1.99/0.99  --conj_cone_tolerance                   3.
% 1.99/0.99  --extra_neg_conj                        none
% 1.99/0.99  --large_theory_mode                     true
% 1.99/0.99  --prolific_symb_bound                   200
% 1.99/0.99  --lt_threshold                          2000
% 1.99/0.99  --clause_weak_htbl                      true
% 1.99/0.99  --gc_record_bc_elim                     false
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing Options
% 1.99/0.99  
% 1.99/0.99  --preprocessing_flag                    true
% 1.99/0.99  --time_out_prep_mult                    0.1
% 1.99/0.99  --splitting_mode                        input
% 1.99/0.99  --splitting_grd                         true
% 1.99/0.99  --splitting_cvd                         false
% 1.99/0.99  --splitting_cvd_svl                     false
% 1.99/0.99  --splitting_nvd                         32
% 1.99/0.99  --sub_typing                            true
% 1.99/0.99  --prep_gs_sim                           true
% 1.99/0.99  --prep_unflatten                        true
% 1.99/0.99  --prep_res_sim                          true
% 1.99/0.99  --prep_upred                            true
% 1.99/0.99  --prep_sem_filter                       exhaustive
% 1.99/0.99  --prep_sem_filter_out                   false
% 1.99/0.99  --pred_elim                             true
% 1.99/0.99  --res_sim_input                         true
% 1.99/0.99  --eq_ax_congr_red                       true
% 1.99/0.99  --pure_diseq_elim                       true
% 1.99/0.99  --brand_transform                       false
% 1.99/0.99  --non_eq_to_eq                          false
% 1.99/0.99  --prep_def_merge                        true
% 1.99/0.99  --prep_def_merge_prop_impl              false
% 1.99/0.99  --prep_def_merge_mbd                    true
% 1.99/0.99  --prep_def_merge_tr_red                 false
% 1.99/0.99  --prep_def_merge_tr_cl                  false
% 1.99/0.99  --smt_preprocessing                     true
% 1.99/0.99  --smt_ac_axioms                         fast
% 1.99/0.99  --preprocessed_out                      false
% 1.99/0.99  --preprocessed_stats                    false
% 1.99/0.99  
% 1.99/0.99  ------ Abstraction refinement Options
% 1.99/0.99  
% 1.99/0.99  --abstr_ref                             []
% 1.99/0.99  --abstr_ref_prep                        false
% 1.99/0.99  --abstr_ref_until_sat                   false
% 1.99/0.99  --abstr_ref_sig_restrict                funpre
% 1.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.99  --abstr_ref_under                       []
% 1.99/0.99  
% 1.99/0.99  ------ SAT Options
% 1.99/0.99  
% 1.99/0.99  --sat_mode                              false
% 1.99/0.99  --sat_fm_restart_options                ""
% 1.99/0.99  --sat_gr_def                            false
% 1.99/0.99  --sat_epr_types                         true
% 1.99/0.99  --sat_non_cyclic_types                  false
% 1.99/0.99  --sat_finite_models                     false
% 1.99/0.99  --sat_fm_lemmas                         false
% 1.99/0.99  --sat_fm_prep                           false
% 1.99/0.99  --sat_fm_uc_incr                        true
% 1.99/0.99  --sat_out_model                         small
% 1.99/0.99  --sat_out_clauses                       false
% 1.99/0.99  
% 1.99/0.99  ------ QBF Options
% 1.99/0.99  
% 1.99/0.99  --qbf_mode                              false
% 1.99/0.99  --qbf_elim_univ                         false
% 1.99/0.99  --qbf_dom_inst                          none
% 1.99/0.99  --qbf_dom_pre_inst                      false
% 1.99/0.99  --qbf_sk_in                             false
% 1.99/0.99  --qbf_pred_elim                         true
% 1.99/0.99  --qbf_split                             512
% 1.99/0.99  
% 1.99/0.99  ------ BMC1 Options
% 1.99/0.99  
% 1.99/0.99  --bmc1_incremental                      false
% 1.99/0.99  --bmc1_axioms                           reachable_all
% 1.99/0.99  --bmc1_min_bound                        0
% 1.99/0.99  --bmc1_max_bound                        -1
% 1.99/0.99  --bmc1_max_bound_default                -1
% 1.99/0.99  --bmc1_symbol_reachability              true
% 1.99/0.99  --bmc1_property_lemmas                  false
% 1.99/0.99  --bmc1_k_induction                      false
% 1.99/0.99  --bmc1_non_equiv_states                 false
% 1.99/0.99  --bmc1_deadlock                         false
% 1.99/0.99  --bmc1_ucm                              false
% 1.99/0.99  --bmc1_add_unsat_core                   none
% 1.99/0.99  --bmc1_unsat_core_children              false
% 1.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.99  --bmc1_out_stat                         full
% 1.99/0.99  --bmc1_ground_init                      false
% 1.99/0.99  --bmc1_pre_inst_next_state              false
% 1.99/0.99  --bmc1_pre_inst_state                   false
% 1.99/0.99  --bmc1_pre_inst_reach_state             false
% 1.99/0.99  --bmc1_out_unsat_core                   false
% 1.99/0.99  --bmc1_aig_witness_out                  false
% 1.99/0.99  --bmc1_verbose                          false
% 1.99/0.99  --bmc1_dump_clauses_tptp                false
% 1.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.99  --bmc1_dump_file                        -
% 1.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.99  --bmc1_ucm_extend_mode                  1
% 1.99/0.99  --bmc1_ucm_init_mode                    2
% 1.99/0.99  --bmc1_ucm_cone_mode                    none
% 1.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.99  --bmc1_ucm_relax_model                  4
% 1.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.99  --bmc1_ucm_layered_model                none
% 1.99/0.99  --bmc1_ucm_max_lemma_size               10
% 1.99/0.99  
% 1.99/0.99  ------ AIG Options
% 1.99/0.99  
% 1.99/0.99  --aig_mode                              false
% 1.99/0.99  
% 1.99/0.99  ------ Instantiation Options
% 1.99/0.99  
% 1.99/0.99  --instantiation_flag                    true
% 1.99/0.99  --inst_sos_flag                         false
% 1.99/0.99  --inst_sos_phase                        true
% 1.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel_side                     num_symb
% 1.99/0.99  --inst_solver_per_active                1400
% 1.99/0.99  --inst_solver_calls_frac                1.
% 1.99/0.99  --inst_passive_queue_type               priority_queues
% 1.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/0.99  --inst_passive_queues_freq              [25;2]
% 1.99/0.99  --inst_dismatching                      true
% 1.99/0.99  --inst_eager_unprocessed_to_passive     true
% 1.99/0.99  --inst_prop_sim_given                   true
% 1.99/0.99  --inst_prop_sim_new                     false
% 1.99/0.99  --inst_subs_new                         false
% 1.99/0.99  --inst_eq_res_simp                      false
% 1.99/0.99  --inst_subs_given                       false
% 1.99/0.99  --inst_orphan_elimination               true
% 1.99/0.99  --inst_learning_loop_flag               true
% 1.99/0.99  --inst_learning_start                   3000
% 1.99/0.99  --inst_learning_factor                  2
% 1.99/0.99  --inst_start_prop_sim_after_learn       3
% 1.99/0.99  --inst_sel_renew                        solver
% 1.99/0.99  --inst_lit_activity_flag                true
% 1.99/0.99  --inst_restr_to_given                   false
% 1.99/0.99  --inst_activity_threshold               500
% 1.99/0.99  --inst_out_proof                        true
% 1.99/0.99  
% 1.99/0.99  ------ Resolution Options
% 1.99/0.99  
% 1.99/0.99  --resolution_flag                       true
% 1.99/0.99  --res_lit_sel                           adaptive
% 1.99/0.99  --res_lit_sel_side                      none
% 1.99/0.99  --res_ordering                          kbo
% 1.99/0.99  --res_to_prop_solver                    active
% 1.99/0.99  --res_prop_simpl_new                    false
% 1.99/0.99  --res_prop_simpl_given                  true
% 1.99/0.99  --res_passive_queue_type                priority_queues
% 1.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/0.99  --res_passive_queues_freq               [15;5]
% 1.99/0.99  --res_forward_subs                      full
% 1.99/0.99  --res_backward_subs                     full
% 1.99/0.99  --res_forward_subs_resolution           true
% 1.99/0.99  --res_backward_subs_resolution          true
% 1.99/0.99  --res_orphan_elimination                true
% 1.99/0.99  --res_time_limit                        2.
% 1.99/0.99  --res_out_proof                         true
% 1.99/0.99  
% 1.99/0.99  ------ Superposition Options
% 1.99/0.99  
% 1.99/0.99  --superposition_flag                    true
% 1.99/0.99  --sup_passive_queue_type                priority_queues
% 1.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.99/0.99  --demod_completeness_check              fast
% 1.99/0.99  --demod_use_ground                      true
% 1.99/0.99  --sup_to_prop_solver                    passive
% 1.99/0.99  --sup_prop_simpl_new                    true
% 1.99/0.99  --sup_prop_simpl_given                  true
% 1.99/0.99  --sup_fun_splitting                     false
% 1.99/0.99  --sup_smt_interval                      50000
% 1.99/0.99  
% 1.99/0.99  ------ Superposition Simplification Setup
% 1.99/0.99  
% 1.99/0.99  --sup_indices_passive                   []
% 1.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_full_bw                           [BwDemod]
% 1.99/0.99  --sup_immed_triv                        [TrivRules]
% 1.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_immed_bw_main                     []
% 1.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.99  
% 1.99/0.99  ------ Combination Options
% 1.99/0.99  
% 1.99/0.99  --comb_res_mult                         3
% 1.99/0.99  --comb_sup_mult                         2
% 1.99/0.99  --comb_inst_mult                        10
% 1.99/0.99  
% 1.99/0.99  ------ Debug Options
% 1.99/0.99  
% 1.99/0.99  --dbg_backtrace                         false
% 1.99/0.99  --dbg_dump_prop_clauses                 false
% 1.99/0.99  --dbg_dump_prop_clauses_file            -
% 1.99/0.99  --dbg_out_stat                          false
% 1.99/0.99  ------ Parsing...
% 1.99/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.99/0.99  ------ Proving...
% 1.99/0.99  ------ Problem Properties 
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  clauses                                 10
% 1.99/0.99  conjectures                             3
% 1.99/0.99  EPR                                     0
% 1.99/0.99  Horn                                    8
% 1.99/0.99  unary                                   4
% 1.99/0.99  binary                                  0
% 1.99/0.99  lits                                    30
% 1.99/0.99  lits eq                                 4
% 1.99/0.99  fd_pure                                 0
% 1.99/0.99  fd_pseudo                               0
% 1.99/0.99  fd_cond                                 2
% 1.99/0.99  fd_pseudo_cond                          0
% 1.99/0.99  AC symbols                              0
% 1.99/0.99  
% 1.99/0.99  ------ Schedule dynamic 5 is on 
% 1.99/0.99  
% 1.99/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  ------ 
% 1.99/0.99  Current options:
% 1.99/0.99  ------ 
% 1.99/0.99  
% 1.99/0.99  ------ Input Options
% 1.99/0.99  
% 1.99/0.99  --out_options                           all
% 1.99/0.99  --tptp_safe_out                         true
% 1.99/0.99  --problem_path                          ""
% 1.99/0.99  --include_path                          ""
% 1.99/0.99  --clausifier                            res/vclausify_rel
% 1.99/0.99  --clausifier_options                    --mode clausify
% 1.99/0.99  --stdin                                 false
% 1.99/0.99  --stats_out                             all
% 1.99/0.99  
% 1.99/0.99  ------ General Options
% 1.99/0.99  
% 1.99/0.99  --fof                                   false
% 1.99/0.99  --time_out_real                         305.
% 1.99/0.99  --time_out_virtual                      -1.
% 1.99/0.99  --symbol_type_check                     false
% 1.99/0.99  --clausify_out                          false
% 1.99/0.99  --sig_cnt_out                           false
% 1.99/0.99  --trig_cnt_out                          false
% 1.99/0.99  --trig_cnt_out_tolerance                1.
% 1.99/0.99  --trig_cnt_out_sk_spl                   false
% 1.99/0.99  --abstr_cl_out                          false
% 1.99/0.99  
% 1.99/0.99  ------ Global Options
% 1.99/0.99  
% 1.99/0.99  --schedule                              default
% 1.99/0.99  --add_important_lit                     false
% 1.99/0.99  --prop_solver_per_cl                    1000
% 1.99/0.99  --min_unsat_core                        false
% 1.99/0.99  --soft_assumptions                      false
% 1.99/0.99  --soft_lemma_size                       3
% 1.99/0.99  --prop_impl_unit_size                   0
% 1.99/0.99  --prop_impl_unit                        []
% 1.99/0.99  --share_sel_clauses                     true
% 1.99/0.99  --reset_solvers                         false
% 1.99/0.99  --bc_imp_inh                            [conj_cone]
% 1.99/0.99  --conj_cone_tolerance                   3.
% 1.99/0.99  --extra_neg_conj                        none
% 1.99/0.99  --large_theory_mode                     true
% 1.99/0.99  --prolific_symb_bound                   200
% 1.99/0.99  --lt_threshold                          2000
% 1.99/0.99  --clause_weak_htbl                      true
% 1.99/0.99  --gc_record_bc_elim                     false
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing Options
% 1.99/0.99  
% 1.99/0.99  --preprocessing_flag                    true
% 1.99/0.99  --time_out_prep_mult                    0.1
% 1.99/0.99  --splitting_mode                        input
% 1.99/0.99  --splitting_grd                         true
% 1.99/0.99  --splitting_cvd                         false
% 1.99/0.99  --splitting_cvd_svl                     false
% 1.99/0.99  --splitting_nvd                         32
% 1.99/0.99  --sub_typing                            true
% 1.99/0.99  --prep_gs_sim                           true
% 1.99/0.99  --prep_unflatten                        true
% 1.99/0.99  --prep_res_sim                          true
% 1.99/0.99  --prep_upred                            true
% 1.99/0.99  --prep_sem_filter                       exhaustive
% 1.99/0.99  --prep_sem_filter_out                   false
% 1.99/0.99  --pred_elim                             true
% 1.99/0.99  --res_sim_input                         true
% 1.99/0.99  --eq_ax_congr_red                       true
% 1.99/0.99  --pure_diseq_elim                       true
% 1.99/0.99  --brand_transform                       false
% 1.99/0.99  --non_eq_to_eq                          false
% 1.99/0.99  --prep_def_merge                        true
% 1.99/0.99  --prep_def_merge_prop_impl              false
% 1.99/0.99  --prep_def_merge_mbd                    true
% 1.99/0.99  --prep_def_merge_tr_red                 false
% 1.99/0.99  --prep_def_merge_tr_cl                  false
% 1.99/0.99  --smt_preprocessing                     true
% 1.99/0.99  --smt_ac_axioms                         fast
% 1.99/0.99  --preprocessed_out                      false
% 1.99/0.99  --preprocessed_stats                    false
% 1.99/0.99  
% 1.99/0.99  ------ Abstraction refinement Options
% 1.99/0.99  
% 1.99/0.99  --abstr_ref                             []
% 1.99/0.99  --abstr_ref_prep                        false
% 1.99/0.99  --abstr_ref_until_sat                   false
% 1.99/0.99  --abstr_ref_sig_restrict                funpre
% 1.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.99  --abstr_ref_under                       []
% 1.99/0.99  
% 1.99/0.99  ------ SAT Options
% 1.99/0.99  
% 1.99/0.99  --sat_mode                              false
% 1.99/0.99  --sat_fm_restart_options                ""
% 1.99/0.99  --sat_gr_def                            false
% 1.99/0.99  --sat_epr_types                         true
% 1.99/0.99  --sat_non_cyclic_types                  false
% 1.99/0.99  --sat_finite_models                     false
% 1.99/0.99  --sat_fm_lemmas                         false
% 1.99/0.99  --sat_fm_prep                           false
% 1.99/0.99  --sat_fm_uc_incr                        true
% 1.99/0.99  --sat_out_model                         small
% 1.99/0.99  --sat_out_clauses                       false
% 1.99/0.99  
% 1.99/0.99  ------ QBF Options
% 1.99/0.99  
% 1.99/0.99  --qbf_mode                              false
% 1.99/0.99  --qbf_elim_univ                         false
% 1.99/0.99  --qbf_dom_inst                          none
% 1.99/0.99  --qbf_dom_pre_inst                      false
% 1.99/0.99  --qbf_sk_in                             false
% 1.99/0.99  --qbf_pred_elim                         true
% 1.99/0.99  --qbf_split                             512
% 1.99/0.99  
% 1.99/0.99  ------ BMC1 Options
% 1.99/0.99  
% 1.99/0.99  --bmc1_incremental                      false
% 1.99/0.99  --bmc1_axioms                           reachable_all
% 1.99/0.99  --bmc1_min_bound                        0
% 1.99/0.99  --bmc1_max_bound                        -1
% 1.99/0.99  --bmc1_max_bound_default                -1
% 1.99/0.99  --bmc1_symbol_reachability              true
% 1.99/0.99  --bmc1_property_lemmas                  false
% 1.99/0.99  --bmc1_k_induction                      false
% 1.99/0.99  --bmc1_non_equiv_states                 false
% 1.99/0.99  --bmc1_deadlock                         false
% 1.99/0.99  --bmc1_ucm                              false
% 1.99/0.99  --bmc1_add_unsat_core                   none
% 1.99/0.99  --bmc1_unsat_core_children              false
% 1.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.99  --bmc1_out_stat                         full
% 1.99/0.99  --bmc1_ground_init                      false
% 1.99/0.99  --bmc1_pre_inst_next_state              false
% 1.99/0.99  --bmc1_pre_inst_state                   false
% 1.99/0.99  --bmc1_pre_inst_reach_state             false
% 1.99/0.99  --bmc1_out_unsat_core                   false
% 1.99/0.99  --bmc1_aig_witness_out                  false
% 1.99/0.99  --bmc1_verbose                          false
% 1.99/0.99  --bmc1_dump_clauses_tptp                false
% 1.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.99  --bmc1_dump_file                        -
% 1.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.99  --bmc1_ucm_extend_mode                  1
% 1.99/0.99  --bmc1_ucm_init_mode                    2
% 1.99/0.99  --bmc1_ucm_cone_mode                    none
% 1.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.99  --bmc1_ucm_relax_model                  4
% 1.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.99  --bmc1_ucm_layered_model                none
% 1.99/0.99  --bmc1_ucm_max_lemma_size               10
% 1.99/0.99  
% 1.99/0.99  ------ AIG Options
% 1.99/0.99  
% 1.99/0.99  --aig_mode                              false
% 1.99/0.99  
% 1.99/0.99  ------ Instantiation Options
% 1.99/0.99  
% 1.99/0.99  --instantiation_flag                    true
% 1.99/0.99  --inst_sos_flag                         false
% 1.99/0.99  --inst_sos_phase                        true
% 1.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel_side                     none
% 1.99/0.99  --inst_solver_per_active                1400
% 1.99/0.99  --inst_solver_calls_frac                1.
% 1.99/0.99  --inst_passive_queue_type               priority_queues
% 1.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/0.99  --inst_passive_queues_freq              [25;2]
% 1.99/0.99  --inst_dismatching                      true
% 1.99/0.99  --inst_eager_unprocessed_to_passive     true
% 1.99/0.99  --inst_prop_sim_given                   true
% 1.99/0.99  --inst_prop_sim_new                     false
% 1.99/0.99  --inst_subs_new                         false
% 1.99/0.99  --inst_eq_res_simp                      false
% 1.99/0.99  --inst_subs_given                       false
% 1.99/0.99  --inst_orphan_elimination               true
% 1.99/0.99  --inst_learning_loop_flag               true
% 1.99/0.99  --inst_learning_start                   3000
% 1.99/0.99  --inst_learning_factor                  2
% 1.99/0.99  --inst_start_prop_sim_after_learn       3
% 1.99/0.99  --inst_sel_renew                        solver
% 1.99/0.99  --inst_lit_activity_flag                true
% 1.99/0.99  --inst_restr_to_given                   false
% 1.99/0.99  --inst_activity_threshold               500
% 1.99/0.99  --inst_out_proof                        true
% 1.99/0.99  
% 1.99/0.99  ------ Resolution Options
% 1.99/0.99  
% 1.99/0.99  --resolution_flag                       false
% 1.99/0.99  --res_lit_sel                           adaptive
% 1.99/0.99  --res_lit_sel_side                      none
% 1.99/0.99  --res_ordering                          kbo
% 1.99/0.99  --res_to_prop_solver                    active
% 1.99/0.99  --res_prop_simpl_new                    false
% 1.99/0.99  --res_prop_simpl_given                  true
% 1.99/0.99  --res_passive_queue_type                priority_queues
% 1.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/0.99  --res_passive_queues_freq               [15;5]
% 1.99/0.99  --res_forward_subs                      full
% 1.99/0.99  --res_backward_subs                     full
% 1.99/0.99  --res_forward_subs_resolution           true
% 1.99/0.99  --res_backward_subs_resolution          true
% 1.99/0.99  --res_orphan_elimination                true
% 1.99/0.99  --res_time_limit                        2.
% 1.99/0.99  --res_out_proof                         true
% 1.99/0.99  
% 1.99/0.99  ------ Superposition Options
% 1.99/0.99  
% 1.99/0.99  --superposition_flag                    true
% 1.99/0.99  --sup_passive_queue_type                priority_queues
% 1.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.99/0.99  --demod_completeness_check              fast
% 1.99/0.99  --demod_use_ground                      true
% 1.99/0.99  --sup_to_prop_solver                    passive
% 1.99/0.99  --sup_prop_simpl_new                    true
% 1.99/0.99  --sup_prop_simpl_given                  true
% 1.99/0.99  --sup_fun_splitting                     false
% 1.99/0.99  --sup_smt_interval                      50000
% 1.99/0.99  
% 1.99/0.99  ------ Superposition Simplification Setup
% 1.99/0.99  
% 1.99/0.99  --sup_indices_passive                   []
% 1.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_full_bw                           [BwDemod]
% 1.99/0.99  --sup_immed_triv                        [TrivRules]
% 1.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_immed_bw_main                     []
% 1.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.99  
% 1.99/0.99  ------ Combination Options
% 1.99/0.99  
% 1.99/0.99  --comb_res_mult                         3
% 1.99/0.99  --comb_sup_mult                         2
% 1.99/0.99  --comb_inst_mult                        10
% 1.99/0.99  
% 1.99/0.99  ------ Debug Options
% 1.99/0.99  
% 1.99/0.99  --dbg_backtrace                         false
% 1.99/0.99  --dbg_dump_prop_clauses                 false
% 1.99/0.99  --dbg_dump_prop_clauses_file            -
% 1.99/0.99  --dbg_out_stat                          false
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  ------ Proving...
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  % SZS status Theorem for theBenchmark.p
% 1.99/0.99  
% 1.99/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.99/0.99  
% 1.99/0.99  fof(f1,axiom,(
% 1.99/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f11,plain,(
% 1.99/0.99    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f1])).
% 1.99/0.99  
% 1.99/0.99  fof(f12,plain,(
% 1.99/0.99    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.99/0.99    inference(flattening,[],[f11])).
% 1.99/0.99  
% 1.99/0.99  fof(f27,plain,(
% 1.99/0.99    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)))),
% 1.99/0.99    introduced(choice_axiom,[])).
% 1.99/0.99  
% 1.99/0.99  fof(f28,plain,(
% 1.99/0.99    ! [X0,X1] : ((r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.99/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f27])).
% 1.99/0.99  
% 1.99/0.99  fof(f37,plain,(
% 1.99/0.99    ( ! [X0,X1] : (m1_subset_1(sK0(X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.99/0.99    inference(cnf_transformation,[],[f28])).
% 1.99/0.99  
% 1.99/0.99  fof(f38,plain,(
% 1.99/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.99/0.99    inference(cnf_transformation,[],[f28])).
% 1.99/0.99  
% 1.99/0.99  fof(f6,axiom,(
% 1.99/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f21,plain,(
% 1.99/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f6])).
% 1.99/0.99  
% 1.99/0.99  fof(f22,plain,(
% 1.99/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/0.99    inference(flattening,[],[f21])).
% 1.99/0.99  
% 1.99/0.99  fof(f30,plain,(
% 1.99/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/0.99    inference(nnf_transformation,[],[f22])).
% 1.99/0.99  
% 1.99/0.99  fof(f31,plain,(
% 1.99/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/0.99    inference(flattening,[],[f30])).
% 1.99/0.99  
% 1.99/0.99  fof(f45,plain,(
% 1.99/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f31])).
% 1.99/0.99  
% 1.99/0.99  fof(f8,conjecture,(
% 1.99/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f9,negated_conjecture,(
% 1.99/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 1.99/0.99    inference(negated_conjecture,[],[f8])).
% 1.99/0.99  
% 1.99/0.99  fof(f25,plain,(
% 1.99/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1) & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f9])).
% 1.99/0.99  
% 1.99/0.99  fof(f26,plain,(
% 1.99/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.99/0.99    inference(flattening,[],[f25])).
% 1.99/0.99  
% 1.99/0.99  fof(f35,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) => (k1_xboole_0 != k3_orders_2(X0,sK4,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(sK4,X0,X2))) )),
% 1.99/0.99    introduced(choice_axiom,[])).
% 1.99/0.99  
% 1.99/0.99  fof(f34,plain,(
% 1.99/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) => (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(sK3,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,sK3)) & m1_orders_1(sK3,k1_orders_1(u1_struct_0(X0))))) )),
% 1.99/0.99    introduced(choice_axiom,[])).
% 1.99/0.99  
% 1.99/0.99  fof(f33,plain,(
% 1.99/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,sK2) & k1_funct_1(X2,u1_struct_0(X0)) = sK2 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.99/0.99    introduced(choice_axiom,[])).
% 1.99/0.99  
% 1.99/0.99  fof(f32,plain,(
% 1.99/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK1,X3,X1) & k1_funct_1(X2,u1_struct_0(sK1)) = X1 & m2_orders_2(X3,sK1,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.99/0.99    introduced(choice_axiom,[])).
% 1.99/0.99  
% 1.99/0.99  fof(f36,plain,(
% 1.99/0.99    (((k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) & k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 & m2_orders_2(sK4,sK1,sK3)) & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 1.99/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f35,f34,f33,f32])).
% 1.99/0.99  
% 1.99/0.99  fof(f52,plain,(
% 1.99/0.99    l1_orders_2(sK1)),
% 1.99/0.99    inference(cnf_transformation,[],[f36])).
% 1.99/0.99  
% 1.99/0.99  fof(f48,plain,(
% 1.99/0.99    ~v2_struct_0(sK1)),
% 1.99/0.99    inference(cnf_transformation,[],[f36])).
% 1.99/0.99  
% 1.99/0.99  fof(f49,plain,(
% 1.99/0.99    v3_orders_2(sK1)),
% 1.99/0.99    inference(cnf_transformation,[],[f36])).
% 1.99/0.99  
% 1.99/0.99  fof(f50,plain,(
% 1.99/0.99    v4_orders_2(sK1)),
% 1.99/0.99    inference(cnf_transformation,[],[f36])).
% 1.99/0.99  
% 1.99/0.99  fof(f51,plain,(
% 1.99/0.99    v5_orders_2(sK1)),
% 1.99/0.99    inference(cnf_transformation,[],[f36])).
% 1.99/0.99  
% 1.99/0.99  fof(f2,axiom,(
% 1.99/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f13,plain,(
% 1.99/0.99    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f2])).
% 1.99/0.99  
% 1.99/0.99  fof(f14,plain,(
% 1.99/0.99    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/0.99    inference(flattening,[],[f13])).
% 1.99/0.99  
% 1.99/0.99  fof(f39,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f14])).
% 1.99/0.99  
% 1.99/0.99  fof(f44,plain,(
% 1.99/0.99    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f31])).
% 1.99/0.99  
% 1.99/0.99  fof(f5,axiom,(
% 1.99/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(r2_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)))))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f19,plain,(
% 1.99/0.99    ! [X0] : (! [X1] : (! [X2] : ((~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f5])).
% 1.99/0.99  
% 1.99/0.99  fof(f20,plain,(
% 1.99/0.99    ! [X0] : (! [X1] : (! [X2] : (~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.99/0.99    inference(flattening,[],[f19])).
% 1.99/0.99  
% 1.99/0.99  fof(f43,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f20])).
% 1.99/0.99  
% 1.99/0.99  fof(f4,axiom,(
% 1.99/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f17,plain,(
% 1.99/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f4])).
% 1.99/0.99  
% 1.99/0.99  fof(f18,plain,(
% 1.99/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/0.99    inference(flattening,[],[f17])).
% 1.99/0.99  
% 1.99/0.99  fof(f29,plain,(
% 1.99/0.99    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/0.99    inference(nnf_transformation,[],[f18])).
% 1.99/0.99  
% 1.99/0.99  fof(f41,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f29])).
% 1.99/0.99  
% 1.99/0.99  fof(f7,axiom,(
% 1.99/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) => ! [X4] : (m2_orders_2(X4,X0,X3) => ((k1_funct_1(X3,u1_struct_0(X0)) = X2 & r2_hidden(X1,X4)) => r3_orders_2(X0,X2,X1)))))))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f23,plain,(
% 1.99/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r3_orders_2(X0,X2,X1) | (k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4))) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f7])).
% 1.99/0.99  
% 1.99/0.99  fof(f24,plain,(
% 1.99/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/0.99    inference(flattening,[],[f23])).
% 1.99/0.99  
% 1.99/0.99  fof(f47,plain,(
% 1.99/0.99    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f24])).
% 1.99/0.99  
% 1.99/0.99  fof(f58,plain,(
% 1.99/0.99    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,k1_funct_1(X3,u1_struct_0(X0)),X1) | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(k1_funct_1(X3,u1_struct_0(X0)),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(equality_resolution,[],[f47])).
% 1.99/0.99  
% 1.99/0.99  fof(f55,plain,(
% 1.99/0.99    m2_orders_2(sK4,sK1,sK3)),
% 1.99/0.99    inference(cnf_transformation,[],[f36])).
% 1.99/0.99  
% 1.99/0.99  fof(f54,plain,(
% 1.99/0.99    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))),
% 1.99/0.99    inference(cnf_transformation,[],[f36])).
% 1.99/0.99  
% 1.99/0.99  fof(f56,plain,(
% 1.99/0.99    k1_funct_1(sK3,u1_struct_0(sK1)) = sK2),
% 1.99/0.99    inference(cnf_transformation,[],[f36])).
% 1.99/0.99  
% 1.99/0.99  fof(f53,plain,(
% 1.99/0.99    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.99/0.99    inference(cnf_transformation,[],[f36])).
% 1.99/0.99  
% 1.99/0.99  fof(f57,plain,(
% 1.99/0.99    k1_xboole_0 != k3_orders_2(sK1,sK4,sK2)),
% 1.99/0.99    inference(cnf_transformation,[],[f36])).
% 1.99/0.99  
% 1.99/0.99  fof(f3,axiom,(
% 1.99/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f10,plain,(
% 1.99/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.99/0.99    inference(pure_predicate_removal,[],[f3])).
% 1.99/0.99  
% 1.99/0.99  fof(f15,plain,(
% 1.99/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f10])).
% 1.99/0.99  
% 1.99/0.99  fof(f16,plain,(
% 1.99/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.99/0.99    inference(flattening,[],[f15])).
% 1.99/0.99  
% 1.99/0.99  fof(f40,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f16])).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.99/0.99      | m1_subset_1(sK0(X1,X0),X1)
% 1.99/0.99      | k1_xboole_0 = X0 ),
% 1.99/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_547,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X0_52))
% 1.99/0.99      | m1_subset_1(sK0(X0_52,X0_51),X0_52)
% 1.99/0.99      | k1_xboole_0 = X0_51 ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_705,plain,
% 1.99/0.99      ( k1_xboole_0 = X0_51
% 1.99/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(X0_52)) != iProver_top
% 1.99/0.99      | m1_subset_1(sK0(X0_52,X0_51),X0_52) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_0,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.99/0.99      | r2_hidden(sK0(X1,X0),X0)
% 1.99/0.99      | k1_xboole_0 = X0 ),
% 1.99/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_548,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X0_52))
% 1.99/0.99      | r2_hidden(sK0(X0_52,X0_51),X0_51)
% 1.99/0.99      | k1_xboole_0 = X0_51 ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_704,plain,
% 1.99/0.99      ( k1_xboole_0 = X0_51
% 1.99/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(X0_52)) != iProver_top
% 1.99/0.99      | r2_hidden(sK0(X0_52,X0_51),X0_51) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_548]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_8,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.99/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.99/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/0.99      | r2_hidden(X2,X3)
% 1.99/0.99      | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
% 1.99/0.99      | v2_struct_0(X1)
% 1.99/0.99      | ~ v3_orders_2(X1)
% 1.99/0.99      | ~ v4_orders_2(X1)
% 1.99/0.99      | ~ v5_orders_2(X1)
% 1.99/0.99      | ~ l1_orders_2(X1) ),
% 1.99/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_16,negated_conjecture,
% 1.99/0.99      ( l1_orders_2(sK1) ),
% 1.99/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_416,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.99/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.99/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/0.99      | r2_hidden(X2,X3)
% 1.99/0.99      | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
% 1.99/0.99      | v2_struct_0(X1)
% 1.99/0.99      | ~ v3_orders_2(X1)
% 1.99/0.99      | ~ v4_orders_2(X1)
% 1.99/0.99      | ~ v5_orders_2(X1)
% 1.99/0.99      | sK1 != X1 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_417,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/0.99      | r2_hidden(X0,X2)
% 1.99/0.99      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 1.99/0.99      | v2_struct_0(sK1)
% 1.99/0.99      | ~ v3_orders_2(sK1)
% 1.99/0.99      | ~ v4_orders_2(sK1)
% 1.99/0.99      | ~ v5_orders_2(sK1) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_416]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_20,negated_conjecture,
% 1.99/0.99      ( ~ v2_struct_0(sK1) ),
% 1.99/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_19,negated_conjecture,
% 1.99/0.99      ( v3_orders_2(sK1) ),
% 1.99/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_18,negated_conjecture,
% 1.99/0.99      ( v4_orders_2(sK1) ),
% 1.99/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_17,negated_conjecture,
% 1.99/0.99      ( v5_orders_2(sK1) ),
% 1.99/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_421,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/0.99      | r2_hidden(X0,X2)
% 1.99/0.99      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1)) ),
% 1.99/0.99      inference(global_propositional_subsumption,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_417,c_20,c_19,c_18,c_17]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_540,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0_51,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(X1_51,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(X2_51,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/0.99      | r2_hidden(X0_51,X2_51)
% 1.99/0.99      | ~ r2_hidden(X0_51,k3_orders_2(sK1,X2_51,X1_51)) ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_421]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_710,plain,
% 1.99/0.99      ( m1_subset_1(X0_51,u1_struct_0(sK1)) != iProver_top
% 1.99/0.99      | m1_subset_1(X1_51,u1_struct_0(sK1)) != iProver_top
% 1.99/0.99      | m1_subset_1(X2_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/0.99      | r2_hidden(X0_51,X2_51) = iProver_top
% 1.99/0.99      | r2_hidden(X0_51,k3_orders_2(sK1,X2_51,X1_51)) != iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1098,plain,
% 1.99/0.99      ( k3_orders_2(sK1,X0_51,X1_51) = k1_xboole_0
% 1.99/0.99      | m1_subset_1(X1_51,u1_struct_0(sK1)) != iProver_top
% 1.99/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/0.99      | m1_subset_1(k3_orders_2(sK1,X0_51,X1_51),k1_zfmisc_1(X0_52)) != iProver_top
% 1.99/0.99      | m1_subset_1(sK0(X0_52,k3_orders_2(sK1,X0_51,X1_51)),u1_struct_0(sK1)) != iProver_top
% 1.99/0.99      | r2_hidden(sK0(X0_52,k3_orders_2(sK1,X0_51,X1_51)),X0_51) = iProver_top ),
% 1.99/0.99      inference(superposition,[status(thm)],[c_704,c_710]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1260,plain,
% 1.99/0.99      ( k3_orders_2(sK1,X0_51,X1_51) = k1_xboole_0
% 1.99/0.99      | m1_subset_1(X1_51,u1_struct_0(sK1)) != iProver_top
% 1.99/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/0.99      | m1_subset_1(k3_orders_2(sK1,X0_51,X1_51),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/0.99      | r2_hidden(sK0(u1_struct_0(sK1),k3_orders_2(sK1,X0_51,X1_51)),X0_51) = iProver_top ),
% 1.99/0.99      inference(superposition,[status(thm)],[c_705,c_1098]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_2,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.99/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/0.99      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/0.99      | v2_struct_0(X1)
% 1.99/0.99      | ~ v3_orders_2(X1)
% 1.99/0.99      | ~ v4_orders_2(X1)
% 1.99/0.99      | ~ v5_orders_2(X1)
% 1.99/0.99      | ~ l1_orders_2(X1) ),
% 1.99/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_443,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.99/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/0.99      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/0.99      | v2_struct_0(X1)
% 1.99/0.99      | ~ v3_orders_2(X1)
% 1.99/0.99      | ~ v4_orders_2(X1)
% 1.99/0.99      | ~ v5_orders_2(X1)
% 1.99/0.99      | sK1 != X1 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_16]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_444,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/0.99      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/0.99      | v2_struct_0(sK1)
% 1.99/0.99      | ~ v3_orders_2(sK1)
% 1.99/0.99      | ~ v4_orders_2(sK1)
% 1.99/0.99      | ~ v5_orders_2(sK1) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_443]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_448,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/0.99      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.99/0.99      inference(global_propositional_subsumption,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_444,c_20,c_19,c_18,c_17]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_539,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0_51,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/0.99      | m1_subset_1(k3_orders_2(sK1,X1_51,X0_51),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_448]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_711,plain,
% 1.99/0.99      ( m1_subset_1(X0_51,u1_struct_0(sK1)) != iProver_top
% 1.99/0.99      | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/0.99      | m1_subset_1(k3_orders_2(sK1,X1_51,X0_51),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1337,plain,
% 1.99/0.99      ( k3_orders_2(sK1,X0_51,X1_51) = k1_xboole_0
% 1.99/0.99      | m1_subset_1(X1_51,u1_struct_0(sK1)) != iProver_top
% 1.99/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/0.99      | r2_hidden(sK0(u1_struct_0(sK1),k3_orders_2(sK1,X0_51,X1_51)),X0_51) = iProver_top ),
% 1.99/0.99      inference(forward_subsumption_resolution,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_1260,c_711]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_9,plain,
% 1.99/0.99      ( r2_orders_2(X0,X1,X2)
% 1.99/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.99/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.99/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 1.99/0.99      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 1.99/0.99      | v2_struct_0(X0)
% 1.99/0.99      | ~ v3_orders_2(X0)
% 1.99/0.99      | ~ v4_orders_2(X0)
% 1.99/0.99      | ~ v5_orders_2(X0)
% 1.99/0.99      | ~ l1_orders_2(X0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_6,plain,
% 1.99/0.99      ( ~ r2_orders_2(X0,X1,X2)
% 1.99/0.99      | ~ r1_orders_2(X0,X2,X1)
% 1.99/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.99/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.99/0.99      | ~ v5_orders_2(X0)
% 1.99/0.99      | ~ l1_orders_2(X0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_5,plain,
% 1.99/0.99      ( r1_orders_2(X0,X1,X2)
% 1.99/0.99      | ~ r3_orders_2(X0,X1,X2)
% 1.99/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.99/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.99/0.99      | v2_struct_0(X0)
% 1.99/0.99      | ~ v3_orders_2(X0)
% 1.99/0.99      | ~ l1_orders_2(X0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_10,plain,
% 1.99/0.99      ( r3_orders_2(X0,k1_funct_1(X1,u1_struct_0(X0)),X2)
% 1.99/0.99      | ~ m2_orders_2(X3,X0,X1)
% 1.99/0.99      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.99/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(X0)),u1_struct_0(X0))
% 1.99/0.99      | ~ r2_hidden(X2,X3)
% 1.99/0.99      | v2_struct_0(X0)
% 1.99/0.99      | ~ v3_orders_2(X0)
% 1.99/0.99      | ~ v4_orders_2(X0)
% 1.99/0.99      | ~ v5_orders_2(X0)
% 1.99/0.99      | ~ l1_orders_2(X0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_13,negated_conjecture,
% 1.99/0.99      ( m2_orders_2(sK4,sK1,sK3) ),
% 1.99/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_224,plain,
% 1.99/0.99      ( r3_orders_2(X0,k1_funct_1(X1,u1_struct_0(X0)),X2)
% 1.99/0.99      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.99/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(X0)),u1_struct_0(X0))
% 1.99/0.99      | ~ r2_hidden(X2,X3)
% 1.99/0.99      | v2_struct_0(X0)
% 1.99/0.99      | ~ v3_orders_2(X0)
% 1.99/0.99      | ~ v4_orders_2(X0)
% 1.99/0.99      | ~ v5_orders_2(X0)
% 1.99/0.99      | ~ l1_orders_2(X0)
% 1.99/0.99      | sK3 != X1
% 1.99/0.99      | sK4 != X3
% 1.99/0.99      | sK1 != X0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_13]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_225,plain,
% 1.99/0.99      ( r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
% 1.99/0.99      | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
% 1.99/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 1.99/0.99      | ~ r2_hidden(X0,sK4)
% 1.99/0.99      | v2_struct_0(sK1)
% 1.99/0.99      | ~ v3_orders_2(sK1)
% 1.99/0.99      | ~ v4_orders_2(sK1)
% 1.99/0.99      | ~ v5_orders_2(sK1)
% 1.99/0.99      | ~ l1_orders_2(sK1) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_224]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_14,negated_conjecture,
% 1.99/0.99      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) ),
% 1.99/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_229,plain,
% 1.99/0.99      ( ~ r2_hidden(X0,sK4)
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.99/0.99      | r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0) ),
% 1.99/0.99      inference(global_propositional_subsumption,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_225,c_20,c_19,c_18,c_17,c_16,c_14]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_230,plain,
% 1.99/0.99      ( r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
% 1.99/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 1.99/0.99      | ~ r2_hidden(X0,sK4) ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_229]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_256,plain,
% 1.99/0.99      ( r1_orders_2(X0,X1,X2)
% 1.99/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.99/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.99/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 1.99/0.99      | ~ r2_hidden(X3,sK4)
% 1.99/0.99      | v2_struct_0(X0)
% 1.99/0.99      | ~ v3_orders_2(X0)
% 1.99/0.99      | ~ l1_orders_2(X0)
% 1.99/0.99      | X3 != X2
% 1.99/0.99      | k1_funct_1(sK3,u1_struct_0(sK1)) != X1
% 1.99/0.99      | sK1 != X0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_230]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_257,plain,
% 1.99/0.99      ( r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
% 1.99/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 1.99/0.99      | ~ r2_hidden(X0,sK4)
% 1.99/0.99      | v2_struct_0(sK1)
% 1.99/0.99      | ~ v3_orders_2(sK1)
% 1.99/0.99      | ~ l1_orders_2(sK1) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_256]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_261,plain,
% 1.99/0.99      ( ~ r2_hidden(X0,sK4)
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.99/0.99      | r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0) ),
% 1.99/0.99      inference(global_propositional_subsumption,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_257,c_20,c_19,c_16]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_262,plain,
% 1.99/0.99      ( r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
% 1.99/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 1.99/0.99      | ~ r2_hidden(X0,sK4) ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_261]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_285,plain,
% 1.99/0.99      ( ~ r2_orders_2(X0,X1,X2)
% 1.99/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.99/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.99/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 1.99/0.99      | ~ r2_hidden(X3,sK4)
% 1.99/0.99      | ~ v5_orders_2(X0)
% 1.99/0.99      | ~ l1_orders_2(X0)
% 1.99/0.99      | X3 != X1
% 1.99/0.99      | k1_funct_1(sK3,u1_struct_0(sK1)) != X2
% 1.99/0.99      | sK1 != X0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_262]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_286,plain,
% 1.99/0.99      ( ~ r2_orders_2(sK1,X0,k1_funct_1(sK3,u1_struct_0(sK1)))
% 1.99/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 1.99/0.99      | ~ r2_hidden(X0,sK4)
% 1.99/0.99      | ~ v5_orders_2(sK1)
% 1.99/0.99      | ~ l1_orders_2(sK1) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_285]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_290,plain,
% 1.99/0.99      ( ~ r2_orders_2(sK1,X0,k1_funct_1(sK3,u1_struct_0(sK1)))
% 1.99/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 1.99/0.99      | ~ r2_hidden(X0,sK4) ),
% 1.99/0.99      inference(global_propositional_subsumption,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_286,c_17,c_16]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_353,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.99/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.99/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 1.99/0.99      | ~ r2_hidden(X2,k3_orders_2(X1,X4,X0))
% 1.99/0.99      | ~ r2_hidden(X3,sK4)
% 1.99/0.99      | v2_struct_0(X1)
% 1.99/0.99      | ~ v3_orders_2(X1)
% 1.99/0.99      | ~ v4_orders_2(X1)
% 1.99/0.99      | ~ v5_orders_2(X1)
% 1.99/0.99      | ~ l1_orders_2(X1)
% 1.99/0.99      | X3 != X2
% 1.99/0.99      | k1_funct_1(sK3,u1_struct_0(sK1)) != X0
% 1.99/0.99      | sK1 != X1 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_290]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_354,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 1.99/0.99      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,k1_funct_1(sK3,u1_struct_0(sK1))))
% 1.99/0.99      | ~ r2_hidden(X0,sK4)
% 1.99/0.99      | v2_struct_0(sK1)
% 1.99/0.99      | ~ v3_orders_2(sK1)
% 1.99/0.99      | ~ v4_orders_2(sK1)
% 1.99/0.99      | ~ v5_orders_2(sK1)
% 1.99/0.99      | ~ l1_orders_2(sK1) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_353]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_358,plain,
% 1.99/0.99      ( ~ r2_hidden(X0,sK4)
% 1.99/0.99      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,k1_funct_1(sK3,u1_struct_0(sK1))))
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.99/0.99      inference(global_propositional_subsumption,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_354,c_20,c_19,c_18,c_17,c_16]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_359,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 1.99/0.99      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,k1_funct_1(sK3,u1_struct_0(sK1))))
% 1.99/0.99      | ~ r2_hidden(X0,sK4) ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_358]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_542,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0_51,u1_struct_0(sK1))
% 1.99/0.99      | ~ m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/0.99      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 1.99/0.99      | ~ r2_hidden(X0_51,k3_orders_2(sK1,X1_51,k1_funct_1(sK3,u1_struct_0(sK1))))
% 1.99/0.99      | ~ r2_hidden(X0_51,sK4) ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_359]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_708,plain,
% 1.99/0.99      ( m1_subset_1(X0_51,u1_struct_0(sK1)) != iProver_top
% 1.99/0.99      | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/0.99      | m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) != iProver_top
% 1.99/0.99      | r2_hidden(X0_51,k3_orders_2(sK1,X1_51,k1_funct_1(sK3,u1_struct_0(sK1)))) != iProver_top
% 1.99/0.99      | r2_hidden(X0_51,sK4) != iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_12,negated_conjecture,
% 1.99/0.99      ( k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 ),
% 1.99/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_545,negated_conjecture,
% 1.99/0.99      ( k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_748,plain,
% 1.99/0.99      ( m1_subset_1(X0_51,u1_struct_0(sK1)) != iProver_top
% 1.99/0.99      | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.99/0.99      | r2_hidden(X0_51,k3_orders_2(sK1,X1_51,sK2)) != iProver_top
% 1.99/0.99      | r2_hidden(X0_51,sK4) != iProver_top ),
% 1.99/0.99      inference(light_normalisation,[status(thm)],[c_708,c_545]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_15,negated_conjecture,
% 1.99/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.99/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_544,negated_conjecture,
% 1.99/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_706,plain,
% 1.99/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_754,plain,
% 1.99/0.99      ( m1_subset_1(X0_51,u1_struct_0(sK1)) != iProver_top
% 1.99/0.99      | m1_subset_1(X1_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/0.99      | r2_hidden(X0_51,k3_orders_2(sK1,X1_51,sK2)) != iProver_top
% 1.99/0.99      | r2_hidden(X0_51,sK4) != iProver_top ),
% 1.99/0.99      inference(forward_subsumption_resolution,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_748,c_706]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1099,plain,
% 1.99/0.99      ( k3_orders_2(sK1,X0_51,sK2) = k1_xboole_0
% 1.99/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/0.99      | m1_subset_1(k3_orders_2(sK1,X0_51,sK2),k1_zfmisc_1(X0_52)) != iProver_top
% 1.99/0.99      | m1_subset_1(sK0(X0_52,k3_orders_2(sK1,X0_51,sK2)),u1_struct_0(sK1)) != iProver_top
% 1.99/0.99      | r2_hidden(sK0(X0_52,k3_orders_2(sK1,X0_51,sK2)),sK4) != iProver_top ),
% 1.99/0.99      inference(superposition,[status(thm)],[c_704,c_754]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1207,plain,
% 1.99/0.99      ( k3_orders_2(sK1,X0_51,sK2) = k1_xboole_0
% 1.99/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/0.99      | m1_subset_1(k3_orders_2(sK1,X0_51,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/0.99      | r2_hidden(sK0(u1_struct_0(sK1),k3_orders_2(sK1,X0_51,sK2)),sK4) != iProver_top ),
% 1.99/0.99      inference(superposition,[status(thm)],[c_705,c_1099]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_26,plain,
% 1.99/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_793,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/0.99      | m1_subset_1(k3_orders_2(sK1,X0_51,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.99/0.99      inference(instantiation,[status(thm)],[c_539]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_794,plain,
% 1.99/0.99      ( m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/0.99      | m1_subset_1(k3_orders_2(sK1,X0_51,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.99/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_793]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1212,plain,
% 1.99/0.99      ( m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/0.99      | k3_orders_2(sK1,X0_51,sK2) = k1_xboole_0
% 1.99/0.99      | r2_hidden(sK0(u1_struct_0(sK1),k3_orders_2(sK1,X0_51,sK2)),sK4) != iProver_top ),
% 1.99/0.99      inference(global_propositional_subsumption,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_1207,c_26,c_794]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1213,plain,
% 1.99/0.99      ( k3_orders_2(sK1,X0_51,sK2) = k1_xboole_0
% 1.99/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.99/0.99      | r2_hidden(sK0(u1_struct_0(sK1),k3_orders_2(sK1,X0_51,sK2)),sK4) != iProver_top ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_1212]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1344,plain,
% 1.99/0.99      ( k3_orders_2(sK1,sK4,sK2) = k1_xboole_0
% 1.99/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.99/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.99/0.99      inference(superposition,[status(thm)],[c_1337,c_1213]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_551,plain,
% 1.99/0.99      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 1.99/0.99      theory(equality) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_818,plain,
% 1.99/0.99      ( k3_orders_2(sK1,sK4,sK2) != X0_51
% 1.99/0.99      | k1_xboole_0 != X0_51
% 1.99/0.99      | k1_xboole_0 = k3_orders_2(sK1,sK4,sK2) ),
% 1.99/0.99      inference(instantiation,[status(thm)],[c_551]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_819,plain,
% 1.99/0.99      ( k3_orders_2(sK1,sK4,sK2) != k1_xboole_0
% 1.99/0.99      | k1_xboole_0 = k3_orders_2(sK1,sK4,sK2)
% 1.99/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 1.99/0.99      inference(instantiation,[status(thm)],[c_818]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_11,negated_conjecture,
% 1.99/0.99      ( k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) ),
% 1.99/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_546,negated_conjecture,
% 1.99/0.99      ( k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) ),
% 1.99/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_550,plain,( X0_51 = X0_51 ),theory(equality) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_559,plain,
% 1.99/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 1.99/0.99      inference(instantiation,[status(thm)],[c_550]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_3,plain,
% 1.99/0.99      ( ~ m2_orders_2(X0,X1,X2)
% 1.99/0.99      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.99/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/0.99      | v2_struct_0(X1)
% 1.99/0.99      | ~ v3_orders_2(X1)
% 1.99/0.99      | ~ v4_orders_2(X1)
% 1.99/0.99      | ~ v5_orders_2(X1)
% 1.99/0.99      | ~ l1_orders_2(X1) ),
% 1.99/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_213,plain,
% 1.99/0.99      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
% 1.99/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/0.99      | v2_struct_0(X1)
% 1.99/0.99      | ~ v3_orders_2(X1)
% 1.99/0.99      | ~ v4_orders_2(X1)
% 1.99/0.99      | ~ v5_orders_2(X1)
% 1.99/0.99      | ~ l1_orders_2(X1)
% 1.99/0.99      | sK3 != X0
% 1.99/0.99      | sK4 != X2
% 1.99/0.99      | sK1 != X1 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_13]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_214,plain,
% 1.99/0.99      ( ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
% 1.99/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.99/0.99      | v2_struct_0(sK1)
% 1.99/0.99      | ~ v3_orders_2(sK1)
% 1.99/0.99      | ~ v4_orders_2(sK1)
% 1.99/0.99      | ~ v5_orders_2(sK1)
% 1.99/0.99      | ~ l1_orders_2(sK1) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_213]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_215,plain,
% 1.99/0.99      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) != iProver_top
% 1.99/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.99/0.99      | v2_struct_0(sK1) = iProver_top
% 1.99/0.99      | v3_orders_2(sK1) != iProver_top
% 1.99/0.99      | v4_orders_2(sK1) != iProver_top
% 1.99/0.99      | v5_orders_2(sK1) != iProver_top
% 1.99/0.99      | l1_orders_2(sK1) != iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_214]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_27,plain,
% 1.99/0.99      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_25,plain,
% 1.99/0.99      ( l1_orders_2(sK1) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_24,plain,
% 1.99/0.99      ( v5_orders_2(sK1) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_23,plain,
% 1.99/0.99      ( v4_orders_2(sK1) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_22,plain,
% 1.99/0.99      ( v3_orders_2(sK1) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_21,plain,
% 1.99/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(contradiction,plain,
% 1.99/0.99      ( $false ),
% 1.99/0.99      inference(minisat,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_1344,c_819,c_546,c_559,c_215,c_27,c_26,c_25,c_24,c_23,
% 1.99/0.99                 c_22,c_21]) ).
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.99/0.99  
% 1.99/0.99  ------                               Statistics
% 1.99/0.99  
% 1.99/0.99  ------ General
% 1.99/0.99  
% 1.99/0.99  abstr_ref_over_cycles:                  0
% 1.99/0.99  abstr_ref_under_cycles:                 0
% 1.99/0.99  gc_basic_clause_elim:                   0
% 1.99/0.99  forced_gc_time:                         0
% 1.99/0.99  parsing_time:                           0.009
% 1.99/0.99  unif_index_cands_time:                  0.
% 1.99/0.99  unif_index_add_time:                    0.
% 1.99/0.99  orderings_time:                         0.
% 1.99/0.99  out_proof_time:                         0.022
% 1.99/0.99  total_time:                             0.092
% 1.99/0.99  num_of_symbols:                         55
% 1.99/0.99  num_of_terms:                           1676
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing
% 1.99/0.99  
% 1.99/0.99  num_of_splits:                          0
% 1.99/0.99  num_of_split_atoms:                     0
% 1.99/0.99  num_of_reused_defs:                     0
% 1.99/0.99  num_eq_ax_congr_red:                    20
% 1.99/0.99  num_of_sem_filtered_clauses:            1
% 1.99/0.99  num_of_subtypes:                        4
% 1.99/0.99  monotx_restored_types:                  0
% 1.99/0.99  sat_num_of_epr_types:                   0
% 1.99/0.99  sat_num_of_non_cyclic_types:            0
% 1.99/0.99  sat_guarded_non_collapsed_types:        1
% 1.99/0.99  num_pure_diseq_elim:                    0
% 1.99/0.99  simp_replaced_by:                       0
% 1.99/0.99  res_preprocessed:                       62
% 1.99/0.99  prep_upred:                             0
% 1.99/0.99  prep_unflattend:                        18
% 1.99/0.99  smt_new_axioms:                         0
% 1.99/0.99  pred_elim_cands:                        2
% 1.99/0.99  pred_elim:                              10
% 1.99/0.99  pred_elim_cl:                           11
% 1.99/0.99  pred_elim_cycles:                       12
% 1.99/0.99  merged_defs:                            0
% 1.99/0.99  merged_defs_ncl:                        0
% 1.99/0.99  bin_hyper_res:                          0
% 1.99/0.99  prep_cycles:                            4
% 1.99/0.99  pred_elim_time:                         0.007
% 1.99/0.99  splitting_time:                         0.
% 1.99/0.99  sem_filter_time:                        0.
% 1.99/0.99  monotx_time:                            0.
% 1.99/0.99  subtype_inf_time:                       0.
% 1.99/0.99  
% 1.99/0.99  ------ Problem properties
% 1.99/0.99  
% 1.99/0.99  clauses:                                10
% 1.99/0.99  conjectures:                            3
% 1.99/0.99  epr:                                    0
% 1.99/0.99  horn:                                   8
% 1.99/0.99  ground:                                 4
% 1.99/0.99  unary:                                  4
% 1.99/0.99  binary:                                 0
% 1.99/0.99  lits:                                   30
% 1.99/0.99  lits_eq:                                4
% 1.99/0.99  fd_pure:                                0
% 1.99/0.99  fd_pseudo:                              0
% 1.99/0.99  fd_cond:                                2
% 1.99/0.99  fd_pseudo_cond:                         0
% 1.99/0.99  ac_symbols:                             0
% 1.99/0.99  
% 1.99/0.99  ------ Propositional Solver
% 1.99/0.99  
% 1.99/0.99  prop_solver_calls:                      26
% 1.99/0.99  prop_fast_solver_calls:                 602
% 1.99/0.99  smt_solver_calls:                       0
% 1.99/0.99  smt_fast_solver_calls:                  0
% 1.99/0.99  prop_num_of_clauses:                    432
% 1.99/0.99  prop_preprocess_simplified:             1806
% 1.99/0.99  prop_fo_subsumed:                       35
% 1.99/0.99  prop_solver_time:                       0.
% 1.99/0.99  smt_solver_time:                        0.
% 1.99/0.99  smt_fast_solver_time:                   0.
% 1.99/0.99  prop_fast_solver_time:                  0.
% 1.99/0.99  prop_unsat_core_time:                   0.
% 1.99/0.99  
% 1.99/0.99  ------ QBF
% 1.99/0.99  
% 1.99/0.99  qbf_q_res:                              0
% 1.99/0.99  qbf_num_tautologies:                    0
% 1.99/0.99  qbf_prep_cycles:                        0
% 1.99/0.99  
% 1.99/0.99  ------ BMC1
% 1.99/0.99  
% 1.99/0.99  bmc1_current_bound:                     -1
% 1.99/0.99  bmc1_last_solved_bound:                 -1
% 1.99/0.99  bmc1_unsat_core_size:                   -1
% 1.99/0.99  bmc1_unsat_core_parents_size:           -1
% 1.99/0.99  bmc1_merge_next_fun:                    0
% 1.99/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.99/0.99  
% 1.99/0.99  ------ Instantiation
% 1.99/0.99  
% 1.99/0.99  inst_num_of_clauses:                    109
% 1.99/0.99  inst_num_in_passive:                    28
% 1.99/0.99  inst_num_in_active:                     73
% 1.99/0.99  inst_num_in_unprocessed:                8
% 1.99/0.99  inst_num_of_loops:                      80
% 1.99/0.99  inst_num_of_learning_restarts:          0
% 1.99/0.99  inst_num_moves_active_passive:          4
% 1.99/0.99  inst_lit_activity:                      0
% 1.99/0.99  inst_lit_activity_moves:                0
% 1.99/0.99  inst_num_tautologies:                   0
% 1.99/0.99  inst_num_prop_implied:                  0
% 1.99/0.99  inst_num_existing_simplified:           0
% 1.99/0.99  inst_num_eq_res_simplified:             0
% 1.99/0.99  inst_num_child_elim:                    0
% 1.99/0.99  inst_num_of_dismatching_blockings:      7
% 1.99/0.99  inst_num_of_non_proper_insts:           88
% 1.99/0.99  inst_num_of_duplicates:                 0
% 1.99/0.99  inst_inst_num_from_inst_to_res:         0
% 1.99/0.99  inst_dismatching_checking_time:         0.
% 1.99/0.99  
% 1.99/0.99  ------ Resolution
% 1.99/0.99  
% 1.99/0.99  res_num_of_clauses:                     0
% 1.99/0.99  res_num_in_passive:                     0
% 1.99/0.99  res_num_in_active:                      0
% 1.99/0.99  res_num_of_loops:                       66
% 1.99/0.99  res_forward_subset_subsumed:            13
% 1.99/0.99  res_backward_subset_subsumed:           0
% 1.99/0.99  res_forward_subsumed:                   0
% 1.99/0.99  res_backward_subsumed:                  0
% 1.99/0.99  res_forward_subsumption_resolution:     0
% 1.99/0.99  res_backward_subsumption_resolution:    0
% 1.99/0.99  res_clause_to_clause_subsumption:       140
% 1.99/0.99  res_orphan_elimination:                 0
% 1.99/0.99  res_tautology_del:                      11
% 1.99/0.99  res_num_eq_res_simplified:              0
% 1.99/0.99  res_num_sel_changes:                    0
% 1.99/0.99  res_moves_from_active_to_pass:          0
% 1.99/0.99  
% 1.99/0.99  ------ Superposition
% 1.99/0.99  
% 1.99/0.99  sup_time_total:                         0.
% 1.99/0.99  sup_time_generating:                    0.
% 1.99/0.99  sup_time_sim_full:                      0.
% 1.99/0.99  sup_time_sim_immed:                     0.
% 1.99/0.99  
% 1.99/0.99  sup_num_of_clauses:                     19
% 1.99/0.99  sup_num_in_active:                      15
% 1.99/0.99  sup_num_in_passive:                     4
% 1.99/0.99  sup_num_of_loops:                       14
% 1.99/0.99  sup_fw_superposition:                   2
% 1.99/0.99  sup_bw_superposition:                   10
% 1.99/0.99  sup_immediate_simplified:               2
% 1.99/0.99  sup_given_eliminated:                   0
% 1.99/0.99  comparisons_done:                       0
% 1.99/0.99  comparisons_avoided:                    0
% 1.99/0.99  
% 1.99/0.99  ------ Simplifications
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  sim_fw_subset_subsumed:                 0
% 1.99/0.99  sim_bw_subset_subsumed:                 0
% 1.99/0.99  sim_fw_subsumed:                        2
% 1.99/0.99  sim_bw_subsumed:                        0
% 1.99/0.99  sim_fw_subsumption_res:                 2
% 1.99/0.99  sim_bw_subsumption_res:                 0
% 1.99/0.99  sim_tautology_del:                      1
% 1.99/0.99  sim_eq_tautology_del:                   0
% 1.99/0.99  sim_eq_res_simp:                        0
% 1.99/0.99  sim_fw_demodulated:                     0
% 1.99/0.99  sim_bw_demodulated:                     0
% 1.99/0.99  sim_light_normalised:                   1
% 1.99/0.99  sim_joinable_taut:                      0
% 1.99/0.99  sim_joinable_simp:                      0
% 1.99/0.99  sim_ac_normalised:                      0
% 1.99/0.99  sim_smt_subsumption:                    0
% 1.99/0.99  
%------------------------------------------------------------------------------
