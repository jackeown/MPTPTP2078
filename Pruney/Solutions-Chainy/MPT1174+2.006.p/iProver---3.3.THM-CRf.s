%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:44 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 849 expanded)
%              Number of clauses        :   91 ( 166 expanded)
%              Number of leaves         :   15 ( 320 expanded)
%              Depth                    :   30
%              Number of atoms          :  880 (6925 expanded)
%              Number of equality atoms :  189 (1768 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f31])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

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
    inference(cnf_transformation,[],[f37])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
          & k1_funct_1(X2,u1_struct_0(X0)) = X1
          & m2_orders_2(X3,X0,X2) )
     => ( k1_xboole_0 != k3_orders_2(X0,sK4,X1)
        & k1_funct_1(X2,u1_struct_0(X0)) = X1
        & m2_orders_2(sK4,X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f41,f40,f39,f38])).

fof(f61,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f17,plain,(
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
    inference(flattening,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
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
    inference(equality_resolution,[],[f59])).

fof(f67,plain,(
    m2_orders_2(sK4,sK1,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X0,X1,X3)
      | ~ r2_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
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

fof(f12,plain,(
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
    inference(pure_predicate_removal,[],[f5])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
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

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f69,plain,(
    k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1107,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_25,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_424,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_425,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_429,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_425,c_26,c_24,c_23,c_22])).

cnf(c_430,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_429])).

cnf(c_1101,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_431,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_25])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_404,c_26,c_24,c_23,c_22])).

cnf(c_1102,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1110,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1681,plain,
    ( r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1102,c_1110])).

cnf(c_1900,plain,
    ( r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1101,c_431,c_1681])).

cnf(c_1901,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1900])).

cnf(c_1908,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1107,c_1901])).

cnf(c_15,plain,
    ( r2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_346,plain,
    ( r2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_347,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_351,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_26,c_24,c_23,c_22])).

cnf(c_352,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_351])).

cnf(c_1104,plain,
    ( r2_orders_2(sK1,X0,X1) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK1,X2,X1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_1918,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | r2_orders_2(sK1,sK0(k3_orders_2(sK1,X0,X1)),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1107,c_1104])).

cnf(c_2124,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1107,c_1681])).

cnf(c_2497,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_orders_2(sK1,sK0(k3_orders_2(sK1,X0,X1)),X1) = iProver_top
    | k3_orders_2(sK1,X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1918,c_2124])).

cnf(c_2498,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | r2_orders_2(sK1,sK0(k3_orders_2(sK1,X0,X1)),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2497])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1106,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_10,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_16,plain,
    ( r3_orders_2(X0,k1_funct_1(X1,u1_struct_0(X0)),X2)
    | ~ m2_orders_2(X3,X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(X0)),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_19,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_285,plain,
    ( r3_orders_2(X0,k1_funct_1(X1,u1_struct_0(X0)),X2)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(X0)),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X1
    | sK4 != X3
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_286,plain,
    ( r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
    | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_20,negated_conjecture,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_290,plain,
    ( ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK4)
    | r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_286,c_26,c_25,c_24,c_23,c_22,c_20])).

cnf(c_291,plain,
    ( r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_290])).

cnf(c_317,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X3,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X3 != X2
    | k1_funct_1(sK3,u1_struct_0(sK1)) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_291])).

cnf(c_318,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_322,plain,
    ( ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK4)
    | r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_318,c_26,c_25,c_22])).

cnf(c_323,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_322])).

cnf(c_11,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X2,X3)
    | r2_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_499,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X2,X3)
    | r2_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_500,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X1,X2)
    | r2_orders_2(sK1,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v4_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_502,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X1,X2)
    | r2_orders_2(sK1,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_500,c_24,c_22])).

cnf(c_503,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X1,X2)
    | r2_orders_2(sK1,X0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_502])).

cnf(c_649,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | r2_orders_2(sK1,X2,X1)
    | ~ r2_hidden(X3,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | X0 != X3
    | k1_funct_1(sK3,u1_struct_0(sK1)) != X2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_323,c_503])).

cnf(c_650,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | r2_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X1)
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_649])).

cnf(c_1097,plain,
    ( r2_orders_2(sK1,X0,X1) != iProver_top
    | r2_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X1) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_650])).

cnf(c_18,negated_conjecture,
    ( k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1218,plain,
    ( r2_orders_2(sK1,X0,X1) != iProver_top
    | r2_orders_2(sK1,sK2,X1) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1097,c_18])).

cnf(c_1225,plain,
    ( r2_orders_2(sK1,X0,X1) != iProver_top
    | r2_orders_2(sK1,sK2,X1) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1218,c_1106])).

cnf(c_8,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_274,plain,
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
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_275,plain,
    ( ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_277,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_275,c_26,c_25,c_24,c_23,c_22,c_20])).

cnf(c_1105,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_1680,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_1110])).

cnf(c_1699,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_orders_2(sK1,sK2,X1) = iProver_top
    | r2_orders_2(sK1,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1225,c_1680])).

cnf(c_1700,plain,
    ( r2_orders_2(sK1,X0,X1) != iProver_top
    | r2_orders_2(sK1,sK2,X1) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1699])).

cnf(c_1707,plain,
    ( r2_orders_2(sK1,X0,sK2) != iProver_top
    | r2_orders_2(sK1,sK2,sK2) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1106,c_1700])).

cnf(c_32,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_557,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_22])).

cnf(c_558,plain,
    ( ~ r2_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_1268,plain,
    ( ~ r2_orders_2(sK1,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_558])).

cnf(c_1269,plain,
    ( r2_orders_2(sK1,sK2,sK2) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1268])).

cnf(c_1784,plain,
    ( r2_orders_2(sK1,X0,sK2) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1707,c_32,c_1269])).

cnf(c_2507,plain,
    ( k3_orders_2(sK1,X0,sK2) = k1_xboole_0
    | r2_hidden(sK0(k3_orders_2(sK1,X0,sK2)),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2498,c_1784])).

cnf(c_2581,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X0,sK2)),sK4) != iProver_top
    | k3_orders_2(sK1,X0,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2507,c_32])).

cnf(c_2582,plain,
    ( k3_orders_2(sK1,X0,sK2) = k1_xboole_0
    | r2_hidden(sK0(k3_orders_2(sK1,X0,sK2)),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2581])).

cnf(c_2590,plain,
    ( k3_orders_2(sK1,sK4,sK2) = k1_xboole_0
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1908,c_2582])).

cnf(c_27,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,plain,
    ( v3_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_29,plain,
    ( v4_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_30,plain,
    ( v5_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_31,plain,
    ( l1_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_33,plain,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_276,plain,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v3_orders_2(sK1) != iProver_top
    | v4_orders_2(sK1) != iProver_top
    | v5_orders_2(sK1) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_275])).

cnf(c_3349,plain,
    ( k3_orders_2(sK1,sK4,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2590,c_27,c_28,c_29,c_30,c_31,c_32,c_33,c_276])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3352,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3349,c_17])).

cnf(c_3424,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3352])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.19/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.03  
% 2.19/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.19/1.03  
% 2.19/1.03  ------  iProver source info
% 2.19/1.03  
% 2.19/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.19/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.19/1.03  git: non_committed_changes: false
% 2.19/1.03  git: last_make_outside_of_git: false
% 2.19/1.03  
% 2.19/1.03  ------ 
% 2.19/1.03  
% 2.19/1.03  ------ Input Options
% 2.19/1.03  
% 2.19/1.03  --out_options                           all
% 2.19/1.03  --tptp_safe_out                         true
% 2.19/1.03  --problem_path                          ""
% 2.19/1.03  --include_path                          ""
% 2.19/1.03  --clausifier                            res/vclausify_rel
% 2.19/1.03  --clausifier_options                    --mode clausify
% 2.19/1.03  --stdin                                 false
% 2.19/1.03  --stats_out                             all
% 2.19/1.03  
% 2.19/1.03  ------ General Options
% 2.19/1.03  
% 2.19/1.03  --fof                                   false
% 2.19/1.03  --time_out_real                         305.
% 2.19/1.03  --time_out_virtual                      -1.
% 2.19/1.03  --symbol_type_check                     false
% 2.19/1.03  --clausify_out                          false
% 2.19/1.03  --sig_cnt_out                           false
% 2.19/1.03  --trig_cnt_out                          false
% 2.19/1.03  --trig_cnt_out_tolerance                1.
% 2.19/1.03  --trig_cnt_out_sk_spl                   false
% 2.19/1.03  --abstr_cl_out                          false
% 2.19/1.03  
% 2.19/1.03  ------ Global Options
% 2.19/1.03  
% 2.19/1.03  --schedule                              default
% 2.19/1.03  --add_important_lit                     false
% 2.19/1.03  --prop_solver_per_cl                    1000
% 2.19/1.03  --min_unsat_core                        false
% 2.19/1.03  --soft_assumptions                      false
% 2.19/1.03  --soft_lemma_size                       3
% 2.19/1.03  --prop_impl_unit_size                   0
% 2.19/1.03  --prop_impl_unit                        []
% 2.19/1.03  --share_sel_clauses                     true
% 2.19/1.03  --reset_solvers                         false
% 2.19/1.03  --bc_imp_inh                            [conj_cone]
% 2.19/1.03  --conj_cone_tolerance                   3.
% 2.19/1.03  --extra_neg_conj                        none
% 2.19/1.03  --large_theory_mode                     true
% 2.19/1.03  --prolific_symb_bound                   200
% 2.19/1.03  --lt_threshold                          2000
% 2.19/1.03  --clause_weak_htbl                      true
% 2.19/1.03  --gc_record_bc_elim                     false
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing Options
% 2.19/1.03  
% 2.19/1.03  --preprocessing_flag                    true
% 2.19/1.03  --time_out_prep_mult                    0.1
% 2.19/1.03  --splitting_mode                        input
% 2.19/1.03  --splitting_grd                         true
% 2.19/1.03  --splitting_cvd                         false
% 2.19/1.03  --splitting_cvd_svl                     false
% 2.19/1.03  --splitting_nvd                         32
% 2.19/1.03  --sub_typing                            true
% 2.19/1.03  --prep_gs_sim                           true
% 2.19/1.03  --prep_unflatten                        true
% 2.19/1.03  --prep_res_sim                          true
% 2.19/1.03  --prep_upred                            true
% 2.19/1.03  --prep_sem_filter                       exhaustive
% 2.19/1.03  --prep_sem_filter_out                   false
% 2.19/1.03  --pred_elim                             true
% 2.19/1.03  --res_sim_input                         true
% 2.19/1.03  --eq_ax_congr_red                       true
% 2.19/1.03  --pure_diseq_elim                       true
% 2.19/1.03  --brand_transform                       false
% 2.19/1.03  --non_eq_to_eq                          false
% 2.19/1.03  --prep_def_merge                        true
% 2.19/1.03  --prep_def_merge_prop_impl              false
% 2.19/1.03  --prep_def_merge_mbd                    true
% 2.19/1.03  --prep_def_merge_tr_red                 false
% 2.19/1.03  --prep_def_merge_tr_cl                  false
% 2.19/1.03  --smt_preprocessing                     true
% 2.19/1.03  --smt_ac_axioms                         fast
% 2.19/1.03  --preprocessed_out                      false
% 2.19/1.03  --preprocessed_stats                    false
% 2.19/1.03  
% 2.19/1.03  ------ Abstraction refinement Options
% 2.19/1.03  
% 2.19/1.03  --abstr_ref                             []
% 2.19/1.03  --abstr_ref_prep                        false
% 2.19/1.03  --abstr_ref_until_sat                   false
% 2.19/1.03  --abstr_ref_sig_restrict                funpre
% 2.19/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/1.03  --abstr_ref_under                       []
% 2.19/1.03  
% 2.19/1.03  ------ SAT Options
% 2.19/1.03  
% 2.19/1.03  --sat_mode                              false
% 2.19/1.03  --sat_fm_restart_options                ""
% 2.19/1.03  --sat_gr_def                            false
% 2.19/1.03  --sat_epr_types                         true
% 2.19/1.03  --sat_non_cyclic_types                  false
% 2.19/1.03  --sat_finite_models                     false
% 2.19/1.03  --sat_fm_lemmas                         false
% 2.19/1.03  --sat_fm_prep                           false
% 2.19/1.03  --sat_fm_uc_incr                        true
% 2.19/1.03  --sat_out_model                         small
% 2.19/1.03  --sat_out_clauses                       false
% 2.19/1.03  
% 2.19/1.03  ------ QBF Options
% 2.19/1.03  
% 2.19/1.03  --qbf_mode                              false
% 2.19/1.03  --qbf_elim_univ                         false
% 2.19/1.03  --qbf_dom_inst                          none
% 2.19/1.03  --qbf_dom_pre_inst                      false
% 2.19/1.03  --qbf_sk_in                             false
% 2.19/1.03  --qbf_pred_elim                         true
% 2.19/1.03  --qbf_split                             512
% 2.19/1.03  
% 2.19/1.03  ------ BMC1 Options
% 2.19/1.03  
% 2.19/1.03  --bmc1_incremental                      false
% 2.19/1.03  --bmc1_axioms                           reachable_all
% 2.19/1.03  --bmc1_min_bound                        0
% 2.19/1.03  --bmc1_max_bound                        -1
% 2.19/1.03  --bmc1_max_bound_default                -1
% 2.19/1.03  --bmc1_symbol_reachability              true
% 2.19/1.03  --bmc1_property_lemmas                  false
% 2.19/1.03  --bmc1_k_induction                      false
% 2.19/1.03  --bmc1_non_equiv_states                 false
% 2.19/1.03  --bmc1_deadlock                         false
% 2.19/1.03  --bmc1_ucm                              false
% 2.19/1.03  --bmc1_add_unsat_core                   none
% 2.19/1.03  --bmc1_unsat_core_children              false
% 2.19/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/1.03  --bmc1_out_stat                         full
% 2.19/1.03  --bmc1_ground_init                      false
% 2.19/1.03  --bmc1_pre_inst_next_state              false
% 2.19/1.03  --bmc1_pre_inst_state                   false
% 2.19/1.03  --bmc1_pre_inst_reach_state             false
% 2.19/1.03  --bmc1_out_unsat_core                   false
% 2.19/1.03  --bmc1_aig_witness_out                  false
% 2.19/1.03  --bmc1_verbose                          false
% 2.19/1.03  --bmc1_dump_clauses_tptp                false
% 2.19/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.19/1.03  --bmc1_dump_file                        -
% 2.19/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.19/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.19/1.03  --bmc1_ucm_extend_mode                  1
% 2.19/1.03  --bmc1_ucm_init_mode                    2
% 2.19/1.03  --bmc1_ucm_cone_mode                    none
% 2.19/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.19/1.03  --bmc1_ucm_relax_model                  4
% 2.19/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.19/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/1.03  --bmc1_ucm_layered_model                none
% 2.19/1.03  --bmc1_ucm_max_lemma_size               10
% 2.19/1.03  
% 2.19/1.03  ------ AIG Options
% 2.19/1.03  
% 2.19/1.03  --aig_mode                              false
% 2.19/1.03  
% 2.19/1.03  ------ Instantiation Options
% 2.19/1.03  
% 2.19/1.03  --instantiation_flag                    true
% 2.19/1.03  --inst_sos_flag                         false
% 2.19/1.03  --inst_sos_phase                        true
% 2.19/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/1.03  --inst_lit_sel_side                     num_symb
% 2.19/1.03  --inst_solver_per_active                1400
% 2.19/1.03  --inst_solver_calls_frac                1.
% 2.19/1.03  --inst_passive_queue_type               priority_queues
% 2.19/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/1.03  --inst_passive_queues_freq              [25;2]
% 2.19/1.03  --inst_dismatching                      true
% 2.19/1.03  --inst_eager_unprocessed_to_passive     true
% 2.19/1.03  --inst_prop_sim_given                   true
% 2.19/1.03  --inst_prop_sim_new                     false
% 2.19/1.03  --inst_subs_new                         false
% 2.19/1.03  --inst_eq_res_simp                      false
% 2.19/1.03  --inst_subs_given                       false
% 2.19/1.03  --inst_orphan_elimination               true
% 2.19/1.03  --inst_learning_loop_flag               true
% 2.19/1.03  --inst_learning_start                   3000
% 2.19/1.03  --inst_learning_factor                  2
% 2.19/1.03  --inst_start_prop_sim_after_learn       3
% 2.19/1.03  --inst_sel_renew                        solver
% 2.19/1.03  --inst_lit_activity_flag                true
% 2.19/1.03  --inst_restr_to_given                   false
% 2.19/1.03  --inst_activity_threshold               500
% 2.19/1.03  --inst_out_proof                        true
% 2.19/1.03  
% 2.19/1.03  ------ Resolution Options
% 2.19/1.03  
% 2.19/1.03  --resolution_flag                       true
% 2.19/1.03  --res_lit_sel                           adaptive
% 2.19/1.03  --res_lit_sel_side                      none
% 2.19/1.03  --res_ordering                          kbo
% 2.19/1.03  --res_to_prop_solver                    active
% 2.19/1.03  --res_prop_simpl_new                    false
% 2.19/1.03  --res_prop_simpl_given                  true
% 2.19/1.03  --res_passive_queue_type                priority_queues
% 2.19/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/1.03  --res_passive_queues_freq               [15;5]
% 2.19/1.03  --res_forward_subs                      full
% 2.19/1.03  --res_backward_subs                     full
% 2.19/1.03  --res_forward_subs_resolution           true
% 2.19/1.03  --res_backward_subs_resolution          true
% 2.19/1.03  --res_orphan_elimination                true
% 2.19/1.03  --res_time_limit                        2.
% 2.19/1.03  --res_out_proof                         true
% 2.19/1.03  
% 2.19/1.03  ------ Superposition Options
% 2.19/1.03  
% 2.19/1.03  --superposition_flag                    true
% 2.19/1.03  --sup_passive_queue_type                priority_queues
% 2.19/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.19/1.03  --demod_completeness_check              fast
% 2.19/1.03  --demod_use_ground                      true
% 2.19/1.03  --sup_to_prop_solver                    passive
% 2.19/1.03  --sup_prop_simpl_new                    true
% 2.19/1.03  --sup_prop_simpl_given                  true
% 2.19/1.03  --sup_fun_splitting                     false
% 2.19/1.03  --sup_smt_interval                      50000
% 2.19/1.03  
% 2.19/1.03  ------ Superposition Simplification Setup
% 2.19/1.03  
% 2.19/1.03  --sup_indices_passive                   []
% 2.19/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_full_bw                           [BwDemod]
% 2.19/1.03  --sup_immed_triv                        [TrivRules]
% 2.19/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_immed_bw_main                     []
% 2.19/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.03  
% 2.19/1.03  ------ Combination Options
% 2.19/1.03  
% 2.19/1.03  --comb_res_mult                         3
% 2.19/1.03  --comb_sup_mult                         2
% 2.19/1.03  --comb_inst_mult                        10
% 2.19/1.03  
% 2.19/1.03  ------ Debug Options
% 2.19/1.03  
% 2.19/1.03  --dbg_backtrace                         false
% 2.19/1.03  --dbg_dump_prop_clauses                 false
% 2.19/1.03  --dbg_dump_prop_clauses_file            -
% 2.19/1.03  --dbg_out_stat                          false
% 2.19/1.03  ------ Parsing...
% 2.19/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.19/1.03  ------ Proving...
% 2.19/1.03  ------ Problem Properties 
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  clauses                                 17
% 2.19/1.03  conjectures                             3
% 2.19/1.03  EPR                                     0
% 2.19/1.03  Horn                                    15
% 2.19/1.03  unary                                   4
% 2.19/1.03  binary                                  2
% 2.19/1.03  lits                                    58
% 2.19/1.03  lits eq                                 8
% 2.19/1.03  fd_pure                                 0
% 2.19/1.03  fd_pseudo                               0
% 2.19/1.03  fd_cond                                 4
% 2.19/1.03  fd_pseudo_cond                          0
% 2.19/1.03  AC symbols                              0
% 2.19/1.03  
% 2.19/1.03  ------ Schedule dynamic 5 is on 
% 2.19/1.03  
% 2.19/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  ------ 
% 2.19/1.03  Current options:
% 2.19/1.03  ------ 
% 2.19/1.03  
% 2.19/1.03  ------ Input Options
% 2.19/1.03  
% 2.19/1.03  --out_options                           all
% 2.19/1.03  --tptp_safe_out                         true
% 2.19/1.03  --problem_path                          ""
% 2.19/1.03  --include_path                          ""
% 2.19/1.03  --clausifier                            res/vclausify_rel
% 2.19/1.03  --clausifier_options                    --mode clausify
% 2.19/1.03  --stdin                                 false
% 2.19/1.03  --stats_out                             all
% 2.19/1.03  
% 2.19/1.03  ------ General Options
% 2.19/1.03  
% 2.19/1.03  --fof                                   false
% 2.19/1.03  --time_out_real                         305.
% 2.19/1.03  --time_out_virtual                      -1.
% 2.19/1.03  --symbol_type_check                     false
% 2.19/1.03  --clausify_out                          false
% 2.19/1.03  --sig_cnt_out                           false
% 2.19/1.03  --trig_cnt_out                          false
% 2.19/1.03  --trig_cnt_out_tolerance                1.
% 2.19/1.03  --trig_cnt_out_sk_spl                   false
% 2.19/1.03  --abstr_cl_out                          false
% 2.19/1.03  
% 2.19/1.03  ------ Global Options
% 2.19/1.03  
% 2.19/1.03  --schedule                              default
% 2.19/1.03  --add_important_lit                     false
% 2.19/1.03  --prop_solver_per_cl                    1000
% 2.19/1.03  --min_unsat_core                        false
% 2.19/1.03  --soft_assumptions                      false
% 2.19/1.03  --soft_lemma_size                       3
% 2.19/1.03  --prop_impl_unit_size                   0
% 2.19/1.03  --prop_impl_unit                        []
% 2.19/1.03  --share_sel_clauses                     true
% 2.19/1.03  --reset_solvers                         false
% 2.19/1.03  --bc_imp_inh                            [conj_cone]
% 2.19/1.03  --conj_cone_tolerance                   3.
% 2.19/1.03  --extra_neg_conj                        none
% 2.19/1.03  --large_theory_mode                     true
% 2.19/1.03  --prolific_symb_bound                   200
% 2.19/1.03  --lt_threshold                          2000
% 2.19/1.03  --clause_weak_htbl                      true
% 2.19/1.03  --gc_record_bc_elim                     false
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing Options
% 2.19/1.03  
% 2.19/1.03  --preprocessing_flag                    true
% 2.19/1.03  --time_out_prep_mult                    0.1
% 2.19/1.03  --splitting_mode                        input
% 2.19/1.03  --splitting_grd                         true
% 2.19/1.03  --splitting_cvd                         false
% 2.19/1.03  --splitting_cvd_svl                     false
% 2.19/1.03  --splitting_nvd                         32
% 2.19/1.03  --sub_typing                            true
% 2.19/1.03  --prep_gs_sim                           true
% 2.19/1.03  --prep_unflatten                        true
% 2.19/1.03  --prep_res_sim                          true
% 2.19/1.03  --prep_upred                            true
% 2.19/1.03  --prep_sem_filter                       exhaustive
% 2.19/1.03  --prep_sem_filter_out                   false
% 2.19/1.03  --pred_elim                             true
% 2.19/1.03  --res_sim_input                         true
% 2.19/1.03  --eq_ax_congr_red                       true
% 2.19/1.03  --pure_diseq_elim                       true
% 2.19/1.03  --brand_transform                       false
% 2.19/1.03  --non_eq_to_eq                          false
% 2.19/1.03  --prep_def_merge                        true
% 2.19/1.03  --prep_def_merge_prop_impl              false
% 2.19/1.03  --prep_def_merge_mbd                    true
% 2.19/1.03  --prep_def_merge_tr_red                 false
% 2.19/1.03  --prep_def_merge_tr_cl                  false
% 2.19/1.03  --smt_preprocessing                     true
% 2.19/1.03  --smt_ac_axioms                         fast
% 2.19/1.03  --preprocessed_out                      false
% 2.19/1.03  --preprocessed_stats                    false
% 2.19/1.03  
% 2.19/1.03  ------ Abstraction refinement Options
% 2.19/1.03  
% 2.19/1.03  --abstr_ref                             []
% 2.19/1.03  --abstr_ref_prep                        false
% 2.19/1.03  --abstr_ref_until_sat                   false
% 2.19/1.03  --abstr_ref_sig_restrict                funpre
% 2.19/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/1.03  --abstr_ref_under                       []
% 2.19/1.03  
% 2.19/1.03  ------ SAT Options
% 2.19/1.03  
% 2.19/1.03  --sat_mode                              false
% 2.19/1.03  --sat_fm_restart_options                ""
% 2.19/1.03  --sat_gr_def                            false
% 2.19/1.03  --sat_epr_types                         true
% 2.19/1.03  --sat_non_cyclic_types                  false
% 2.19/1.03  --sat_finite_models                     false
% 2.19/1.03  --sat_fm_lemmas                         false
% 2.19/1.03  --sat_fm_prep                           false
% 2.19/1.03  --sat_fm_uc_incr                        true
% 2.19/1.03  --sat_out_model                         small
% 2.19/1.03  --sat_out_clauses                       false
% 2.19/1.03  
% 2.19/1.03  ------ QBF Options
% 2.19/1.03  
% 2.19/1.03  --qbf_mode                              false
% 2.19/1.03  --qbf_elim_univ                         false
% 2.19/1.03  --qbf_dom_inst                          none
% 2.19/1.03  --qbf_dom_pre_inst                      false
% 2.19/1.03  --qbf_sk_in                             false
% 2.19/1.03  --qbf_pred_elim                         true
% 2.19/1.03  --qbf_split                             512
% 2.19/1.03  
% 2.19/1.03  ------ BMC1 Options
% 2.19/1.03  
% 2.19/1.03  --bmc1_incremental                      false
% 2.19/1.03  --bmc1_axioms                           reachable_all
% 2.19/1.03  --bmc1_min_bound                        0
% 2.19/1.03  --bmc1_max_bound                        -1
% 2.19/1.03  --bmc1_max_bound_default                -1
% 2.19/1.03  --bmc1_symbol_reachability              true
% 2.19/1.03  --bmc1_property_lemmas                  false
% 2.19/1.03  --bmc1_k_induction                      false
% 2.19/1.03  --bmc1_non_equiv_states                 false
% 2.19/1.03  --bmc1_deadlock                         false
% 2.19/1.03  --bmc1_ucm                              false
% 2.19/1.03  --bmc1_add_unsat_core                   none
% 2.19/1.03  --bmc1_unsat_core_children              false
% 2.19/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/1.03  --bmc1_out_stat                         full
% 2.19/1.03  --bmc1_ground_init                      false
% 2.19/1.03  --bmc1_pre_inst_next_state              false
% 2.19/1.03  --bmc1_pre_inst_state                   false
% 2.19/1.03  --bmc1_pre_inst_reach_state             false
% 2.19/1.03  --bmc1_out_unsat_core                   false
% 2.19/1.03  --bmc1_aig_witness_out                  false
% 2.19/1.03  --bmc1_verbose                          false
% 2.19/1.03  --bmc1_dump_clauses_tptp                false
% 2.19/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.19/1.03  --bmc1_dump_file                        -
% 2.19/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.19/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.19/1.03  --bmc1_ucm_extend_mode                  1
% 2.19/1.03  --bmc1_ucm_init_mode                    2
% 2.19/1.03  --bmc1_ucm_cone_mode                    none
% 2.19/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.19/1.03  --bmc1_ucm_relax_model                  4
% 2.19/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.19/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/1.03  --bmc1_ucm_layered_model                none
% 2.19/1.03  --bmc1_ucm_max_lemma_size               10
% 2.19/1.03  
% 2.19/1.03  ------ AIG Options
% 2.19/1.03  
% 2.19/1.03  --aig_mode                              false
% 2.19/1.03  
% 2.19/1.03  ------ Instantiation Options
% 2.19/1.03  
% 2.19/1.03  --instantiation_flag                    true
% 2.19/1.03  --inst_sos_flag                         false
% 2.19/1.03  --inst_sos_phase                        true
% 2.19/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/1.03  --inst_lit_sel_side                     none
% 2.19/1.03  --inst_solver_per_active                1400
% 2.19/1.03  --inst_solver_calls_frac                1.
% 2.19/1.03  --inst_passive_queue_type               priority_queues
% 2.19/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/1.03  --inst_passive_queues_freq              [25;2]
% 2.19/1.03  --inst_dismatching                      true
% 2.19/1.03  --inst_eager_unprocessed_to_passive     true
% 2.19/1.03  --inst_prop_sim_given                   true
% 2.19/1.03  --inst_prop_sim_new                     false
% 2.19/1.03  --inst_subs_new                         false
% 2.19/1.03  --inst_eq_res_simp                      false
% 2.19/1.03  --inst_subs_given                       false
% 2.19/1.03  --inst_orphan_elimination               true
% 2.19/1.03  --inst_learning_loop_flag               true
% 2.19/1.03  --inst_learning_start                   3000
% 2.19/1.03  --inst_learning_factor                  2
% 2.19/1.03  --inst_start_prop_sim_after_learn       3
% 2.19/1.03  --inst_sel_renew                        solver
% 2.19/1.03  --inst_lit_activity_flag                true
% 2.19/1.03  --inst_restr_to_given                   false
% 2.19/1.03  --inst_activity_threshold               500
% 2.19/1.03  --inst_out_proof                        true
% 2.19/1.03  
% 2.19/1.03  ------ Resolution Options
% 2.19/1.03  
% 2.19/1.03  --resolution_flag                       false
% 2.19/1.03  --res_lit_sel                           adaptive
% 2.19/1.03  --res_lit_sel_side                      none
% 2.19/1.03  --res_ordering                          kbo
% 2.19/1.03  --res_to_prop_solver                    active
% 2.19/1.03  --res_prop_simpl_new                    false
% 2.19/1.03  --res_prop_simpl_given                  true
% 2.19/1.03  --res_passive_queue_type                priority_queues
% 2.19/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/1.03  --res_passive_queues_freq               [15;5]
% 2.19/1.03  --res_forward_subs                      full
% 2.19/1.03  --res_backward_subs                     full
% 2.19/1.03  --res_forward_subs_resolution           true
% 2.19/1.03  --res_backward_subs_resolution          true
% 2.19/1.03  --res_orphan_elimination                true
% 2.19/1.03  --res_time_limit                        2.
% 2.19/1.03  --res_out_proof                         true
% 2.19/1.03  
% 2.19/1.03  ------ Superposition Options
% 2.19/1.03  
% 2.19/1.03  --superposition_flag                    true
% 2.19/1.03  --sup_passive_queue_type                priority_queues
% 2.19/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.19/1.03  --demod_completeness_check              fast
% 2.19/1.03  --demod_use_ground                      true
% 2.19/1.03  --sup_to_prop_solver                    passive
% 2.19/1.03  --sup_prop_simpl_new                    true
% 2.19/1.03  --sup_prop_simpl_given                  true
% 2.19/1.03  --sup_fun_splitting                     false
% 2.19/1.03  --sup_smt_interval                      50000
% 2.19/1.03  
% 2.19/1.03  ------ Superposition Simplification Setup
% 2.19/1.03  
% 2.19/1.03  --sup_indices_passive                   []
% 2.19/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_full_bw                           [BwDemod]
% 2.19/1.03  --sup_immed_triv                        [TrivRules]
% 2.19/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_immed_bw_main                     []
% 2.19/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.03  
% 2.19/1.03  ------ Combination Options
% 2.19/1.03  
% 2.19/1.03  --comb_res_mult                         3
% 2.19/1.03  --comb_sup_mult                         2
% 2.19/1.03  --comb_inst_mult                        10
% 2.19/1.03  
% 2.19/1.03  ------ Debug Options
% 2.19/1.03  
% 2.19/1.03  --dbg_backtrace                         false
% 2.19/1.03  --dbg_dump_prop_clauses                 false
% 2.19/1.03  --dbg_dump_prop_clauses_file            -
% 2.19/1.03  --dbg_out_stat                          false
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  ------ Proving...
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  % SZS status Theorem for theBenchmark.p
% 2.19/1.03  
% 2.19/1.03   Resolution empty clause
% 2.19/1.03  
% 2.19/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.19/1.03  
% 2.19/1.03  fof(f2,axiom,(
% 2.19/1.03    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f15,plain,(
% 2.19/1.03    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.19/1.03    inference(ennf_transformation,[],[f2])).
% 2.19/1.03  
% 2.19/1.03  fof(f31,plain,(
% 2.19/1.03    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 2.19/1.03    introduced(choice_axiom,[])).
% 2.19/1.03  
% 2.19/1.03  fof(f32,plain,(
% 2.19/1.03    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 2.19/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f31])).
% 2.19/1.03  
% 2.19/1.03  fof(f44,plain,(
% 2.19/1.03    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.19/1.03    inference(cnf_transformation,[],[f32])).
% 2.19/1.03  
% 2.19/1.03  fof(f8,axiom,(
% 2.19/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f25,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/1.03    inference(ennf_transformation,[],[f8])).
% 2.19/1.03  
% 2.19/1.03  fof(f26,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/1.03    inference(flattening,[],[f25])).
% 2.19/1.03  
% 2.19/1.03  fof(f36,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/1.03    inference(nnf_transformation,[],[f26])).
% 2.19/1.03  
% 2.19/1.03  fof(f37,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/1.03    inference(flattening,[],[f36])).
% 2.19/1.03  
% 2.19/1.03  fof(f57,plain,(
% 2.19/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f37])).
% 2.19/1.03  
% 2.19/1.03  fof(f10,conjecture,(
% 2.19/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f11,negated_conjecture,(
% 2.19/1.03    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 2.19/1.03    inference(negated_conjecture,[],[f10])).
% 2.19/1.03  
% 2.19/1.03  fof(f29,plain,(
% 2.19/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1) & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.19/1.03    inference(ennf_transformation,[],[f11])).
% 2.19/1.03  
% 2.19/1.03  fof(f30,plain,(
% 2.19/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.19/1.03    inference(flattening,[],[f29])).
% 2.19/1.03  
% 2.19/1.03  fof(f41,plain,(
% 2.19/1.03    ( ! [X2,X0,X1] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) => (k1_xboole_0 != k3_orders_2(X0,sK4,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(sK4,X0,X2))) )),
% 2.19/1.03    introduced(choice_axiom,[])).
% 2.19/1.03  
% 2.19/1.03  fof(f40,plain,(
% 2.19/1.03    ( ! [X0,X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) => (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(sK3,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,sK3)) & m1_orders_1(sK3,k1_orders_1(u1_struct_0(X0))))) )),
% 2.19/1.03    introduced(choice_axiom,[])).
% 2.19/1.03  
% 2.19/1.03  fof(f39,plain,(
% 2.19/1.03    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,sK2) & k1_funct_1(X2,u1_struct_0(X0)) = sK2 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.19/1.03    introduced(choice_axiom,[])).
% 2.19/1.03  
% 2.19/1.03  fof(f38,plain,(
% 2.19/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK1,X3,X1) & k1_funct_1(X2,u1_struct_0(sK1)) = X1 & m2_orders_2(X3,sK1,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 2.19/1.03    introduced(choice_axiom,[])).
% 2.19/1.03  
% 2.19/1.03  fof(f42,plain,(
% 2.19/1.03    (((k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) & k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 & m2_orders_2(sK4,sK1,sK3)) & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 2.19/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f41,f40,f39,f38])).
% 2.19/1.03  
% 2.19/1.03  fof(f61,plain,(
% 2.19/1.03    v3_orders_2(sK1)),
% 2.19/1.03    inference(cnf_transformation,[],[f42])).
% 2.19/1.03  
% 2.19/1.03  fof(f60,plain,(
% 2.19/1.03    ~v2_struct_0(sK1)),
% 2.19/1.03    inference(cnf_transformation,[],[f42])).
% 2.19/1.03  
% 2.19/1.03  fof(f62,plain,(
% 2.19/1.03    v4_orders_2(sK1)),
% 2.19/1.03    inference(cnf_transformation,[],[f42])).
% 2.19/1.03  
% 2.19/1.03  fof(f63,plain,(
% 2.19/1.03    v5_orders_2(sK1)),
% 2.19/1.03    inference(cnf_transformation,[],[f42])).
% 2.19/1.03  
% 2.19/1.03  fof(f64,plain,(
% 2.19/1.03    l1_orders_2(sK1)),
% 2.19/1.03    inference(cnf_transformation,[],[f42])).
% 2.19/1.03  
% 2.19/1.03  fof(f4,axiom,(
% 2.19/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f17,plain,(
% 2.19/1.03    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/1.03    inference(ennf_transformation,[],[f4])).
% 2.19/1.03  
% 2.19/1.03  fof(f18,plain,(
% 2.19/1.03    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/1.03    inference(flattening,[],[f17])).
% 2.19/1.03  
% 2.19/1.03  fof(f50,plain,(
% 2.19/1.03    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f18])).
% 2.19/1.03  
% 2.19/1.03  fof(f1,axiom,(
% 2.19/1.03    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f13,plain,(
% 2.19/1.03    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.19/1.03    inference(ennf_transformation,[],[f1])).
% 2.19/1.03  
% 2.19/1.03  fof(f14,plain,(
% 2.19/1.03    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.19/1.03    inference(flattening,[],[f13])).
% 2.19/1.03  
% 2.19/1.03  fof(f43,plain,(
% 2.19/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f14])).
% 2.19/1.03  
% 2.19/1.03  fof(f56,plain,(
% 2.19/1.03    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f37])).
% 2.19/1.03  
% 2.19/1.03  fof(f65,plain,(
% 2.19/1.03    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.19/1.03    inference(cnf_transformation,[],[f42])).
% 2.19/1.03  
% 2.19/1.03  fof(f6,axiom,(
% 2.19/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f21,plain,(
% 2.19/1.03    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/1.03    inference(ennf_transformation,[],[f6])).
% 2.19/1.03  
% 2.19/1.03  fof(f22,plain,(
% 2.19/1.03    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/1.03    inference(flattening,[],[f21])).
% 2.19/1.03  
% 2.19/1.03  fof(f35,plain,(
% 2.19/1.03    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/1.03    inference(nnf_transformation,[],[f22])).
% 2.19/1.03  
% 2.19/1.03  fof(f52,plain,(
% 2.19/1.03    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f35])).
% 2.19/1.03  
% 2.19/1.03  fof(f9,axiom,(
% 2.19/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) => ! [X4] : (m2_orders_2(X4,X0,X3) => ((k1_funct_1(X3,u1_struct_0(X0)) = X2 & r2_hidden(X1,X4)) => r3_orders_2(X0,X2,X1)))))))),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f27,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r3_orders_2(X0,X2,X1) | (k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4))) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/1.03    inference(ennf_transformation,[],[f9])).
% 2.19/1.03  
% 2.19/1.03  fof(f28,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/1.03    inference(flattening,[],[f27])).
% 2.19/1.03  
% 2.19/1.03  fof(f59,plain,(
% 2.19/1.03    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f28])).
% 2.19/1.03  
% 2.19/1.03  fof(f71,plain,(
% 2.19/1.03    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,k1_funct_1(X3,u1_struct_0(X0)),X1) | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(k1_funct_1(X3,u1_struct_0(X0)),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/1.03    inference(equality_resolution,[],[f59])).
% 2.19/1.03  
% 2.19/1.03  fof(f67,plain,(
% 2.19/1.03    m2_orders_2(sK4,sK1,sK3)),
% 2.19/1.03    inference(cnf_transformation,[],[f42])).
% 2.19/1.03  
% 2.19/1.03  fof(f66,plain,(
% 2.19/1.03    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))),
% 2.19/1.03    inference(cnf_transformation,[],[f42])).
% 2.19/1.03  
% 2.19/1.03  fof(f7,axiom,(
% 2.19/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) => r2_orders_2(X0,X1,X3))))))),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f23,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_orders_2(X0,X1,X3) | ((~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2)))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)))),
% 2.19/1.03    inference(ennf_transformation,[],[f7])).
% 2.19/1.03  
% 2.19/1.03  fof(f24,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_orders_2(X0,X1,X3) | ((~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0))),
% 2.19/1.03    inference(flattening,[],[f23])).
% 2.19/1.03  
% 2.19/1.03  fof(f55,plain,(
% 2.19/1.03    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X3) | ~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f24])).
% 2.19/1.03  
% 2.19/1.03  fof(f68,plain,(
% 2.19/1.03    k1_funct_1(sK3,u1_struct_0(sK1)) = sK2),
% 2.19/1.03    inference(cnf_transformation,[],[f42])).
% 2.19/1.03  
% 2.19/1.03  fof(f5,axiom,(
% 2.19/1.03    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f12,plain,(
% 2.19/1.03    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.19/1.03    inference(pure_predicate_removal,[],[f5])).
% 2.19/1.03  
% 2.19/1.03  fof(f19,plain,(
% 2.19/1.03    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/1.03    inference(ennf_transformation,[],[f12])).
% 2.19/1.03  
% 2.19/1.03  fof(f20,plain,(
% 2.19/1.03    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/1.03    inference(flattening,[],[f19])).
% 2.19/1.03  
% 2.19/1.03  fof(f51,plain,(
% 2.19/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f20])).
% 2.19/1.03  
% 2.19/1.03  fof(f3,axiom,(
% 2.19/1.03    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 2.19/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.03  
% 2.19/1.03  fof(f16,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.19/1.03    inference(ennf_transformation,[],[f3])).
% 2.19/1.03  
% 2.19/1.03  fof(f33,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.19/1.03    inference(nnf_transformation,[],[f16])).
% 2.19/1.03  
% 2.19/1.03  fof(f34,plain,(
% 2.19/1.03    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.19/1.03    inference(flattening,[],[f33])).
% 2.19/1.03  
% 2.19/1.03  fof(f48,plain,(
% 2.19/1.03    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.19/1.03    inference(cnf_transformation,[],[f34])).
% 2.19/1.03  
% 2.19/1.03  fof(f70,plain,(
% 2.19/1.03    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.19/1.03    inference(equality_resolution,[],[f48])).
% 2.19/1.03  
% 2.19/1.03  fof(f69,plain,(
% 2.19/1.03    k1_xboole_0 != k3_orders_2(sK1,sK4,sK2)),
% 2.19/1.03    inference(cnf_transformation,[],[f42])).
% 2.19/1.03  
% 2.19/1.03  cnf(c_3,plain,
% 2.19/1.03      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.19/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1107,plain,
% 2.19/1.03      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_14,plain,
% 2.19/1.03      ( r2_hidden(X0,X1)
% 2.19/1.03      | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
% 2.19/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 2.19/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.19/1.03      | v2_struct_0(X2)
% 2.19/1.03      | ~ v3_orders_2(X2)
% 2.19/1.03      | ~ v4_orders_2(X2)
% 2.19/1.03      | ~ v5_orders_2(X2)
% 2.19/1.03      | ~ l1_orders_2(X2) ),
% 2.19/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_25,negated_conjecture,
% 2.19/1.03      ( v3_orders_2(sK1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_424,plain,
% 2.19/1.03      ( r2_hidden(X0,X1)
% 2.19/1.03      | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
% 2.19/1.03      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 2.19/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.19/1.03      | v2_struct_0(X2)
% 2.19/1.03      | ~ v4_orders_2(X2)
% 2.19/1.03      | ~ v5_orders_2(X2)
% 2.19/1.03      | ~ l1_orders_2(X2)
% 2.19/1.03      | sK1 != X2 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_425,plain,
% 2.19/1.03      ( r2_hidden(X0,X1)
% 2.19/1.03      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.19/1.03      | v2_struct_0(sK1)
% 2.19/1.03      | ~ v4_orders_2(sK1)
% 2.19/1.03      | ~ v5_orders_2(sK1)
% 2.19/1.03      | ~ l1_orders_2(sK1) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_424]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_26,negated_conjecture,
% 2.19/1.03      ( ~ v2_struct_0(sK1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_24,negated_conjecture,
% 2.19/1.03      ( v4_orders_2(sK1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_23,negated_conjecture,
% 2.19/1.03      ( v5_orders_2(sK1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_22,negated_conjecture,
% 2.19/1.03      ( l1_orders_2(sK1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_429,plain,
% 2.19/1.03      ( r2_hidden(X0,X1)
% 2.19/1.03      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_425,c_26,c_24,c_23,c_22]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_430,plain,
% 2.19/1.03      ( r2_hidden(X0,X1)
% 2.19/1.03      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
% 2.19/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.19/1.03      inference(renaming,[status(thm)],[c_429]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1101,plain,
% 2.19/1.03      ( r2_hidden(X0,X1) = iProver_top
% 2.19/1.03      | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_431,plain,
% 2.19/1.03      ( r2_hidden(X0,X1) = iProver_top
% 2.19/1.03      | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_7,plain,
% 2.19/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.19/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.03      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.03      | v2_struct_0(X1)
% 2.19/1.03      | ~ v3_orders_2(X1)
% 2.19/1.03      | ~ v4_orders_2(X1)
% 2.19/1.03      | ~ v5_orders_2(X1)
% 2.19/1.03      | ~ l1_orders_2(X1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_403,plain,
% 2.19/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.19/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.03      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.03      | v2_struct_0(X1)
% 2.19/1.03      | ~ v4_orders_2(X1)
% 2.19/1.03      | ~ v5_orders_2(X1)
% 2.19/1.03      | ~ l1_orders_2(X1)
% 2.19/1.03      | sK1 != X1 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_25]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_404,plain,
% 2.19/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.19/1.03      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.19/1.03      | v2_struct_0(sK1)
% 2.19/1.03      | ~ v4_orders_2(sK1)
% 2.19/1.03      | ~ v5_orders_2(sK1)
% 2.19/1.03      | ~ l1_orders_2(sK1) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_403]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_408,plain,
% 2.19/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.19/1.03      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_404,c_26,c_24,c_23,c_22]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1102,plain,
% 2.19/1.03      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.19/1.03      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_0,plain,
% 2.19/1.03      ( ~ r2_hidden(X0,X1)
% 2.19/1.03      | m1_subset_1(X0,X2)
% 2.19/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.19/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1110,plain,
% 2.19/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,X2) = iProver_top
% 2.19/1.03      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1681,plain,
% 2.19/1.03      ( r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
% 2.19/1.03      | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
% 2.19/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1102,c_1110]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1900,plain,
% 2.19/1.03      ( r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
% 2.19/1.03      | r2_hidden(X0,X1) = iProver_top
% 2.19/1.03      | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_1101,c_431,c_1681]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1901,plain,
% 2.19/1.03      ( r2_hidden(X0,X1) = iProver_top
% 2.19/1.03      | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
% 2.19/1.03      | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.19/1.03      inference(renaming,[status(thm)],[c_1900]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1908,plain,
% 2.19/1.03      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 2.19/1.03      | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
% 2.19/1.03      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1107,c_1901]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_15,plain,
% 2.19/1.03      ( r2_orders_2(X0,X1,X2)
% 2.19/1.03      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 2.19/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.19/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.19/1.03      | v2_struct_0(X0)
% 2.19/1.03      | ~ v3_orders_2(X0)
% 2.19/1.03      | ~ v4_orders_2(X0)
% 2.19/1.03      | ~ v5_orders_2(X0)
% 2.19/1.03      | ~ l1_orders_2(X0) ),
% 2.19/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_346,plain,
% 2.19/1.03      ( r2_orders_2(X0,X1,X2)
% 2.19/1.03      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 2.19/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.19/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.19/1.03      | v2_struct_0(X0)
% 2.19/1.03      | ~ v4_orders_2(X0)
% 2.19/1.03      | ~ v5_orders_2(X0)
% 2.19/1.03      | ~ l1_orders_2(X0)
% 2.19/1.03      | sK1 != X0 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_347,plain,
% 2.19/1.03      ( r2_orders_2(sK1,X0,X1)
% 2.19/1.03      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.19/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.19/1.03      | v2_struct_0(sK1)
% 2.19/1.03      | ~ v4_orders_2(sK1)
% 2.19/1.03      | ~ v5_orders_2(sK1)
% 2.19/1.03      | ~ l1_orders_2(sK1) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_346]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_351,plain,
% 2.19/1.03      ( r2_orders_2(sK1,X0,X1)
% 2.19/1.03      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.19/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_347,c_26,c_24,c_23,c_22]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_352,plain,
% 2.19/1.03      ( r2_orders_2(sK1,X0,X1)
% 2.19/1.03      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.19/1.03      inference(renaming,[status(thm)],[c_351]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1104,plain,
% 2.19/1.03      ( r2_orders_2(sK1,X0,X1) = iProver_top
% 2.19/1.03      | r2_hidden(X0,k3_orders_2(sK1,X2,X1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_352]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1918,plain,
% 2.19/1.03      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 2.19/1.03      | r2_orders_2(sK1,sK0(k3_orders_2(sK1,X0,X1)),X1) = iProver_top
% 2.19/1.03      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.19/1.03      | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) != iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1107,c_1104]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2124,plain,
% 2.19/1.03      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 2.19/1.03      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.19/1.03      | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) = iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1107,c_1681]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2497,plain,
% 2.19/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.19/1.03      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | r2_orders_2(sK1,sK0(k3_orders_2(sK1,X0,X1)),X1) = iProver_top
% 2.19/1.03      | k3_orders_2(sK1,X0,X1) = k1_xboole_0 ),
% 2.19/1.03      inference(global_propositional_subsumption,[status(thm)],[c_1918,c_2124]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2498,plain,
% 2.19/1.03      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 2.19/1.03      | r2_orders_2(sK1,sK0(k3_orders_2(sK1,X0,X1)),X1) = iProver_top
% 2.19/1.03      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.19/1.03      inference(renaming,[status(thm)],[c_2497]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_21,negated_conjecture,
% 2.19/1.03      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.19/1.03      inference(cnf_transformation,[],[f65]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1106,plain,
% 2.19/1.03      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_10,plain,
% 2.19/1.03      ( ~ r3_orders_2(X0,X1,X2)
% 2.19/1.03      | r1_orders_2(X0,X1,X2)
% 2.19/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.19/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/1.03      | v2_struct_0(X0)
% 2.19/1.03      | ~ v3_orders_2(X0)
% 2.19/1.03      | ~ l1_orders_2(X0) ),
% 2.19/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_16,plain,
% 2.19/1.03      ( r3_orders_2(X0,k1_funct_1(X1,u1_struct_0(X0)),X2)
% 2.19/1.03      | ~ m2_orders_2(X3,X0,X1)
% 2.19/1.03      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 2.19/1.03      | ~ r2_hidden(X2,X3)
% 2.19/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.19/1.03      | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(X0)),u1_struct_0(X0))
% 2.19/1.03      | v2_struct_0(X0)
% 2.19/1.03      | ~ v3_orders_2(X0)
% 2.19/1.03      | ~ v4_orders_2(X0)
% 2.19/1.03      | ~ v5_orders_2(X0)
% 2.19/1.03      | ~ l1_orders_2(X0) ),
% 2.19/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_19,negated_conjecture,
% 2.19/1.03      ( m2_orders_2(sK4,sK1,sK3) ),
% 2.19/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_285,plain,
% 2.19/1.03      ( r3_orders_2(X0,k1_funct_1(X1,u1_struct_0(X0)),X2)
% 2.19/1.03      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 2.19/1.03      | ~ r2_hidden(X2,X3)
% 2.19/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.19/1.03      | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(X0)),u1_struct_0(X0))
% 2.19/1.03      | v2_struct_0(X0)
% 2.19/1.03      | ~ v3_orders_2(X0)
% 2.19/1.03      | ~ v4_orders_2(X0)
% 2.19/1.03      | ~ v5_orders_2(X0)
% 2.19/1.03      | ~ l1_orders_2(X0)
% 2.19/1.03      | sK3 != X1
% 2.19/1.03      | sK4 != X3
% 2.19/1.03      | sK1 != X0 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_286,plain,
% 2.19/1.03      ( r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
% 2.19/1.03      | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
% 2.19/1.03      | ~ r2_hidden(X0,sK4)
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.19/1.03      | v2_struct_0(sK1)
% 2.19/1.03      | ~ v3_orders_2(sK1)
% 2.19/1.03      | ~ v4_orders_2(sK1)
% 2.19/1.03      | ~ v5_orders_2(sK1)
% 2.19/1.03      | ~ l1_orders_2(sK1) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_285]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_20,negated_conjecture,
% 2.19/1.03      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) ),
% 2.19/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_290,plain,
% 2.19/1.03      ( ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ r2_hidden(X0,sK4)
% 2.19/1.03      | r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0) ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_286,c_26,c_25,c_24,c_23,c_22,c_20]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_291,plain,
% 2.19/1.03      ( r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
% 2.19/1.03      | ~ r2_hidden(X0,sK4)
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
% 2.19/1.03      inference(renaming,[status(thm)],[c_290]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_317,plain,
% 2.19/1.03      ( r1_orders_2(X0,X1,X2)
% 2.19/1.03      | ~ r2_hidden(X3,sK4)
% 2.19/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.19/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.19/1.03      | v2_struct_0(X0)
% 2.19/1.03      | ~ v3_orders_2(X0)
% 2.19/1.03      | ~ l1_orders_2(X0)
% 2.19/1.03      | X3 != X2
% 2.19/1.03      | k1_funct_1(sK3,u1_struct_0(sK1)) != X1
% 2.19/1.03      | sK1 != X0 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_291]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_318,plain,
% 2.19/1.03      ( r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
% 2.19/1.03      | ~ r2_hidden(X0,sK4)
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.19/1.03      | v2_struct_0(sK1)
% 2.19/1.03      | ~ v3_orders_2(sK1)
% 2.19/1.03      | ~ l1_orders_2(sK1) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_317]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_322,plain,
% 2.19/1.03      ( ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ r2_hidden(X0,sK4)
% 2.19/1.03      | r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0) ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_318,c_26,c_25,c_22]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_323,plain,
% 2.19/1.03      ( r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
% 2.19/1.03      | ~ r2_hidden(X0,sK4)
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
% 2.19/1.03      inference(renaming,[status(thm)],[c_322]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_11,plain,
% 2.19/1.03      ( ~ r1_orders_2(X0,X1,X2)
% 2.19/1.03      | ~ r2_orders_2(X0,X2,X3)
% 2.19/1.03      | r2_orders_2(X0,X1,X3)
% 2.19/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.19/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.19/1.03      | ~ v4_orders_2(X0)
% 2.19/1.03      | ~ v5_orders_2(X0)
% 2.19/1.03      | ~ l1_orders_2(X0) ),
% 2.19/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_499,plain,
% 2.19/1.03      ( ~ r1_orders_2(X0,X1,X2)
% 2.19/1.03      | ~ r2_orders_2(X0,X2,X3)
% 2.19/1.03      | r2_orders_2(X0,X1,X3)
% 2.19/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.19/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.19/1.03      | ~ v4_orders_2(X0)
% 2.19/1.03      | ~ l1_orders_2(X0)
% 2.19/1.03      | sK1 != X0 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_500,plain,
% 2.19/1.03      ( ~ r1_orders_2(sK1,X0,X1)
% 2.19/1.03      | ~ r2_orders_2(sK1,X1,X2)
% 2.19/1.03      | r2_orders_2(sK1,X0,X2)
% 2.19/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ v4_orders_2(sK1)
% 2.19/1.03      | ~ l1_orders_2(sK1) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_499]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_502,plain,
% 2.19/1.03      ( ~ r1_orders_2(sK1,X0,X1)
% 2.19/1.03      | ~ r2_orders_2(sK1,X1,X2)
% 2.19/1.03      | r2_orders_2(sK1,X0,X2)
% 2.19/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_500,c_24,c_22]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_503,plain,
% 2.19/1.03      ( ~ r1_orders_2(sK1,X0,X1)
% 2.19/1.03      | ~ r2_orders_2(sK1,X1,X2)
% 2.19/1.03      | r2_orders_2(sK1,X0,X2)
% 2.19/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 2.19/1.03      inference(renaming,[status(thm)],[c_502]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_649,plain,
% 2.19/1.03      ( ~ r2_orders_2(sK1,X0,X1)
% 2.19/1.03      | r2_orders_2(sK1,X2,X1)
% 2.19/1.03      | ~ r2_hidden(X3,sK4)
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.19/1.03      | X0 != X3
% 2.19/1.03      | k1_funct_1(sK3,u1_struct_0(sK1)) != X2
% 2.19/1.03      | sK1 != sK1 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_323,c_503]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_650,plain,
% 2.19/1.03      ( ~ r2_orders_2(sK1,X0,X1)
% 2.19/1.03      | r2_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X1)
% 2.19/1.03      | ~ r2_hidden(X0,sK4)
% 2.19/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.19/1.03      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_649]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1097,plain,
% 2.19/1.03      ( r2_orders_2(sK1,X0,X1) != iProver_top
% 2.19/1.03      | r2_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X1) = iProver_top
% 2.19/1.03      | r2_hidden(X0,sK4) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_650]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_18,negated_conjecture,
% 2.19/1.03      ( k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 ),
% 2.19/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1218,plain,
% 2.19/1.03      ( r2_orders_2(sK1,X0,X1) != iProver_top
% 2.19/1.03      | r2_orders_2(sK1,sK2,X1) = iProver_top
% 2.19/1.03      | r2_hidden(X0,sK4) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.19/1.03      inference(light_normalisation,[status(thm)],[c_1097,c_18]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1225,plain,
% 2.19/1.03      ( r2_orders_2(sK1,X0,X1) != iProver_top
% 2.19/1.03      | r2_orders_2(sK1,sK2,X1) = iProver_top
% 2.19/1.03      | r2_hidden(X0,sK4) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
% 2.19/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_1218,c_1106]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_8,plain,
% 2.19/1.03      ( ~ m2_orders_2(X0,X1,X2)
% 2.19/1.03      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.19/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.03      | v2_struct_0(X1)
% 2.19/1.03      | ~ v3_orders_2(X1)
% 2.19/1.03      | ~ v4_orders_2(X1)
% 2.19/1.03      | ~ v5_orders_2(X1)
% 2.19/1.03      | ~ l1_orders_2(X1) ),
% 2.19/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_274,plain,
% 2.19/1.03      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
% 2.19/1.03      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.19/1.03      | v2_struct_0(X1)
% 2.19/1.03      | ~ v3_orders_2(X1)
% 2.19/1.03      | ~ v4_orders_2(X1)
% 2.19/1.03      | ~ v5_orders_2(X1)
% 2.19/1.03      | ~ l1_orders_2(X1)
% 2.19/1.03      | sK3 != X0
% 2.19/1.03      | sK4 != X2
% 2.19/1.03      | sK1 != X1 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_275,plain,
% 2.19/1.03      ( ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
% 2.19/1.03      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.19/1.03      | v2_struct_0(sK1)
% 2.19/1.03      | ~ v3_orders_2(sK1)
% 2.19/1.03      | ~ v4_orders_2(sK1)
% 2.19/1.03      | ~ v5_orders_2(sK1)
% 2.19/1.03      | ~ l1_orders_2(sK1) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_274]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_277,plain,
% 2.19/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_275,c_26,c_25,c_24,c_23,c_22,c_20]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1105,plain,
% 2.19/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1680,plain,
% 2.19/1.03      ( r2_hidden(X0,sK4) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1105,c_1110]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1699,plain,
% 2.19/1.03      ( r2_hidden(X0,sK4) != iProver_top
% 2.19/1.03      | r2_orders_2(sK1,sK2,X1) = iProver_top
% 2.19/1.03      | r2_orders_2(sK1,X0,X1) != iProver_top
% 2.19/1.03      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
% 2.19/1.03      inference(global_propositional_subsumption,[status(thm)],[c_1225,c_1680]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1700,plain,
% 2.19/1.03      ( r2_orders_2(sK1,X0,X1) != iProver_top
% 2.19/1.03      | r2_orders_2(sK1,sK2,X1) = iProver_top
% 2.19/1.03      | r2_hidden(X0,sK4) != iProver_top
% 2.19/1.03      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
% 2.19/1.03      inference(renaming,[status(thm)],[c_1699]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1707,plain,
% 2.19/1.03      ( r2_orders_2(sK1,X0,sK2) != iProver_top
% 2.19/1.03      | r2_orders_2(sK1,sK2,sK2) = iProver_top
% 2.19/1.03      | r2_hidden(X0,sK4) != iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1106,c_1700]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_32,plain,
% 2.19/1.03      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_5,plain,
% 2.19/1.03      ( ~ r2_orders_2(X0,X1,X1)
% 2.19/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/1.03      | ~ l1_orders_2(X0) ),
% 2.19/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_557,plain,
% 2.19/1.03      ( ~ r2_orders_2(X0,X1,X1)
% 2.19/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.19/1.03      | sK1 != X0 ),
% 2.19/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_22]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_558,plain,
% 2.19/1.03      ( ~ r2_orders_2(sK1,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.19/1.03      inference(unflattening,[status(thm)],[c_557]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1268,plain,
% 2.19/1.03      ( ~ r2_orders_2(sK1,sK2,sK2) | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.19/1.03      inference(instantiation,[status(thm)],[c_558]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1269,plain,
% 2.19/1.03      ( r2_orders_2(sK1,sK2,sK2) != iProver_top
% 2.19/1.03      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_1268]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_1784,plain,
% 2.19/1.03      ( r2_orders_2(sK1,X0,sK2) != iProver_top
% 2.19/1.03      | r2_hidden(X0,sK4) != iProver_top ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_1707,c_32,c_1269]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2507,plain,
% 2.19/1.03      ( k3_orders_2(sK1,X0,sK2) = k1_xboole_0
% 2.19/1.03      | r2_hidden(sK0(k3_orders_2(sK1,X0,sK2)),sK4) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.19/1.03      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_2498,c_1784]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2581,plain,
% 2.19/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.19/1.03      | r2_hidden(sK0(k3_orders_2(sK1,X0,sK2)),sK4) != iProver_top
% 2.19/1.03      | k3_orders_2(sK1,X0,sK2) = k1_xboole_0 ),
% 2.19/1.03      inference(global_propositional_subsumption,[status(thm)],[c_2507,c_32]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2582,plain,
% 2.19/1.03      ( k3_orders_2(sK1,X0,sK2) = k1_xboole_0
% 2.19/1.03      | r2_hidden(sK0(k3_orders_2(sK1,X0,sK2)),sK4) != iProver_top
% 2.19/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.19/1.03      inference(renaming,[status(thm)],[c_2581]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_2590,plain,
% 2.19/1.03      ( k3_orders_2(sK1,sK4,sK2) = k1_xboole_0
% 2.19/1.03      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.19/1.03      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.19/1.03      inference(superposition,[status(thm)],[c_1908,c_2582]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_27,plain,
% 2.19/1.03      ( v2_struct_0(sK1) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_28,plain,
% 2.19/1.03      ( v3_orders_2(sK1) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_29,plain,
% 2.19/1.03      ( v4_orders_2(sK1) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_30,plain,
% 2.19/1.03      ( v5_orders_2(sK1) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_31,plain,
% 2.19/1.03      ( l1_orders_2(sK1) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_33,plain,
% 2.19/1.03      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_276,plain,
% 2.19/1.03      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) != iProver_top
% 2.19/1.03      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.19/1.03      | v2_struct_0(sK1) = iProver_top
% 2.19/1.03      | v3_orders_2(sK1) != iProver_top
% 2.19/1.03      | v4_orders_2(sK1) != iProver_top
% 2.19/1.03      | v5_orders_2(sK1) != iProver_top
% 2.19/1.03      | l1_orders_2(sK1) != iProver_top ),
% 2.19/1.03      inference(predicate_to_equality,[status(thm)],[c_275]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_3349,plain,
% 2.19/1.03      ( k3_orders_2(sK1,sK4,sK2) = k1_xboole_0 ),
% 2.19/1.03      inference(global_propositional_subsumption,
% 2.19/1.03                [status(thm)],
% 2.19/1.03                [c_2590,c_27,c_28,c_29,c_30,c_31,c_32,c_33,c_276]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_17,negated_conjecture,
% 2.19/1.03      ( k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) ),
% 2.19/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_3352,plain,
% 2.19/1.03      ( k1_xboole_0 != k1_xboole_0 ),
% 2.19/1.03      inference(demodulation,[status(thm)],[c_3349,c_17]) ).
% 2.19/1.03  
% 2.19/1.03  cnf(c_3424,plain,
% 2.19/1.03      ( $false ),
% 2.19/1.03      inference(equality_resolution_simp,[status(thm)],[c_3352]) ).
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.19/1.03  
% 2.19/1.03  ------                               Statistics
% 2.19/1.03  
% 2.19/1.03  ------ General
% 2.19/1.03  
% 2.19/1.03  abstr_ref_over_cycles:                  0
% 2.19/1.03  abstr_ref_under_cycles:                 0
% 2.19/1.03  gc_basic_clause_elim:                   0
% 2.19/1.03  forced_gc_time:                         0
% 2.19/1.03  parsing_time:                           0.014
% 2.19/1.03  unif_index_cands_time:                  0.
% 2.19/1.03  unif_index_add_time:                    0.
% 2.19/1.03  orderings_time:                         0.
% 2.19/1.03  out_proof_time:                         0.01
% 2.19/1.03  total_time:                             0.164
% 2.19/1.03  num_of_symbols:                         55
% 2.19/1.03  num_of_terms:                           2821
% 2.19/1.03  
% 2.19/1.03  ------ Preprocessing
% 2.19/1.03  
% 2.19/1.03  num_of_splits:                          0
% 2.19/1.03  num_of_split_atoms:                     0
% 2.19/1.03  num_of_reused_defs:                     0
% 2.19/1.03  num_eq_ax_congr_red:                    17
% 2.19/1.03  num_of_sem_filtered_clauses:            1
% 2.19/1.03  num_of_subtypes:                        0
% 2.19/1.03  monotx_restored_types:                  0
% 2.19/1.03  sat_num_of_epr_types:                   0
% 2.19/1.03  sat_num_of_non_cyclic_types:            0
% 2.19/1.03  sat_guarded_non_collapsed_types:        0
% 2.19/1.03  num_pure_diseq_elim:                    0
% 2.19/1.03  simp_replaced_by:                       0
% 2.19/1.03  res_preprocessed:                       97
% 2.19/1.03  prep_upred:                             0
% 2.19/1.03  prep_unflattend:                        24
% 2.19/1.03  smt_new_axioms:                         0
% 2.19/1.03  pred_elim_cands:                        3
% 2.19/1.03  pred_elim:                              9
% 2.19/1.03  pred_elim_cl:                           10
% 2.19/1.03  pred_elim_cycles:                       11
% 2.19/1.03  merged_defs:                            0
% 2.19/1.03  merged_defs_ncl:                        0
% 2.19/1.03  bin_hyper_res:                          0
% 2.19/1.03  prep_cycles:                            4
% 2.19/1.03  pred_elim_time:                         0.012
% 2.19/1.03  splitting_time:                         0.
% 2.19/1.03  sem_filter_time:                        0.
% 2.19/1.03  monotx_time:                            0.001
% 2.19/1.03  subtype_inf_time:                       0.
% 2.19/1.03  
% 2.19/1.03  ------ Problem properties
% 2.19/1.03  
% 2.19/1.03  clauses:                                17
% 2.19/1.03  conjectures:                            3
% 2.19/1.03  epr:                                    0
% 2.19/1.03  horn:                                   15
% 2.19/1.03  ground:                                 4
% 2.19/1.03  unary:                                  4
% 2.19/1.03  binary:                                 2
% 2.19/1.03  lits:                                   58
% 2.19/1.03  lits_eq:                                8
% 2.19/1.03  fd_pure:                                0
% 2.19/1.03  fd_pseudo:                              0
% 2.19/1.03  fd_cond:                                4
% 2.19/1.03  fd_pseudo_cond:                         0
% 2.19/1.03  ac_symbols:                             0
% 2.19/1.03  
% 2.19/1.03  ------ Propositional Solver
% 2.19/1.03  
% 2.19/1.03  prop_solver_calls:                      28
% 2.19/1.03  prop_fast_solver_calls:                 1031
% 2.19/1.03  smt_solver_calls:                       0
% 2.19/1.03  smt_fast_solver_calls:                  0
% 2.19/1.03  prop_num_of_clauses:                    1258
% 2.19/1.03  prop_preprocess_simplified:             3792
% 2.19/1.03  prop_fo_subsumed:                       43
% 2.19/1.03  prop_solver_time:                       0.
% 2.19/1.03  smt_solver_time:                        0.
% 2.19/1.03  smt_fast_solver_time:                   0.
% 2.19/1.03  prop_fast_solver_time:                  0.
% 2.19/1.03  prop_unsat_core_time:                   0.
% 2.19/1.03  
% 2.19/1.03  ------ QBF
% 2.19/1.03  
% 2.19/1.03  qbf_q_res:                              0
% 2.19/1.03  qbf_num_tautologies:                    0
% 2.19/1.03  qbf_prep_cycles:                        0
% 2.19/1.03  
% 2.19/1.03  ------ BMC1
% 2.19/1.03  
% 2.19/1.03  bmc1_current_bound:                     -1
% 2.19/1.03  bmc1_last_solved_bound:                 -1
% 2.19/1.03  bmc1_unsat_core_size:                   -1
% 2.19/1.03  bmc1_unsat_core_parents_size:           -1
% 2.19/1.03  bmc1_merge_next_fun:                    0
% 2.19/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.19/1.03  
% 2.19/1.03  ------ Instantiation
% 2.19/1.03  
% 2.19/1.03  inst_num_of_clauses:                    387
% 2.19/1.03  inst_num_in_passive:                    58
% 2.19/1.03  inst_num_in_active:                     167
% 2.19/1.03  inst_num_in_unprocessed:                162
% 2.19/1.03  inst_num_of_loops:                      180
% 2.19/1.03  inst_num_of_learning_restarts:          0
% 2.19/1.03  inst_num_moves_active_passive:          10
% 2.19/1.03  inst_lit_activity:                      0
% 2.19/1.03  inst_lit_activity_moves:                0
% 2.19/1.03  inst_num_tautologies:                   0
% 2.19/1.03  inst_num_prop_implied:                  0
% 2.19/1.03  inst_num_existing_simplified:           0
% 2.19/1.03  inst_num_eq_res_simplified:             0
% 2.19/1.03  inst_num_child_elim:                    0
% 2.19/1.03  inst_num_of_dismatching_blockings:      7
% 2.19/1.03  inst_num_of_non_proper_insts:           251
% 2.19/1.03  inst_num_of_duplicates:                 0
% 2.19/1.03  inst_inst_num_from_inst_to_res:         0
% 2.19/1.03  inst_dismatching_checking_time:         0.
% 2.19/1.03  
% 2.19/1.03  ------ Resolution
% 2.19/1.03  
% 2.19/1.03  res_num_of_clauses:                     0
% 2.19/1.03  res_num_in_passive:                     0
% 2.19/1.03  res_num_in_active:                      0
% 2.19/1.03  res_num_of_loops:                       101
% 2.19/1.03  res_forward_subset_subsumed:            23
% 2.19/1.03  res_backward_subset_subsumed:           0
% 2.19/1.03  res_forward_subsumed:                   1
% 2.19/1.03  res_backward_subsumed:                  0
% 2.19/1.03  res_forward_subsumption_resolution:     1
% 2.19/1.03  res_backward_subsumption_resolution:    0
% 2.19/1.03  res_clause_to_clause_subsumption:       382
% 2.19/1.03  res_orphan_elimination:                 0
% 2.19/1.03  res_tautology_del:                      18
% 2.19/1.03  res_num_eq_res_simplified:              0
% 2.19/1.03  res_num_sel_changes:                    0
% 2.19/1.03  res_moves_from_active_to_pass:          0
% 2.19/1.03  
% 2.19/1.03  ------ Superposition
% 2.19/1.03  
% 2.19/1.03  sup_time_total:                         0.
% 2.19/1.03  sup_time_generating:                    0.
% 2.19/1.03  sup_time_sim_full:                      0.
% 2.19/1.03  sup_time_sim_immed:                     0.
% 2.19/1.03  
% 2.19/1.03  sup_num_of_clauses:                     54
% 2.19/1.03  sup_num_in_active:                      34
% 2.19/1.03  sup_num_in_passive:                     20
% 2.19/1.03  sup_num_of_loops:                       35
% 2.19/1.03  sup_fw_superposition:                   21
% 2.19/1.03  sup_bw_superposition:                   39
% 2.19/1.03  sup_immediate_simplified:               20
% 2.19/1.03  sup_given_eliminated:                   0
% 2.19/1.03  comparisons_done:                       0
% 2.19/1.03  comparisons_avoided:                    3
% 2.19/1.03  
% 2.19/1.03  ------ Simplifications
% 2.19/1.03  
% 2.19/1.03  
% 2.19/1.03  sim_fw_subset_subsumed:                 13
% 2.19/1.03  sim_bw_subset_subsumed:                 0
% 2.19/1.03  sim_fw_subsumed:                        3
% 2.19/1.03  sim_bw_subsumed:                        0
% 2.19/1.03  sim_fw_subsumption_res:                 8
% 2.19/1.03  sim_bw_subsumption_res:                 0
% 2.19/1.03  sim_tautology_del:                      2
% 2.19/1.03  sim_eq_tautology_del:                   1
% 2.19/1.03  sim_eq_res_simp:                        0
% 2.19/1.03  sim_fw_demodulated:                     1
% 2.19/1.03  sim_bw_demodulated:                     1
% 2.19/1.03  sim_light_normalised:                   4
% 2.19/1.03  sim_joinable_taut:                      0
% 2.19/1.03  sim_joinable_simp:                      0
% 2.19/1.03  sim_ac_normalised:                      0
% 2.19/1.03  sim_smt_subsumption:                    0
% 2.19/1.03  
%------------------------------------------------------------------------------
