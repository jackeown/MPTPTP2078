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
% DateTime   : Thu Dec  3 12:12:45 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 630 expanded)
%              Number of clauses        :   73 ( 117 expanded)
%              Number of leaves         :   14 ( 241 expanded)
%              Depth                    :   30
%              Number of atoms          :  748 (5157 expanded)
%              Number of equality atoms :  139 (1313 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   20 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f29])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
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
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(cnf_transformation,[],[f33])).

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
              ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X2)
                 => ( k1_funct_1(X2,u1_struct_0(X0)) = X1
                   => k1_xboole_0 = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X2)
                   => ( k1_funct_1(X2,u1_struct_0(X0)) = X1
                     => k1_xboole_0 = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
          & k1_funct_1(X2,u1_struct_0(X0)) = X1
          & m2_orders_2(X3,X0,X2) )
     => ( k1_xboole_0 != k3_orders_2(X0,sK4,X1)
        & k1_funct_1(X2,u1_struct_0(X0)) = X1
        & m2_orders_2(sK4,X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f37,f36,f35,f34])).

fof(f56,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f53,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

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
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

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
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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
                  ( m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
                 => ! [X4] :
                      ( m2_orders_2(X4,X0,X3)
                     => ( ( k1_funct_1(X3,u1_struct_0(X0)) = X2
                          & r2_hidden(X1,X4) )
                       => r3_orders_2(X0,X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
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
    inference(equality_resolution,[],[f51])).

fof(f59,plain,(
    m2_orders_2(sK4,sK1,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(pure_predicate_removal,[],[f4])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_760,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
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
    inference(cnf_transformation,[],[f49])).

cnf(c_18,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_455,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_456,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_19,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_460,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_22,c_21,c_20,c_19])).

cnf(c_461,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_460])).

cnf(c_754,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_1200,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_754])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_18])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_22,c_21,c_20,c_19])).

cnf(c_756,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_763,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1295,plain,
    ( r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_756,c_763])).

cnf(c_1372,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_1295])).

cnf(c_1455,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
    | k3_orders_2(sK1,X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1200,c_1372])).

cnf(c_1456,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1455])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f48])).

cnf(c_8,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f62])).

cnf(c_15,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_245,plain,
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
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_246,plain,
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
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_16,negated_conjecture,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_250,plain,
    ( ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK4)
    | r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_246,c_22,c_21,c_20,c_19,c_18,c_16])).

cnf(c_251,plain,
    ( r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_250])).

cnf(c_277,plain,
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
    inference(resolution_lifted,[status(thm)],[c_7,c_251])).

cnf(c_278,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_282,plain,
    ( ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK4)
    | r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_278,c_22,c_21,c_18])).

cnf(c_283,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_282])).

cnf(c_306,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X3,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X3 != X1
    | k1_funct_1(sK3,u1_struct_0(sK1)) != X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_283])).

cnf(c_307,plain,
    ( ~ r2_orders_2(sK1,X0,k1_funct_1(sK3,u1_struct_0(sK1)))
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_311,plain,
    ( ~ r2_orders_2(sK1,X0,k1_funct_1(sK3,u1_struct_0(sK1)))
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_19,c_18])).

cnf(c_374,plain,
    ( ~ r2_hidden(X0,k3_orders_2(X1,X2,X3))
    | ~ r2_hidden(X4,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X4 != X0
    | k1_funct_1(sK3,u1_struct_0(sK1)) != X3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_311])).

cnf(c_375,plain,
    ( ~ r2_hidden(X0,k3_orders_2(sK1,X1,k1_funct_1(sK3,u1_struct_0(sK1))))
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_379,plain,
    ( ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,k1_funct_1(sK3,u1_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_375,c_22,c_21,c_20,c_19,c_18])).

cnf(c_380,plain,
    ( ~ r2_hidden(X0,k3_orders_2(sK1,X1,k1_funct_1(sK3,u1_struct_0(sK1))))
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_379])).

cnf(c_757,plain,
    ( r2_hidden(X0,k3_orders_2(sK1,X1,k1_funct_1(sK3,u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_380])).

cnf(c_14,negated_conjecture,
    ( k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_810,plain,
    ( r2_hidden(X0,k3_orders_2(sK1,X1,sK2)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_757,c_14])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_759,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_816,plain,
    ( r2_hidden(X0,k3_orders_2(sK1,X1,sK2)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_810,c_759])).

cnf(c_1201,plain,
    ( k3_orders_2(sK1,X0,sK2) = k1_xboole_0
    | r2_hidden(sK0(k3_orders_2(sK1,X0,sK2)),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(k3_orders_2(sK1,X0,sK2)),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_816])).

cnf(c_5,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_234,plain,
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
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_235,plain,
    ( ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_237,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_235,c_22,c_21,c_20,c_19,c_18,c_16])).

cnf(c_758,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_237])).

cnf(c_1294,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_758,c_763])).

cnf(c_1450,plain,
    ( k3_orders_2(sK1,X0,sK2) = k1_xboole_0
    | r2_hidden(sK0(k3_orders_2(sK1,X0,sK2)),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1201,c_1294])).

cnf(c_1469,plain,
    ( k3_orders_2(sK1,sK4,sK2) = k1_xboole_0
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_1450])).

cnf(c_23,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_24,plain,
    ( v3_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_25,plain,
    ( v4_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_26,plain,
    ( v5_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_27,plain,
    ( l1_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_29,plain,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_236,plain,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v3_orders_2(sK1) != iProver_top
    | v4_orders_2(sK1) != iProver_top
    | v5_orders_2(sK1) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_235])).

cnf(c_1813,plain,
    ( k3_orders_2(sK1,sK4,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1469,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_236])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1816,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1813,c_13])).

cnf(c_2078,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1816])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.09/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.09/0.99  
% 2.09/0.99  ------  iProver source info
% 2.09/0.99  
% 2.09/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.09/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.09/0.99  git: non_committed_changes: false
% 2.09/0.99  git: last_make_outside_of_git: false
% 2.09/0.99  
% 2.09/0.99  ------ 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options
% 2.09/0.99  
% 2.09/0.99  --out_options                           all
% 2.09/0.99  --tptp_safe_out                         true
% 2.09/0.99  --problem_path                          ""
% 2.09/0.99  --include_path                          ""
% 2.09/0.99  --clausifier                            res/vclausify_rel
% 2.09/0.99  --clausifier_options                    --mode clausify
% 2.09/0.99  --stdin                                 false
% 2.09/0.99  --stats_out                             all
% 2.09/0.99  
% 2.09/0.99  ------ General Options
% 2.09/0.99  
% 2.09/0.99  --fof                                   false
% 2.09/0.99  --time_out_real                         305.
% 2.09/0.99  --time_out_virtual                      -1.
% 2.09/0.99  --symbol_type_check                     false
% 2.09/0.99  --clausify_out                          false
% 2.09/0.99  --sig_cnt_out                           false
% 2.09/0.99  --trig_cnt_out                          false
% 2.09/0.99  --trig_cnt_out_tolerance                1.
% 2.09/0.99  --trig_cnt_out_sk_spl                   false
% 2.09/0.99  --abstr_cl_out                          false
% 2.09/0.99  
% 2.09/0.99  ------ Global Options
% 2.09/0.99  
% 2.09/0.99  --schedule                              default
% 2.09/0.99  --add_important_lit                     false
% 2.09/0.99  --prop_solver_per_cl                    1000
% 2.09/0.99  --min_unsat_core                        false
% 2.09/0.99  --soft_assumptions                      false
% 2.09/0.99  --soft_lemma_size                       3
% 2.09/0.99  --prop_impl_unit_size                   0
% 2.09/0.99  --prop_impl_unit                        []
% 2.09/0.99  --share_sel_clauses                     true
% 2.09/0.99  --reset_solvers                         false
% 2.09/0.99  --bc_imp_inh                            [conj_cone]
% 2.09/0.99  --conj_cone_tolerance                   3.
% 2.09/0.99  --extra_neg_conj                        none
% 2.09/0.99  --large_theory_mode                     true
% 2.09/0.99  --prolific_symb_bound                   200
% 2.09/0.99  --lt_threshold                          2000
% 2.09/0.99  --clause_weak_htbl                      true
% 2.09/0.99  --gc_record_bc_elim                     false
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing Options
% 2.09/0.99  
% 2.09/0.99  --preprocessing_flag                    true
% 2.09/0.99  --time_out_prep_mult                    0.1
% 2.09/0.99  --splitting_mode                        input
% 2.09/0.99  --splitting_grd                         true
% 2.09/0.99  --splitting_cvd                         false
% 2.09/0.99  --splitting_cvd_svl                     false
% 2.09/0.99  --splitting_nvd                         32
% 2.09/0.99  --sub_typing                            true
% 2.09/0.99  --prep_gs_sim                           true
% 2.09/0.99  --prep_unflatten                        true
% 2.09/0.99  --prep_res_sim                          true
% 2.09/0.99  --prep_upred                            true
% 2.09/0.99  --prep_sem_filter                       exhaustive
% 2.09/0.99  --prep_sem_filter_out                   false
% 2.09/0.99  --pred_elim                             true
% 2.09/0.99  --res_sim_input                         true
% 2.09/0.99  --eq_ax_congr_red                       true
% 2.09/0.99  --pure_diseq_elim                       true
% 2.09/0.99  --brand_transform                       false
% 2.09/0.99  --non_eq_to_eq                          false
% 2.09/0.99  --prep_def_merge                        true
% 2.09/0.99  --prep_def_merge_prop_impl              false
% 2.09/0.99  --prep_def_merge_mbd                    true
% 2.09/0.99  --prep_def_merge_tr_red                 false
% 2.09/0.99  --prep_def_merge_tr_cl                  false
% 2.09/0.99  --smt_preprocessing                     true
% 2.09/0.99  --smt_ac_axioms                         fast
% 2.09/0.99  --preprocessed_out                      false
% 2.09/0.99  --preprocessed_stats                    false
% 2.09/0.99  
% 2.09/0.99  ------ Abstraction refinement Options
% 2.09/0.99  
% 2.09/0.99  --abstr_ref                             []
% 2.09/0.99  --abstr_ref_prep                        false
% 2.09/0.99  --abstr_ref_until_sat                   false
% 2.09/0.99  --abstr_ref_sig_restrict                funpre
% 2.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/0.99  --abstr_ref_under                       []
% 2.09/0.99  
% 2.09/0.99  ------ SAT Options
% 2.09/0.99  
% 2.09/0.99  --sat_mode                              false
% 2.09/0.99  --sat_fm_restart_options                ""
% 2.09/0.99  --sat_gr_def                            false
% 2.09/0.99  --sat_epr_types                         true
% 2.09/0.99  --sat_non_cyclic_types                  false
% 2.09/0.99  --sat_finite_models                     false
% 2.09/0.99  --sat_fm_lemmas                         false
% 2.09/0.99  --sat_fm_prep                           false
% 2.09/0.99  --sat_fm_uc_incr                        true
% 2.09/0.99  --sat_out_model                         small
% 2.09/0.99  --sat_out_clauses                       false
% 2.09/0.99  
% 2.09/0.99  ------ QBF Options
% 2.09/0.99  
% 2.09/0.99  --qbf_mode                              false
% 2.09/0.99  --qbf_elim_univ                         false
% 2.09/0.99  --qbf_dom_inst                          none
% 2.09/0.99  --qbf_dom_pre_inst                      false
% 2.09/0.99  --qbf_sk_in                             false
% 2.09/0.99  --qbf_pred_elim                         true
% 2.09/0.99  --qbf_split                             512
% 2.09/0.99  
% 2.09/0.99  ------ BMC1 Options
% 2.09/0.99  
% 2.09/0.99  --bmc1_incremental                      false
% 2.09/0.99  --bmc1_axioms                           reachable_all
% 2.09/0.99  --bmc1_min_bound                        0
% 2.09/0.99  --bmc1_max_bound                        -1
% 2.09/0.99  --bmc1_max_bound_default                -1
% 2.09/0.99  --bmc1_symbol_reachability              true
% 2.09/0.99  --bmc1_property_lemmas                  false
% 2.09/0.99  --bmc1_k_induction                      false
% 2.09/0.99  --bmc1_non_equiv_states                 false
% 2.09/0.99  --bmc1_deadlock                         false
% 2.09/0.99  --bmc1_ucm                              false
% 2.09/0.99  --bmc1_add_unsat_core                   none
% 2.09/0.99  --bmc1_unsat_core_children              false
% 2.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/0.99  --bmc1_out_stat                         full
% 2.09/0.99  --bmc1_ground_init                      false
% 2.09/0.99  --bmc1_pre_inst_next_state              false
% 2.09/0.99  --bmc1_pre_inst_state                   false
% 2.09/0.99  --bmc1_pre_inst_reach_state             false
% 2.09/0.99  --bmc1_out_unsat_core                   false
% 2.09/0.99  --bmc1_aig_witness_out                  false
% 2.09/0.99  --bmc1_verbose                          false
% 2.09/0.99  --bmc1_dump_clauses_tptp                false
% 2.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.09/0.99  --bmc1_dump_file                        -
% 2.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.09/0.99  --bmc1_ucm_extend_mode                  1
% 2.09/0.99  --bmc1_ucm_init_mode                    2
% 2.09/0.99  --bmc1_ucm_cone_mode                    none
% 2.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.09/0.99  --bmc1_ucm_relax_model                  4
% 2.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/0.99  --bmc1_ucm_layered_model                none
% 2.09/0.99  --bmc1_ucm_max_lemma_size               10
% 2.09/0.99  
% 2.09/0.99  ------ AIG Options
% 2.09/0.99  
% 2.09/0.99  --aig_mode                              false
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation Options
% 2.09/0.99  
% 2.09/0.99  --instantiation_flag                    true
% 2.09/0.99  --inst_sos_flag                         false
% 2.09/0.99  --inst_sos_phase                        true
% 2.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel_side                     num_symb
% 2.09/0.99  --inst_solver_per_active                1400
% 2.09/0.99  --inst_solver_calls_frac                1.
% 2.09/0.99  --inst_passive_queue_type               priority_queues
% 2.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/0.99  --inst_passive_queues_freq              [25;2]
% 2.09/0.99  --inst_dismatching                      true
% 2.09/0.99  --inst_eager_unprocessed_to_passive     true
% 2.09/0.99  --inst_prop_sim_given                   true
% 2.09/0.99  --inst_prop_sim_new                     false
% 2.09/0.99  --inst_subs_new                         false
% 2.09/0.99  --inst_eq_res_simp                      false
% 2.09/0.99  --inst_subs_given                       false
% 2.09/0.99  --inst_orphan_elimination               true
% 2.09/0.99  --inst_learning_loop_flag               true
% 2.09/0.99  --inst_learning_start                   3000
% 2.09/0.99  --inst_learning_factor                  2
% 2.09/0.99  --inst_start_prop_sim_after_learn       3
% 2.09/0.99  --inst_sel_renew                        solver
% 2.09/0.99  --inst_lit_activity_flag                true
% 2.09/0.99  --inst_restr_to_given                   false
% 2.09/0.99  --inst_activity_threshold               500
% 2.09/0.99  --inst_out_proof                        true
% 2.09/0.99  
% 2.09/0.99  ------ Resolution Options
% 2.09/0.99  
% 2.09/0.99  --resolution_flag                       true
% 2.09/0.99  --res_lit_sel                           adaptive
% 2.09/0.99  --res_lit_sel_side                      none
% 2.09/0.99  --res_ordering                          kbo
% 2.09/0.99  --res_to_prop_solver                    active
% 2.09/0.99  --res_prop_simpl_new                    false
% 2.09/0.99  --res_prop_simpl_given                  true
% 2.09/0.99  --res_passive_queue_type                priority_queues
% 2.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/0.99  --res_passive_queues_freq               [15;5]
% 2.09/0.99  --res_forward_subs                      full
% 2.09/0.99  --res_backward_subs                     full
% 2.09/0.99  --res_forward_subs_resolution           true
% 2.09/0.99  --res_backward_subs_resolution          true
% 2.09/0.99  --res_orphan_elimination                true
% 2.09/0.99  --res_time_limit                        2.
% 2.09/0.99  --res_out_proof                         true
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Options
% 2.09/0.99  
% 2.09/0.99  --superposition_flag                    true
% 2.09/0.99  --sup_passive_queue_type                priority_queues
% 2.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.09/0.99  --demod_completeness_check              fast
% 2.09/0.99  --demod_use_ground                      true
% 2.09/0.99  --sup_to_prop_solver                    passive
% 2.09/0.99  --sup_prop_simpl_new                    true
% 2.09/0.99  --sup_prop_simpl_given                  true
% 2.09/0.99  --sup_fun_splitting                     false
% 2.09/0.99  --sup_smt_interval                      50000
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Simplification Setup
% 2.09/0.99  
% 2.09/0.99  --sup_indices_passive                   []
% 2.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_full_bw                           [BwDemod]
% 2.09/0.99  --sup_immed_triv                        [TrivRules]
% 2.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_immed_bw_main                     []
% 2.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  
% 2.09/0.99  ------ Combination Options
% 2.09/0.99  
% 2.09/0.99  --comb_res_mult                         3
% 2.09/0.99  --comb_sup_mult                         2
% 2.09/0.99  --comb_inst_mult                        10
% 2.09/0.99  
% 2.09/0.99  ------ Debug Options
% 2.09/0.99  
% 2.09/0.99  --dbg_backtrace                         false
% 2.09/0.99  --dbg_dump_prop_clauses                 false
% 2.09/0.99  --dbg_dump_prop_clauses_file            -
% 2.09/0.99  --dbg_out_stat                          false
% 2.09/0.99  ------ Parsing...
% 2.09/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.09/0.99  ------ Proving...
% 2.09/0.99  ------ Problem Properties 
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  clauses                                 12
% 2.09/0.99  conjectures                             3
% 2.09/0.99  EPR                                     0
% 2.09/0.99  Horn                                    11
% 2.09/0.99  unary                                   4
% 2.09/0.99  binary                                  1
% 2.09/0.99  lits                                    34
% 2.09/0.99  lits eq                                 7
% 2.09/0.99  fd_pure                                 0
% 2.09/0.99  fd_pseudo                               0
% 2.09/0.99  fd_cond                                 3
% 2.09/0.99  fd_pseudo_cond                          0
% 2.09/0.99  AC symbols                              0
% 2.09/0.99  
% 2.09/0.99  ------ Schedule dynamic 5 is on 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  ------ 
% 2.09/0.99  Current options:
% 2.09/0.99  ------ 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options
% 2.09/0.99  
% 2.09/0.99  --out_options                           all
% 2.09/0.99  --tptp_safe_out                         true
% 2.09/0.99  --problem_path                          ""
% 2.09/0.99  --include_path                          ""
% 2.09/0.99  --clausifier                            res/vclausify_rel
% 2.09/0.99  --clausifier_options                    --mode clausify
% 2.09/0.99  --stdin                                 false
% 2.09/0.99  --stats_out                             all
% 2.09/0.99  
% 2.09/0.99  ------ General Options
% 2.09/0.99  
% 2.09/0.99  --fof                                   false
% 2.09/0.99  --time_out_real                         305.
% 2.09/0.99  --time_out_virtual                      -1.
% 2.09/0.99  --symbol_type_check                     false
% 2.09/0.99  --clausify_out                          false
% 2.09/0.99  --sig_cnt_out                           false
% 2.09/0.99  --trig_cnt_out                          false
% 2.09/0.99  --trig_cnt_out_tolerance                1.
% 2.09/0.99  --trig_cnt_out_sk_spl                   false
% 2.09/0.99  --abstr_cl_out                          false
% 2.09/0.99  
% 2.09/0.99  ------ Global Options
% 2.09/0.99  
% 2.09/0.99  --schedule                              default
% 2.09/0.99  --add_important_lit                     false
% 2.09/0.99  --prop_solver_per_cl                    1000
% 2.09/0.99  --min_unsat_core                        false
% 2.09/0.99  --soft_assumptions                      false
% 2.09/0.99  --soft_lemma_size                       3
% 2.09/0.99  --prop_impl_unit_size                   0
% 2.09/0.99  --prop_impl_unit                        []
% 2.09/0.99  --share_sel_clauses                     true
% 2.09/0.99  --reset_solvers                         false
% 2.09/0.99  --bc_imp_inh                            [conj_cone]
% 2.09/0.99  --conj_cone_tolerance                   3.
% 2.09/0.99  --extra_neg_conj                        none
% 2.09/0.99  --large_theory_mode                     true
% 2.09/0.99  --prolific_symb_bound                   200
% 2.09/0.99  --lt_threshold                          2000
% 2.09/0.99  --clause_weak_htbl                      true
% 2.09/0.99  --gc_record_bc_elim                     false
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing Options
% 2.09/0.99  
% 2.09/0.99  --preprocessing_flag                    true
% 2.09/0.99  --time_out_prep_mult                    0.1
% 2.09/0.99  --splitting_mode                        input
% 2.09/0.99  --splitting_grd                         true
% 2.09/0.99  --splitting_cvd                         false
% 2.09/0.99  --splitting_cvd_svl                     false
% 2.09/0.99  --splitting_nvd                         32
% 2.09/0.99  --sub_typing                            true
% 2.09/0.99  --prep_gs_sim                           true
% 2.09/0.99  --prep_unflatten                        true
% 2.09/0.99  --prep_res_sim                          true
% 2.09/0.99  --prep_upred                            true
% 2.09/0.99  --prep_sem_filter                       exhaustive
% 2.09/0.99  --prep_sem_filter_out                   false
% 2.09/0.99  --pred_elim                             true
% 2.09/0.99  --res_sim_input                         true
% 2.09/0.99  --eq_ax_congr_red                       true
% 2.09/0.99  --pure_diseq_elim                       true
% 2.09/0.99  --brand_transform                       false
% 2.09/0.99  --non_eq_to_eq                          false
% 2.09/0.99  --prep_def_merge                        true
% 2.09/0.99  --prep_def_merge_prop_impl              false
% 2.09/0.99  --prep_def_merge_mbd                    true
% 2.09/0.99  --prep_def_merge_tr_red                 false
% 2.09/0.99  --prep_def_merge_tr_cl                  false
% 2.09/0.99  --smt_preprocessing                     true
% 2.09/0.99  --smt_ac_axioms                         fast
% 2.09/0.99  --preprocessed_out                      false
% 2.09/0.99  --preprocessed_stats                    false
% 2.09/0.99  
% 2.09/0.99  ------ Abstraction refinement Options
% 2.09/0.99  
% 2.09/0.99  --abstr_ref                             []
% 2.09/0.99  --abstr_ref_prep                        false
% 2.09/0.99  --abstr_ref_until_sat                   false
% 2.09/0.99  --abstr_ref_sig_restrict                funpre
% 2.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/0.99  --abstr_ref_under                       []
% 2.09/0.99  
% 2.09/0.99  ------ SAT Options
% 2.09/0.99  
% 2.09/0.99  --sat_mode                              false
% 2.09/0.99  --sat_fm_restart_options                ""
% 2.09/0.99  --sat_gr_def                            false
% 2.09/0.99  --sat_epr_types                         true
% 2.09/0.99  --sat_non_cyclic_types                  false
% 2.09/0.99  --sat_finite_models                     false
% 2.09/0.99  --sat_fm_lemmas                         false
% 2.09/0.99  --sat_fm_prep                           false
% 2.09/0.99  --sat_fm_uc_incr                        true
% 2.09/0.99  --sat_out_model                         small
% 2.09/0.99  --sat_out_clauses                       false
% 2.09/0.99  
% 2.09/0.99  ------ QBF Options
% 2.09/0.99  
% 2.09/0.99  --qbf_mode                              false
% 2.09/0.99  --qbf_elim_univ                         false
% 2.09/0.99  --qbf_dom_inst                          none
% 2.09/0.99  --qbf_dom_pre_inst                      false
% 2.09/0.99  --qbf_sk_in                             false
% 2.09/0.99  --qbf_pred_elim                         true
% 2.09/0.99  --qbf_split                             512
% 2.09/0.99  
% 2.09/0.99  ------ BMC1 Options
% 2.09/0.99  
% 2.09/0.99  --bmc1_incremental                      false
% 2.09/0.99  --bmc1_axioms                           reachable_all
% 2.09/0.99  --bmc1_min_bound                        0
% 2.09/0.99  --bmc1_max_bound                        -1
% 2.09/0.99  --bmc1_max_bound_default                -1
% 2.09/0.99  --bmc1_symbol_reachability              true
% 2.09/0.99  --bmc1_property_lemmas                  false
% 2.09/0.99  --bmc1_k_induction                      false
% 2.09/0.99  --bmc1_non_equiv_states                 false
% 2.09/0.99  --bmc1_deadlock                         false
% 2.09/0.99  --bmc1_ucm                              false
% 2.09/0.99  --bmc1_add_unsat_core                   none
% 2.09/0.99  --bmc1_unsat_core_children              false
% 2.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/0.99  --bmc1_out_stat                         full
% 2.09/0.99  --bmc1_ground_init                      false
% 2.09/0.99  --bmc1_pre_inst_next_state              false
% 2.09/0.99  --bmc1_pre_inst_state                   false
% 2.09/0.99  --bmc1_pre_inst_reach_state             false
% 2.09/0.99  --bmc1_out_unsat_core                   false
% 2.09/0.99  --bmc1_aig_witness_out                  false
% 2.09/0.99  --bmc1_verbose                          false
% 2.09/0.99  --bmc1_dump_clauses_tptp                false
% 2.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.09/0.99  --bmc1_dump_file                        -
% 2.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.09/0.99  --bmc1_ucm_extend_mode                  1
% 2.09/0.99  --bmc1_ucm_init_mode                    2
% 2.09/0.99  --bmc1_ucm_cone_mode                    none
% 2.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.09/0.99  --bmc1_ucm_relax_model                  4
% 2.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/0.99  --bmc1_ucm_layered_model                none
% 2.09/0.99  --bmc1_ucm_max_lemma_size               10
% 2.09/0.99  
% 2.09/0.99  ------ AIG Options
% 2.09/0.99  
% 2.09/0.99  --aig_mode                              false
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation Options
% 2.09/0.99  
% 2.09/0.99  --instantiation_flag                    true
% 2.09/0.99  --inst_sos_flag                         false
% 2.09/0.99  --inst_sos_phase                        true
% 2.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel_side                     none
% 2.09/0.99  --inst_solver_per_active                1400
% 2.09/0.99  --inst_solver_calls_frac                1.
% 2.09/0.99  --inst_passive_queue_type               priority_queues
% 2.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/0.99  --inst_passive_queues_freq              [25;2]
% 2.09/0.99  --inst_dismatching                      true
% 2.09/0.99  --inst_eager_unprocessed_to_passive     true
% 2.09/0.99  --inst_prop_sim_given                   true
% 2.09/0.99  --inst_prop_sim_new                     false
% 2.09/0.99  --inst_subs_new                         false
% 2.09/0.99  --inst_eq_res_simp                      false
% 2.09/0.99  --inst_subs_given                       false
% 2.09/0.99  --inst_orphan_elimination               true
% 2.09/0.99  --inst_learning_loop_flag               true
% 2.09/0.99  --inst_learning_start                   3000
% 2.09/0.99  --inst_learning_factor                  2
% 2.09/0.99  --inst_start_prop_sim_after_learn       3
% 2.09/0.99  --inst_sel_renew                        solver
% 2.09/0.99  --inst_lit_activity_flag                true
% 2.09/0.99  --inst_restr_to_given                   false
% 2.09/0.99  --inst_activity_threshold               500
% 2.09/0.99  --inst_out_proof                        true
% 2.09/0.99  
% 2.09/0.99  ------ Resolution Options
% 2.09/0.99  
% 2.09/0.99  --resolution_flag                       false
% 2.09/0.99  --res_lit_sel                           adaptive
% 2.09/0.99  --res_lit_sel_side                      none
% 2.09/0.99  --res_ordering                          kbo
% 2.09/0.99  --res_to_prop_solver                    active
% 2.09/0.99  --res_prop_simpl_new                    false
% 2.09/0.99  --res_prop_simpl_given                  true
% 2.09/0.99  --res_passive_queue_type                priority_queues
% 2.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/0.99  --res_passive_queues_freq               [15;5]
% 2.09/0.99  --res_forward_subs                      full
% 2.09/0.99  --res_backward_subs                     full
% 2.09/0.99  --res_forward_subs_resolution           true
% 2.09/0.99  --res_backward_subs_resolution          true
% 2.09/0.99  --res_orphan_elimination                true
% 2.09/0.99  --res_time_limit                        2.
% 2.09/0.99  --res_out_proof                         true
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Options
% 2.09/0.99  
% 2.09/0.99  --superposition_flag                    true
% 2.09/0.99  --sup_passive_queue_type                priority_queues
% 2.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.09/0.99  --demod_completeness_check              fast
% 2.09/0.99  --demod_use_ground                      true
% 2.09/0.99  --sup_to_prop_solver                    passive
% 2.09/0.99  --sup_prop_simpl_new                    true
% 2.09/0.99  --sup_prop_simpl_given                  true
% 2.09/0.99  --sup_fun_splitting                     false
% 2.09/0.99  --sup_smt_interval                      50000
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Simplification Setup
% 2.09/0.99  
% 2.09/0.99  --sup_indices_passive                   []
% 2.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_full_bw                           [BwDemod]
% 2.09/0.99  --sup_immed_triv                        [TrivRules]
% 2.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_immed_bw_main                     []
% 2.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  
% 2.09/0.99  ------ Combination Options
% 2.09/0.99  
% 2.09/0.99  --comb_res_mult                         3
% 2.09/0.99  --comb_sup_mult                         2
% 2.09/0.99  --comb_inst_mult                        10
% 2.09/0.99  
% 2.09/0.99  ------ Debug Options
% 2.09/0.99  
% 2.09/0.99  --dbg_backtrace                         false
% 2.09/0.99  --dbg_dump_prop_clauses                 false
% 2.09/0.99  --dbg_dump_prop_clauses_file            -
% 2.09/0.99  --dbg_out_stat                          false
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  ------ Proving...
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  % SZS status Theorem for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99   Resolution empty clause
% 2.09/0.99  
% 2.09/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  fof(f2,axiom,(
% 2.09/0.99    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f14,plain,(
% 2.09/0.99    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.09/0.99    inference(ennf_transformation,[],[f2])).
% 2.09/0.99  
% 2.09/0.99  fof(f29,plain,(
% 2.09/0.99    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f30,plain,(
% 2.09/0.99    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 2.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f29])).
% 2.09/0.99  
% 2.09/0.99  fof(f40,plain,(
% 2.09/0.99    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.09/0.99    inference(cnf_transformation,[],[f30])).
% 2.09/0.99  
% 2.09/0.99  fof(f7,axiom,(
% 2.09/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f23,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f7])).
% 2.09/0.99  
% 2.09/0.99  fof(f24,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f23])).
% 2.09/0.99  
% 2.09/0.99  fof(f32,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(nnf_transformation,[],[f24])).
% 2.09/0.99  
% 2.09/0.99  fof(f33,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f32])).
% 2.09/0.99  
% 2.09/0.99  fof(f49,plain,(
% 2.09/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f33])).
% 2.09/0.99  
% 2.09/0.99  fof(f9,conjecture,(
% 2.09/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f10,negated_conjecture,(
% 2.09/0.99    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 2.09/0.99    inference(negated_conjecture,[],[f9])).
% 2.09/0.99  
% 2.09/0.99  fof(f27,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1) & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f10])).
% 2.09/0.99  
% 2.09/0.99  fof(f28,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f37,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) => (k1_xboole_0 != k3_orders_2(X0,sK4,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(sK4,X0,X2))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f36,plain,(
% 2.09/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) => (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(sK3,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,sK3)) & m1_orders_1(sK3,k1_orders_1(u1_struct_0(X0))))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f35,plain,(
% 2.09/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,sK2) & k1_funct_1(X2,u1_struct_0(X0)) = sK2 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f34,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK1,X3,X1) & k1_funct_1(X2,u1_struct_0(sK1)) = X1 & m2_orders_2(X3,sK1,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f38,plain,(
% 2.09/0.99    (((k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) & k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 & m2_orders_2(sK4,sK1,sK3)) & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 2.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f37,f36,f35,f34])).
% 2.09/0.99  
% 2.09/0.99  fof(f56,plain,(
% 2.09/0.99    l1_orders_2(sK1)),
% 2.09/0.99    inference(cnf_transformation,[],[f38])).
% 2.09/0.99  
% 2.09/0.99  fof(f52,plain,(
% 2.09/0.99    ~v2_struct_0(sK1)),
% 2.09/0.99    inference(cnf_transformation,[],[f38])).
% 2.09/0.99  
% 2.09/0.99  fof(f53,plain,(
% 2.09/0.99    v3_orders_2(sK1)),
% 2.09/0.99    inference(cnf_transformation,[],[f38])).
% 2.09/0.99  
% 2.09/0.99  fof(f54,plain,(
% 2.09/0.99    v4_orders_2(sK1)),
% 2.09/0.99    inference(cnf_transformation,[],[f38])).
% 2.09/0.99  
% 2.09/0.99  fof(f55,plain,(
% 2.09/0.99    v5_orders_2(sK1)),
% 2.09/0.99    inference(cnf_transformation,[],[f38])).
% 2.09/0.99  
% 2.09/0.99  fof(f3,axiom,(
% 2.09/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f15,plain,(
% 2.09/0.99    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f3])).
% 2.09/0.99  
% 2.09/0.99  fof(f16,plain,(
% 2.09/0.99    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f15])).
% 2.09/0.99  
% 2.09/0.99  fof(f43,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f16])).
% 2.09/0.99  
% 2.09/0.99  fof(f1,axiom,(
% 2.09/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f12,plain,(
% 2.09/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.09/0.99    inference(ennf_transformation,[],[f1])).
% 2.09/0.99  
% 2.09/0.99  fof(f13,plain,(
% 2.09/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.09/0.99    inference(flattening,[],[f12])).
% 2.09/0.99  
% 2.09/0.99  fof(f39,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f13])).
% 2.09/0.99  
% 2.09/0.99  fof(f48,plain,(
% 2.09/0.99    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f33])).
% 2.09/0.99  
% 2.09/0.99  fof(f6,axiom,(
% 2.09/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(r2_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)))))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f21,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : ((~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f6])).
% 2.09/0.99  
% 2.09/0.99  fof(f22,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : (~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 2.09/0.99    inference(flattening,[],[f21])).
% 2.09/0.99  
% 2.09/0.99  fof(f47,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f22])).
% 2.09/0.99  
% 2.09/0.99  fof(f5,axiom,(
% 2.09/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f19,plain,(
% 2.09/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f5])).
% 2.09/0.99  
% 2.09/0.99  fof(f20,plain,(
% 2.09/0.99    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f19])).
% 2.09/0.99  
% 2.09/0.99  fof(f31,plain,(
% 2.09/0.99    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(nnf_transformation,[],[f20])).
% 2.09/0.99  
% 2.09/0.99  fof(f45,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f31])).
% 2.09/0.99  
% 2.09/0.99  fof(f8,axiom,(
% 2.09/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) => ! [X4] : (m2_orders_2(X4,X0,X3) => ((k1_funct_1(X3,u1_struct_0(X0)) = X2 & r2_hidden(X1,X4)) => r3_orders_2(X0,X2,X1)))))))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f25,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r3_orders_2(X0,X2,X1) | (k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4))) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f8])).
% 2.09/0.99  
% 2.09/0.99  fof(f26,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f25])).
% 2.09/0.99  
% 2.09/0.99  fof(f51,plain,(
% 2.09/0.99    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f26])).
% 2.09/0.99  
% 2.09/0.99  fof(f62,plain,(
% 2.09/0.99    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,k1_funct_1(X3,u1_struct_0(X0)),X1) | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(k1_funct_1(X3,u1_struct_0(X0)),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(equality_resolution,[],[f51])).
% 2.09/0.99  
% 2.09/0.99  fof(f59,plain,(
% 2.09/0.99    m2_orders_2(sK4,sK1,sK3)),
% 2.09/0.99    inference(cnf_transformation,[],[f38])).
% 2.09/0.99  
% 2.09/0.99  fof(f58,plain,(
% 2.09/0.99    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))),
% 2.09/0.99    inference(cnf_transformation,[],[f38])).
% 2.09/0.99  
% 2.09/0.99  fof(f60,plain,(
% 2.09/0.99    k1_funct_1(sK3,u1_struct_0(sK1)) = sK2),
% 2.09/0.99    inference(cnf_transformation,[],[f38])).
% 2.09/0.99  
% 2.09/0.99  fof(f57,plain,(
% 2.09/0.99    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.09/0.99    inference(cnf_transformation,[],[f38])).
% 2.09/0.99  
% 2.09/0.99  fof(f4,axiom,(
% 2.09/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f11,plain,(
% 2.09/0.99    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.09/0.99    inference(pure_predicate_removal,[],[f4])).
% 2.09/0.99  
% 2.09/0.99  fof(f17,plain,(
% 2.09/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f11])).
% 2.09/0.99  
% 2.09/0.99  fof(f18,plain,(
% 2.09/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f17])).
% 2.09/0.99  
% 2.09/0.99  fof(f44,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f18])).
% 2.09/0.99  
% 2.09/0.99  fof(f61,plain,(
% 2.09/0.99    k1_xboole_0 != k3_orders_2(sK1,sK4,sK2)),
% 2.09/0.99    inference(cnf_transformation,[],[f38])).
% 2.09/0.99  
% 2.09/0.99  cnf(c_3,plain,
% 2.09/0.99      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.09/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_760,plain,
% 2.09/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_10,plain,
% 2.09/0.99      ( r2_hidden(X0,X1)
% 2.09/0.99      | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
% 2.09/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.09/0.99      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 2.09/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.09/0.99      | v2_struct_0(X2)
% 2.09/0.99      | ~ v3_orders_2(X2)
% 2.09/0.99      | ~ v4_orders_2(X2)
% 2.09/0.99      | ~ v5_orders_2(X2)
% 2.09/0.99      | ~ l1_orders_2(X2) ),
% 2.09/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_18,negated_conjecture,
% 2.09/0.99      ( l1_orders_2(sK1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_455,plain,
% 2.09/0.99      ( r2_hidden(X0,X1)
% 2.09/0.99      | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
% 2.09/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.09/0.99      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 2.09/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.09/0.99      | v2_struct_0(X2)
% 2.09/0.99      | ~ v3_orders_2(X2)
% 2.09/0.99      | ~ v4_orders_2(X2)
% 2.09/0.99      | ~ v5_orders_2(X2)
% 2.09/0.99      | sK1 != X2 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_456,plain,
% 2.09/0.99      ( r2_hidden(X0,X1)
% 2.09/0.99      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
% 2.09/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.09/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.99      | v2_struct_0(sK1)
% 2.09/0.99      | ~ v3_orders_2(sK1)
% 2.09/0.99      | ~ v4_orders_2(sK1)
% 2.09/0.99      | ~ v5_orders_2(sK1) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_455]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_22,negated_conjecture,
% 2.09/0.99      ( ~ v2_struct_0(sK1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_21,negated_conjecture,
% 2.09/0.99      ( v3_orders_2(sK1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_20,negated_conjecture,
% 2.09/0.99      ( v4_orders_2(sK1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_19,negated_conjecture,
% 2.09/0.99      ( v5_orders_2(sK1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_460,plain,
% 2.09/0.99      ( r2_hidden(X0,X1)
% 2.09/0.99      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
% 2.09/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.09/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_456,c_22,c_21,c_20,c_19]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_461,plain,
% 2.09/0.99      ( r2_hidden(X0,X1)
% 2.09/0.99      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
% 2.09/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.09/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.09/0.99      inference(renaming,[status(thm)],[c_460]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_754,plain,
% 2.09/0.99      ( r2_hidden(X0,X1) = iProver_top
% 2.09/0.99      | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
% 2.09/0.99      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.09/0.99      | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
% 2.09/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1200,plain,
% 2.09/0.99      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 2.09/0.99      | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
% 2.09/0.99      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.09/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.09/0.99      | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_760,c_754]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_4,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.99      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | ~ v3_orders_2(X1)
% 2.09/0.99      | ~ v4_orders_2(X1)
% 2.09/0.99      | ~ v5_orders_2(X1)
% 2.09/0.99      | ~ l1_orders_2(X1) ),
% 2.09/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_408,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.99      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.99      | v2_struct_0(X1)
% 2.09/0.99      | ~ v3_orders_2(X1)
% 2.09/0.99      | ~ v4_orders_2(X1)
% 2.09/0.99      | ~ v5_orders_2(X1)
% 2.09/0.99      | sK1 != X1 ),
% 2.09/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_18]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_409,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.99      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.99      | v2_struct_0(sK1)
% 2.09/0.99      | ~ v3_orders_2(sK1)
% 2.09/0.99      | ~ v4_orders_2(sK1)
% 2.09/0.99      | ~ v5_orders_2(sK1) ),
% 2.09/0.99      inference(unflattening,[status(thm)],[c_408]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_413,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.99      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_409,c_22,c_21,c_20,c_19]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_756,plain,
% 2.09/1.00      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.09/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.09/1.00      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_0,plain,
% 2.09/1.00      ( ~ r2_hidden(X0,X1)
% 2.09/1.00      | m1_subset_1(X0,X2)
% 2.09/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.09/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_763,plain,
% 2.09/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.09/1.00      | m1_subset_1(X0,X2) = iProver_top
% 2.09/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1295,plain,
% 2.09/1.00      ( r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
% 2.09/1.00      | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
% 2.09/1.00      | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
% 2.09/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.09/1.00      inference(superposition,[status(thm)],[c_756,c_763]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1372,plain,
% 2.09/1.00      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 2.09/1.00      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.09/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.09/1.00      | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) = iProver_top ),
% 2.09/1.00      inference(superposition,[status(thm)],[c_760,c_1295]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1455,plain,
% 2.09/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.09/1.00      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.09/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
% 2.09/1.00      | k3_orders_2(sK1,X0,X1) = k1_xboole_0 ),
% 2.09/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1200,c_1372]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1456,plain,
% 2.09/1.00      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 2.09/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
% 2.09/1.00      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.09/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.09/1.00      inference(renaming,[status(thm)],[c_1455]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_11,plain,
% 2.09/1.00      ( r2_orders_2(X0,X1,X2)
% 2.09/1.00      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 2.09/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | ~ v3_orders_2(X0)
% 2.09/1.00      | ~ v4_orders_2(X0)
% 2.09/1.00      | ~ v5_orders_2(X0)
% 2.09/1.00      | ~ l1_orders_2(X0) ),
% 2.09/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_8,plain,
% 2.09/1.00      ( ~ r2_orders_2(X0,X1,X2)
% 2.09/1.00      | ~ r1_orders_2(X0,X2,X1)
% 2.09/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.09/1.00      | ~ v5_orders_2(X0)
% 2.09/1.00      | ~ l1_orders_2(X0) ),
% 2.09/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_7,plain,
% 2.09/1.00      ( r1_orders_2(X0,X1,X2)
% 2.09/1.00      | ~ r3_orders_2(X0,X1,X2)
% 2.09/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | ~ v3_orders_2(X0)
% 2.09/1.00      | ~ l1_orders_2(X0) ),
% 2.09/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_12,plain,
% 2.09/1.00      ( r3_orders_2(X0,k1_funct_1(X1,u1_struct_0(X0)),X2)
% 2.09/1.00      | ~ m2_orders_2(X3,X0,X1)
% 2.09/1.00      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 2.09/1.00      | ~ r2_hidden(X2,X3)
% 2.09/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(X0)),u1_struct_0(X0))
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | ~ v3_orders_2(X0)
% 2.09/1.00      | ~ v4_orders_2(X0)
% 2.09/1.00      | ~ v5_orders_2(X0)
% 2.09/1.00      | ~ l1_orders_2(X0) ),
% 2.09/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_15,negated_conjecture,
% 2.09/1.00      ( m2_orders_2(sK4,sK1,sK3) ),
% 2.09/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_245,plain,
% 2.09/1.00      ( r3_orders_2(X0,k1_funct_1(X1,u1_struct_0(X0)),X2)
% 2.09/1.00      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 2.09/1.00      | ~ r2_hidden(X2,X3)
% 2.09/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(X0)),u1_struct_0(X0))
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | ~ v3_orders_2(X0)
% 2.09/1.00      | ~ v4_orders_2(X0)
% 2.09/1.00      | ~ v5_orders_2(X0)
% 2.09/1.00      | ~ l1_orders_2(X0)
% 2.09/1.00      | sK3 != X1
% 2.09/1.00      | sK4 != X3
% 2.09/1.00      | sK1 != X0 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_246,plain,
% 2.09/1.00      ( r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
% 2.09/1.00      | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
% 2.09/1.00      | ~ r2_hidden(X0,sK4)
% 2.09/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.09/1.00      | v2_struct_0(sK1)
% 2.09/1.00      | ~ v3_orders_2(sK1)
% 2.09/1.00      | ~ v4_orders_2(sK1)
% 2.09/1.00      | ~ v5_orders_2(sK1)
% 2.09/1.00      | ~ l1_orders_2(sK1) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_245]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_16,negated_conjecture,
% 2.09/1.00      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) ),
% 2.09/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_250,plain,
% 2.09/1.00      ( ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/1.00      | ~ r2_hidden(X0,sK4)
% 2.09/1.00      | r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0) ),
% 2.09/1.00      inference(global_propositional_subsumption,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_246,c_22,c_21,c_20,c_19,c_18,c_16]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_251,plain,
% 2.09/1.00      ( r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
% 2.09/1.00      | ~ r2_hidden(X0,sK4)
% 2.09/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
% 2.09/1.00      inference(renaming,[status(thm)],[c_250]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_277,plain,
% 2.09/1.00      ( r1_orders_2(X0,X1,X2)
% 2.09/1.00      | ~ r2_hidden(X3,sK4)
% 2.09/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.09/1.00      | v2_struct_0(X0)
% 2.09/1.00      | ~ v3_orders_2(X0)
% 2.09/1.00      | ~ l1_orders_2(X0)
% 2.09/1.00      | X3 != X2
% 2.09/1.00      | k1_funct_1(sK3,u1_struct_0(sK1)) != X1
% 2.09/1.00      | sK1 != X0 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_251]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_278,plain,
% 2.09/1.00      ( r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
% 2.09/1.00      | ~ r2_hidden(X0,sK4)
% 2.09/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.09/1.00      | v2_struct_0(sK1)
% 2.09/1.00      | ~ v3_orders_2(sK1)
% 2.09/1.00      | ~ l1_orders_2(sK1) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_277]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_282,plain,
% 2.09/1.00      ( ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/1.00      | ~ r2_hidden(X0,sK4)
% 2.09/1.00      | r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0) ),
% 2.09/1.00      inference(global_propositional_subsumption,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_278,c_22,c_21,c_18]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_283,plain,
% 2.09/1.00      ( r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
% 2.09/1.00      | ~ r2_hidden(X0,sK4)
% 2.09/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
% 2.09/1.00      inference(renaming,[status(thm)],[c_282]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_306,plain,
% 2.09/1.00      ( ~ r2_orders_2(X0,X1,X2)
% 2.09/1.00      | ~ r2_hidden(X3,sK4)
% 2.09/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.09/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.09/1.00      | ~ v5_orders_2(X0)
% 2.09/1.00      | ~ l1_orders_2(X0)
% 2.09/1.00      | X3 != X1
% 2.09/1.00      | k1_funct_1(sK3,u1_struct_0(sK1)) != X2
% 2.09/1.00      | sK1 != X0 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_283]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_307,plain,
% 2.09/1.00      ( ~ r2_orders_2(sK1,X0,k1_funct_1(sK3,u1_struct_0(sK1)))
% 2.09/1.00      | ~ r2_hidden(X0,sK4)
% 2.09/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.09/1.00      | ~ v5_orders_2(sK1)
% 2.09/1.00      | ~ l1_orders_2(sK1) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_306]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_311,plain,
% 2.09/1.00      ( ~ r2_orders_2(sK1,X0,k1_funct_1(sK3,u1_struct_0(sK1)))
% 2.09/1.00      | ~ r2_hidden(X0,sK4)
% 2.09/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
% 2.09/1.00      inference(global_propositional_subsumption,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_307,c_19,c_18]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_374,plain,
% 2.09/1.00      ( ~ r2_hidden(X0,k3_orders_2(X1,X2,X3))
% 2.09/1.00      | ~ r2_hidden(X4,sK4)
% 2.09/1.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.09/1.00      | ~ m1_subset_1(X4,u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/1.00      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | ~ v3_orders_2(X1)
% 2.09/1.00      | ~ v4_orders_2(X1)
% 2.09/1.00      | ~ v5_orders_2(X1)
% 2.09/1.00      | ~ l1_orders_2(X1)
% 2.09/1.00      | X4 != X0
% 2.09/1.00      | k1_funct_1(sK3,u1_struct_0(sK1)) != X3
% 2.09/1.00      | sK1 != X1 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_311]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_375,plain,
% 2.09/1.00      ( ~ r2_hidden(X0,k3_orders_2(sK1,X1,k1_funct_1(sK3,u1_struct_0(sK1))))
% 2.09/1.00      | ~ r2_hidden(X0,sK4)
% 2.09/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/1.00      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.09/1.00      | v2_struct_0(sK1)
% 2.09/1.00      | ~ v3_orders_2(sK1)
% 2.09/1.00      | ~ v4_orders_2(sK1)
% 2.09/1.00      | ~ v5_orders_2(sK1)
% 2.09/1.00      | ~ l1_orders_2(sK1) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_374]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_379,plain,
% 2.09/1.00      ( ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/1.00      | ~ r2_hidden(X0,sK4)
% 2.09/1.00      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,k1_funct_1(sK3,u1_struct_0(sK1)))) ),
% 2.09/1.00      inference(global_propositional_subsumption,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_375,c_22,c_21,c_20,c_19,c_18]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_380,plain,
% 2.09/1.00      ( ~ r2_hidden(X0,k3_orders_2(sK1,X1,k1_funct_1(sK3,u1_struct_0(sK1))))
% 2.09/1.00      | ~ r2_hidden(X0,sK4)
% 2.09/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/1.00      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
% 2.09/1.00      inference(renaming,[status(thm)],[c_379]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_757,plain,
% 2.09/1.00      ( r2_hidden(X0,k3_orders_2(sK1,X1,k1_funct_1(sK3,u1_struct_0(sK1)))) != iProver_top
% 2.09/1.00      | r2_hidden(X0,sK4) != iProver_top
% 2.09/1.00      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.09/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.09/1.00      | m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) != iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_380]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_14,negated_conjecture,
% 2.09/1.00      ( k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 ),
% 2.09/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_810,plain,
% 2.09/1.00      ( r2_hidden(X0,k3_orders_2(sK1,X1,sK2)) != iProver_top
% 2.09/1.00      | r2_hidden(X0,sK4) != iProver_top
% 2.09/1.00      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.09/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.09/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.09/1.00      inference(light_normalisation,[status(thm)],[c_757,c_14]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_17,negated_conjecture,
% 2.09/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.09/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_759,plain,
% 2.09/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_816,plain,
% 2.09/1.00      ( r2_hidden(X0,k3_orders_2(sK1,X1,sK2)) != iProver_top
% 2.09/1.00      | r2_hidden(X0,sK4) != iProver_top
% 2.09/1.00      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.09/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.09/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_810,c_759]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1201,plain,
% 2.09/1.00      ( k3_orders_2(sK1,X0,sK2) = k1_xboole_0
% 2.09/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X0,sK2)),sK4) != iProver_top
% 2.09/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.09/1.00      | m1_subset_1(sK0(k3_orders_2(sK1,X0,sK2)),u1_struct_0(sK1)) != iProver_top ),
% 2.09/1.00      inference(superposition,[status(thm)],[c_760,c_816]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5,plain,
% 2.09/1.00      ( ~ m2_orders_2(X0,X1,X2)
% 2.09/1.00      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.09/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | ~ v3_orders_2(X1)
% 2.09/1.00      | ~ v4_orders_2(X1)
% 2.09/1.00      | ~ v5_orders_2(X1)
% 2.09/1.00      | ~ l1_orders_2(X1) ),
% 2.09/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_234,plain,
% 2.09/1.00      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
% 2.09/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | ~ v3_orders_2(X1)
% 2.09/1.00      | ~ v4_orders_2(X1)
% 2.09/1.00      | ~ v5_orders_2(X1)
% 2.09/1.00      | ~ l1_orders_2(X1)
% 2.09/1.00      | sK3 != X0
% 2.09/1.00      | sK4 != X2
% 2.09/1.00      | sK1 != X1 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_15]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_235,plain,
% 2.09/1.00      ( ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
% 2.09/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/1.00      | v2_struct_0(sK1)
% 2.09/1.00      | ~ v3_orders_2(sK1)
% 2.09/1.00      | ~ v4_orders_2(sK1)
% 2.09/1.00      | ~ v5_orders_2(sK1)
% 2.09/1.00      | ~ l1_orders_2(sK1) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_234]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_237,plain,
% 2.09/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.09/1.00      inference(global_propositional_subsumption,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_235,c_22,c_21,c_20,c_19,c_18,c_16]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_758,plain,
% 2.09/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_237]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1294,plain,
% 2.09/1.00      ( r2_hidden(X0,sK4) != iProver_top
% 2.09/1.00      | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top ),
% 2.09/1.00      inference(superposition,[status(thm)],[c_758,c_763]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1450,plain,
% 2.09/1.00      ( k3_orders_2(sK1,X0,sK2) = k1_xboole_0
% 2.09/1.00      | r2_hidden(sK0(k3_orders_2(sK1,X0,sK2)),sK4) != iProver_top
% 2.09/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.09/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1201,c_1294]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1469,plain,
% 2.09/1.00      ( k3_orders_2(sK1,sK4,sK2) = k1_xboole_0
% 2.09/1.00      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.09/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.09/1.00      inference(superposition,[status(thm)],[c_1456,c_1450]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_23,plain,
% 2.09/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_24,plain,
% 2.09/1.00      ( v3_orders_2(sK1) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_25,plain,
% 2.09/1.00      ( v4_orders_2(sK1) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_26,plain,
% 2.09/1.00      ( v5_orders_2(sK1) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_27,plain,
% 2.09/1.00      ( l1_orders_2(sK1) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_28,plain,
% 2.09/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_29,plain,
% 2.09/1.00      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_236,plain,
% 2.09/1.00      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) != iProver_top
% 2.09/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.09/1.00      | v2_struct_0(sK1) = iProver_top
% 2.09/1.00      | v3_orders_2(sK1) != iProver_top
% 2.09/1.00      | v4_orders_2(sK1) != iProver_top
% 2.09/1.00      | v5_orders_2(sK1) != iProver_top
% 2.09/1.00      | l1_orders_2(sK1) != iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_235]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1813,plain,
% 2.09/1.00      ( k3_orders_2(sK1,sK4,sK2) = k1_xboole_0 ),
% 2.09/1.00      inference(global_propositional_subsumption,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_1469,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_236]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_13,negated_conjecture,
% 2.09/1.00      ( k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) ),
% 2.09/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1816,plain,
% 2.09/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 2.09/1.00      inference(demodulation,[status(thm)],[c_1813,c_13]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2078,plain,
% 2.09/1.00      ( $false ),
% 2.09/1.00      inference(equality_resolution_simp,[status(thm)],[c_1816]) ).
% 2.09/1.00  
% 2.09/1.00  
% 2.09/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.09/1.00  
% 2.09/1.00  ------                               Statistics
% 2.09/1.00  
% 2.09/1.00  ------ General
% 2.09/1.00  
% 2.09/1.00  abstr_ref_over_cycles:                  0
% 2.09/1.00  abstr_ref_under_cycles:                 0
% 2.09/1.00  gc_basic_clause_elim:                   0
% 2.09/1.00  forced_gc_time:                         0
% 2.09/1.00  parsing_time:                           0.01
% 2.09/1.00  unif_index_cands_time:                  0.
% 2.09/1.00  unif_index_add_time:                    0.
% 2.09/1.00  orderings_time:                         0.
% 2.09/1.00  out_proof_time:                         0.009
% 2.09/1.00  total_time:                             0.126
% 2.09/1.00  num_of_symbols:                         55
% 2.09/1.00  num_of_terms:                           1875
% 2.09/1.00  
% 2.09/1.00  ------ Preprocessing
% 2.09/1.00  
% 2.09/1.00  num_of_splits:                          0
% 2.09/1.00  num_of_split_atoms:                     0
% 2.09/1.00  num_of_reused_defs:                     0
% 2.09/1.00  num_eq_ax_congr_red:                    23
% 2.09/1.00  num_of_sem_filtered_clauses:            1
% 2.09/1.00  num_of_subtypes:                        0
% 2.09/1.00  monotx_restored_types:                  0
% 2.09/1.00  sat_num_of_epr_types:                   0
% 2.09/1.00  sat_num_of_non_cyclic_types:            0
% 2.09/1.00  sat_guarded_non_collapsed_types:        0
% 2.09/1.00  num_pure_diseq_elim:                    0
% 2.09/1.00  simp_replaced_by:                       0
% 2.09/1.00  res_preprocessed:                       76
% 2.09/1.00  prep_upred:                             0
% 2.09/1.00  prep_unflattend:                        18
% 2.09/1.00  smt_new_axioms:                         0
% 2.09/1.00  pred_elim_cands:                        2
% 2.09/1.00  pred_elim:                              10
% 2.09/1.00  pred_elim_cl:                           11
% 2.09/1.00  pred_elim_cycles:                       12
% 2.09/1.00  merged_defs:                            0
% 2.09/1.00  merged_defs_ncl:                        0
% 2.09/1.00  bin_hyper_res:                          0
% 2.09/1.00  prep_cycles:                            4
% 2.09/1.00  pred_elim_time:                         0.008
% 2.09/1.00  splitting_time:                         0.
% 2.09/1.00  sem_filter_time:                        0.
% 2.09/1.00  monotx_time:                            0.
% 2.09/1.00  subtype_inf_time:                       0.
% 2.09/1.00  
% 2.09/1.00  ------ Problem properties
% 2.09/1.00  
% 2.09/1.00  clauses:                                12
% 2.09/1.00  conjectures:                            3
% 2.09/1.00  epr:                                    0
% 2.09/1.00  horn:                                   11
% 2.09/1.00  ground:                                 4
% 2.09/1.00  unary:                                  4
% 2.09/1.00  binary:                                 1
% 2.09/1.00  lits:                                   34
% 2.09/1.00  lits_eq:                                7
% 2.09/1.00  fd_pure:                                0
% 2.09/1.00  fd_pseudo:                              0
% 2.09/1.00  fd_cond:                                3
% 2.09/1.00  fd_pseudo_cond:                         0
% 2.09/1.00  ac_symbols:                             0
% 2.09/1.00  
% 2.09/1.00  ------ Propositional Solver
% 2.09/1.00  
% 2.09/1.00  prop_solver_calls:                      26
% 2.09/1.00  prop_fast_solver_calls:                 701
% 2.09/1.00  smt_solver_calls:                       0
% 2.09/1.00  smt_fast_solver_calls:                  0
% 2.09/1.00  prop_num_of_clauses:                    723
% 2.09/1.00  prop_preprocess_simplified:             2593
% 2.09/1.00  prop_fo_subsumed:                       38
% 2.09/1.00  prop_solver_time:                       0.
% 2.09/1.00  smt_solver_time:                        0.
% 2.09/1.00  smt_fast_solver_time:                   0.
% 2.09/1.00  prop_fast_solver_time:                  0.
% 2.09/1.00  prop_unsat_core_time:                   0.
% 2.09/1.00  
% 2.09/1.00  ------ QBF
% 2.09/1.00  
% 2.09/1.00  qbf_q_res:                              0
% 2.09/1.00  qbf_num_tautologies:                    0
% 2.09/1.00  qbf_prep_cycles:                        0
% 2.09/1.00  
% 2.09/1.00  ------ BMC1
% 2.09/1.00  
% 2.09/1.00  bmc1_current_bound:                     -1
% 2.09/1.00  bmc1_last_solved_bound:                 -1
% 2.09/1.00  bmc1_unsat_core_size:                   -1
% 2.09/1.00  bmc1_unsat_core_parents_size:           -1
% 2.09/1.00  bmc1_merge_next_fun:                    0
% 2.09/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.09/1.00  
% 2.09/1.00  ------ Instantiation
% 2.09/1.00  
% 2.09/1.00  inst_num_of_clauses:                    192
% 2.09/1.00  inst_num_in_passive:                    76
% 2.09/1.00  inst_num_in_active:                     100
% 2.09/1.00  inst_num_in_unprocessed:                16
% 2.09/1.00  inst_num_of_loops:                      110
% 2.09/1.00  inst_num_of_learning_restarts:          0
% 2.09/1.00  inst_num_moves_active_passive:          7
% 2.09/1.00  inst_lit_activity:                      0
% 2.09/1.00  inst_lit_activity_moves:                0
% 2.09/1.00  inst_num_tautologies:                   0
% 2.09/1.00  inst_num_prop_implied:                  0
% 2.09/1.00  inst_num_existing_simplified:           0
% 2.09/1.00  inst_num_eq_res_simplified:             0
% 2.09/1.00  inst_num_child_elim:                    0
% 2.09/1.00  inst_num_of_dismatching_blockings:      9
% 2.09/1.00  inst_num_of_non_proper_insts:           134
% 2.09/1.00  inst_num_of_duplicates:                 0
% 2.09/1.00  inst_inst_num_from_inst_to_res:         0
% 2.09/1.00  inst_dismatching_checking_time:         0.
% 2.09/1.00  
% 2.09/1.00  ------ Resolution
% 2.09/1.00  
% 2.09/1.00  res_num_of_clauses:                     0
% 2.09/1.00  res_num_in_passive:                     0
% 2.09/1.00  res_num_in_active:                      0
% 2.09/1.00  res_num_of_loops:                       80
% 2.09/1.00  res_forward_subset_subsumed:            12
% 2.09/1.00  res_backward_subset_subsumed:           0
% 2.09/1.00  res_forward_subsumed:                   0
% 2.09/1.00  res_backward_subsumed:                  0
% 2.09/1.00  res_forward_subsumption_resolution:     1
% 2.09/1.00  res_backward_subsumption_resolution:    0
% 2.09/1.00  res_clause_to_clause_subsumption:       194
% 2.09/1.00  res_orphan_elimination:                 0
% 2.09/1.00  res_tautology_del:                      16
% 2.09/1.00  res_num_eq_res_simplified:              0
% 2.09/1.00  res_num_sel_changes:                    0
% 2.09/1.00  res_moves_from_active_to_pass:          0
% 2.09/1.00  
% 2.09/1.00  ------ Superposition
% 2.09/1.00  
% 2.09/1.00  sup_time_total:                         0.
% 2.09/1.00  sup_time_generating:                    0.
% 2.09/1.00  sup_time_sim_full:                      0.
% 2.09/1.00  sup_time_sim_immed:                     0.
% 2.09/1.00  
% 2.09/1.00  sup_num_of_clauses:                     28
% 2.09/1.00  sup_num_in_active:                      19
% 2.09/1.00  sup_num_in_passive:                     9
% 2.09/1.00  sup_num_of_loops:                       20
% 2.09/1.00  sup_fw_superposition:                   3
% 2.09/1.00  sup_bw_superposition:                   28
% 2.09/1.00  sup_immediate_simplified:               18
% 2.09/1.00  sup_given_eliminated:                   0
% 2.09/1.00  comparisons_done:                       0
% 2.09/1.00  comparisons_avoided:                    0
% 2.09/1.00  
% 2.09/1.00  ------ Simplifications
% 2.09/1.00  
% 2.09/1.00  
% 2.09/1.00  sim_fw_subset_subsumed:                 3
% 2.09/1.00  sim_bw_subset_subsumed:                 0
% 2.09/1.00  sim_fw_subsumed:                        9
% 2.09/1.00  sim_bw_subsumed:                        1
% 2.09/1.00  sim_fw_subsumption_res:                 6
% 2.09/1.00  sim_bw_subsumption_res:                 1
% 2.09/1.00  sim_tautology_del:                      2
% 2.09/1.00  sim_eq_tautology_del:                   0
% 2.09/1.00  sim_eq_res_simp:                        0
% 2.09/1.00  sim_fw_demodulated:                     0
% 2.09/1.00  sim_bw_demodulated:                     1
% 2.09/1.00  sim_light_normalised:                   3
% 2.09/1.00  sim_joinable_taut:                      0
% 2.09/1.00  sim_joinable_simp:                      0
% 2.09/1.00  sim_ac_normalised:                      0
% 2.09/1.00  sim_smt_subsumption:                    0
% 2.09/1.00  
%------------------------------------------------------------------------------
