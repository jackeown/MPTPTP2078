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
% DateTime   : Thu Dec  3 12:12:05 EST 2020

% Result     : Theorem 7.17s
% Output     : CNFRefutation 7.17s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 658 expanded)
%              Number of clauses        :   89 ( 184 expanded)
%              Number of leaves         :   20 ( 141 expanded)
%              Depth                    :   24
%              Number of atoms          :  652 (3249 expanded)
%              Number of equality atoms :  172 ( 611 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
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

fof(f37,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f36])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X4,X3)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X6,X5)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f40])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X6,X5)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,X6,sK2(X0,X1,X2))
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
                & r2_hidden(sK1(X1,X2,X3),X2)
                & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,X6,sK2(X0,X1,X2))
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK2(X0,X1,X2) = X0
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f43,f42])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f31,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f45])).

fof(f76,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK1(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK1(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f72,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X1,X6,sK2(X0,X1,X2))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f78,plain,(
    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1567,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1561,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_28,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_604,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_605,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(sK3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_30,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_29,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_27,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_609,plain,
    ( ~ r2_hidden(X0,a_2_0_orders_2(sK3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_605,c_31,c_30,c_29,c_27])).

cnf(c_1558,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_18,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_13,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_413,plain,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_18,c_13])).

cnf(c_749,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_413,c_27])).

cnf(c_750,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_749])).

cnf(c_1644,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1558,c_750])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1569,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_20,plain,
    ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_670,plain,
    ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_671,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1))
    | r2_hidden(sK1(sK3,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_675,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1))
    | r2_hidden(sK1(sK3,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_671,c_31,c_30,c_29,c_27])).

cnf(c_1555,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) = iProver_top
    | r2_hidden(sK1(sK3,X1,X0),X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_1651,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) = iProver_top
    | r2_hidden(sK1(sK3,X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1555,c_750])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1564,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2195,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r1_tarski(X1,sK1(sK3,X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1651,c_1564])).

cnf(c_2460,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,k1_xboole_0)) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_2195])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1568,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_694,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_695,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_699,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_695,c_31,c_30,c_29,c_27])).

cnf(c_1554,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_1608,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1554,c_750])).

cnf(c_1966,plain,
    ( a_2_0_orders_2(sK3,k1_xboole_0) = k1_orders_2(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1568,c_1608])).

cnf(c_25,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_orders_2(X0,k1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_543,plain,
    ( v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_orders_2(X0,k1_struct_0(X0)) = u1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_28])).

cnf(c_544,plain,
    ( v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | k1_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_546,plain,
    ( k1_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_544,c_31,c_30,c_29,c_27])).

cnf(c_12,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_424,plain,
    ( ~ l1_orders_2(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_12])).

cnf(c_744,plain,
    ( k1_struct_0(X0) = k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_424,c_27])).

cnf(c_745,plain,
    ( k1_struct_0(sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_1582,plain,
    ( k1_orders_2(sK3,k1_xboole_0) = k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_546,c_745,c_750])).

cnf(c_1967,plain,
    ( a_2_0_orders_2(sK3,k1_xboole_0) = k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_1966,c_1582])).

cnf(c_2461,plain,
    ( r2_hidden(X0,k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2460,c_1967])).

cnf(c_3587,plain,
    ( r2_hidden(X0,k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2461,c_1568])).

cnf(c_3591,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1644,c_3587])).

cnf(c_22,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_551,plain,
    ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_552,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_556,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_552,c_31,c_30,c_29,c_27])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_572,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_556,c_7])).

cnf(c_1560,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_1669,plain,
    ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1560,c_750])).

cnf(c_15,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_754,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_755,plain,
    ( ~ r2_orders_2(sK3,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_754])).

cnf(c_1553,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_1603,plain,
    ( r2_orders_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1553,c_750])).

cnf(c_2094,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1669,c_1603])).

cnf(c_2508,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2094,c_1644])).

cnf(c_2509,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
    | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2508])).

cnf(c_3763,plain,
    ( r2_hidden(X0,a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3591,c_2509])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1570,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2604,plain,
    ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
    | r1_tarski(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1567,c_1608])).

cnf(c_2819,plain,
    ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1570,c_2604])).

cnf(c_3773,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3763,c_2819])).

cnf(c_22141,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1561,c_3773])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_93,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_99,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_107,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1057,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_1771,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_1772,plain,
    ( k1_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
    | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1771])).

cnf(c_22242,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22141,c_26,c_93,c_99,c_107,c_1772])).

cnf(c_22247,plain,
    ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1567,c_22242])).

cnf(c_22251,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_22247,c_1570])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:06:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.17/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.17/1.49  
% 7.17/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.17/1.49  
% 7.17/1.49  ------  iProver source info
% 7.17/1.49  
% 7.17/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.17/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.17/1.49  git: non_committed_changes: false
% 7.17/1.49  git: last_make_outside_of_git: false
% 7.17/1.49  
% 7.17/1.49  ------ 
% 7.17/1.49  
% 7.17/1.49  ------ Input Options
% 7.17/1.49  
% 7.17/1.49  --out_options                           all
% 7.17/1.49  --tptp_safe_out                         true
% 7.17/1.49  --problem_path                          ""
% 7.17/1.49  --include_path                          ""
% 7.17/1.49  --clausifier                            res/vclausify_rel
% 7.17/1.49  --clausifier_options                    --mode clausify
% 7.17/1.49  --stdin                                 false
% 7.17/1.49  --stats_out                             all
% 7.17/1.49  
% 7.17/1.49  ------ General Options
% 7.17/1.49  
% 7.17/1.49  --fof                                   false
% 7.17/1.49  --time_out_real                         305.
% 7.17/1.49  --time_out_virtual                      -1.
% 7.17/1.49  --symbol_type_check                     false
% 7.17/1.49  --clausify_out                          false
% 7.17/1.49  --sig_cnt_out                           false
% 7.17/1.49  --trig_cnt_out                          false
% 7.17/1.49  --trig_cnt_out_tolerance                1.
% 7.17/1.49  --trig_cnt_out_sk_spl                   false
% 7.17/1.49  --abstr_cl_out                          false
% 7.17/1.49  
% 7.17/1.49  ------ Global Options
% 7.17/1.49  
% 7.17/1.49  --schedule                              default
% 7.17/1.49  --add_important_lit                     false
% 7.17/1.49  --prop_solver_per_cl                    1000
% 7.17/1.49  --min_unsat_core                        false
% 7.17/1.49  --soft_assumptions                      false
% 7.17/1.49  --soft_lemma_size                       3
% 7.17/1.49  --prop_impl_unit_size                   0
% 7.17/1.49  --prop_impl_unit                        []
% 7.17/1.49  --share_sel_clauses                     true
% 7.17/1.49  --reset_solvers                         false
% 7.17/1.49  --bc_imp_inh                            [conj_cone]
% 7.17/1.49  --conj_cone_tolerance                   3.
% 7.17/1.49  --extra_neg_conj                        none
% 7.17/1.49  --large_theory_mode                     true
% 7.17/1.49  --prolific_symb_bound                   200
% 7.17/1.49  --lt_threshold                          2000
% 7.17/1.49  --clause_weak_htbl                      true
% 7.17/1.49  --gc_record_bc_elim                     false
% 7.17/1.49  
% 7.17/1.49  ------ Preprocessing Options
% 7.17/1.49  
% 7.17/1.49  --preprocessing_flag                    true
% 7.17/1.49  --time_out_prep_mult                    0.1
% 7.17/1.49  --splitting_mode                        input
% 7.17/1.49  --splitting_grd                         true
% 7.17/1.49  --splitting_cvd                         false
% 7.17/1.49  --splitting_cvd_svl                     false
% 7.17/1.49  --splitting_nvd                         32
% 7.17/1.49  --sub_typing                            true
% 7.17/1.49  --prep_gs_sim                           true
% 7.17/1.49  --prep_unflatten                        true
% 7.17/1.49  --prep_res_sim                          true
% 7.17/1.49  --prep_upred                            true
% 7.17/1.49  --prep_sem_filter                       exhaustive
% 7.17/1.49  --prep_sem_filter_out                   false
% 7.17/1.49  --pred_elim                             true
% 7.17/1.49  --res_sim_input                         true
% 7.17/1.49  --eq_ax_congr_red                       true
% 7.17/1.49  --pure_diseq_elim                       true
% 7.17/1.49  --brand_transform                       false
% 7.17/1.49  --non_eq_to_eq                          false
% 7.17/1.49  --prep_def_merge                        true
% 7.17/1.49  --prep_def_merge_prop_impl              false
% 7.17/1.49  --prep_def_merge_mbd                    true
% 7.17/1.49  --prep_def_merge_tr_red                 false
% 7.17/1.49  --prep_def_merge_tr_cl                  false
% 7.17/1.49  --smt_preprocessing                     true
% 7.17/1.49  --smt_ac_axioms                         fast
% 7.17/1.49  --preprocessed_out                      false
% 7.17/1.49  --preprocessed_stats                    false
% 7.17/1.49  
% 7.17/1.49  ------ Abstraction refinement Options
% 7.17/1.49  
% 7.17/1.49  --abstr_ref                             []
% 7.17/1.49  --abstr_ref_prep                        false
% 7.17/1.49  --abstr_ref_until_sat                   false
% 7.17/1.49  --abstr_ref_sig_restrict                funpre
% 7.17/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.17/1.49  --abstr_ref_under                       []
% 7.17/1.49  
% 7.17/1.49  ------ SAT Options
% 7.17/1.49  
% 7.17/1.49  --sat_mode                              false
% 7.17/1.49  --sat_fm_restart_options                ""
% 7.17/1.49  --sat_gr_def                            false
% 7.17/1.49  --sat_epr_types                         true
% 7.17/1.49  --sat_non_cyclic_types                  false
% 7.17/1.49  --sat_finite_models                     false
% 7.17/1.49  --sat_fm_lemmas                         false
% 7.17/1.49  --sat_fm_prep                           false
% 7.17/1.49  --sat_fm_uc_incr                        true
% 7.17/1.49  --sat_out_model                         small
% 7.17/1.49  --sat_out_clauses                       false
% 7.17/1.49  
% 7.17/1.49  ------ QBF Options
% 7.17/1.49  
% 7.17/1.49  --qbf_mode                              false
% 7.17/1.49  --qbf_elim_univ                         false
% 7.17/1.49  --qbf_dom_inst                          none
% 7.17/1.49  --qbf_dom_pre_inst                      false
% 7.17/1.49  --qbf_sk_in                             false
% 7.17/1.49  --qbf_pred_elim                         true
% 7.17/1.49  --qbf_split                             512
% 7.17/1.49  
% 7.17/1.49  ------ BMC1 Options
% 7.17/1.49  
% 7.17/1.49  --bmc1_incremental                      false
% 7.17/1.49  --bmc1_axioms                           reachable_all
% 7.17/1.49  --bmc1_min_bound                        0
% 7.17/1.49  --bmc1_max_bound                        -1
% 7.17/1.49  --bmc1_max_bound_default                -1
% 7.17/1.49  --bmc1_symbol_reachability              true
% 7.17/1.49  --bmc1_property_lemmas                  false
% 7.17/1.49  --bmc1_k_induction                      false
% 7.17/1.49  --bmc1_non_equiv_states                 false
% 7.17/1.49  --bmc1_deadlock                         false
% 7.17/1.49  --bmc1_ucm                              false
% 7.17/1.49  --bmc1_add_unsat_core                   none
% 7.17/1.49  --bmc1_unsat_core_children              false
% 7.17/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.17/1.49  --bmc1_out_stat                         full
% 7.17/1.49  --bmc1_ground_init                      false
% 7.17/1.49  --bmc1_pre_inst_next_state              false
% 7.17/1.49  --bmc1_pre_inst_state                   false
% 7.17/1.49  --bmc1_pre_inst_reach_state             false
% 7.17/1.49  --bmc1_out_unsat_core                   false
% 7.17/1.49  --bmc1_aig_witness_out                  false
% 7.17/1.49  --bmc1_verbose                          false
% 7.17/1.49  --bmc1_dump_clauses_tptp                false
% 7.17/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.17/1.49  --bmc1_dump_file                        -
% 7.17/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.17/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.17/1.49  --bmc1_ucm_extend_mode                  1
% 7.17/1.49  --bmc1_ucm_init_mode                    2
% 7.17/1.49  --bmc1_ucm_cone_mode                    none
% 7.17/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.17/1.49  --bmc1_ucm_relax_model                  4
% 7.17/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.17/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.17/1.49  --bmc1_ucm_layered_model                none
% 7.17/1.49  --bmc1_ucm_max_lemma_size               10
% 7.17/1.49  
% 7.17/1.49  ------ AIG Options
% 7.17/1.49  
% 7.17/1.49  --aig_mode                              false
% 7.17/1.49  
% 7.17/1.49  ------ Instantiation Options
% 7.17/1.49  
% 7.17/1.49  --instantiation_flag                    true
% 7.17/1.49  --inst_sos_flag                         false
% 7.17/1.49  --inst_sos_phase                        true
% 7.17/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.17/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.17/1.49  --inst_lit_sel_side                     num_symb
% 7.17/1.49  --inst_solver_per_active                1400
% 7.17/1.49  --inst_solver_calls_frac                1.
% 7.17/1.49  --inst_passive_queue_type               priority_queues
% 7.17/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.17/1.49  --inst_passive_queues_freq              [25;2]
% 7.17/1.49  --inst_dismatching                      true
% 7.17/1.49  --inst_eager_unprocessed_to_passive     true
% 7.17/1.49  --inst_prop_sim_given                   true
% 7.17/1.49  --inst_prop_sim_new                     false
% 7.17/1.49  --inst_subs_new                         false
% 7.17/1.49  --inst_eq_res_simp                      false
% 7.17/1.49  --inst_subs_given                       false
% 7.17/1.49  --inst_orphan_elimination               true
% 7.17/1.49  --inst_learning_loop_flag               true
% 7.17/1.49  --inst_learning_start                   3000
% 7.17/1.49  --inst_learning_factor                  2
% 7.17/1.49  --inst_start_prop_sim_after_learn       3
% 7.17/1.49  --inst_sel_renew                        solver
% 7.17/1.49  --inst_lit_activity_flag                true
% 7.17/1.49  --inst_restr_to_given                   false
% 7.17/1.49  --inst_activity_threshold               500
% 7.17/1.49  --inst_out_proof                        true
% 7.17/1.49  
% 7.17/1.49  ------ Resolution Options
% 7.17/1.49  
% 7.17/1.49  --resolution_flag                       true
% 7.17/1.49  --res_lit_sel                           adaptive
% 7.17/1.49  --res_lit_sel_side                      none
% 7.17/1.49  --res_ordering                          kbo
% 7.17/1.49  --res_to_prop_solver                    active
% 7.17/1.49  --res_prop_simpl_new                    false
% 7.17/1.49  --res_prop_simpl_given                  true
% 7.17/1.49  --res_passive_queue_type                priority_queues
% 7.17/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.17/1.49  --res_passive_queues_freq               [15;5]
% 7.17/1.49  --res_forward_subs                      full
% 7.17/1.49  --res_backward_subs                     full
% 7.17/1.49  --res_forward_subs_resolution           true
% 7.17/1.49  --res_backward_subs_resolution          true
% 7.17/1.49  --res_orphan_elimination                true
% 7.17/1.49  --res_time_limit                        2.
% 7.17/1.49  --res_out_proof                         true
% 7.17/1.49  
% 7.17/1.49  ------ Superposition Options
% 7.17/1.49  
% 7.17/1.49  --superposition_flag                    true
% 7.17/1.49  --sup_passive_queue_type                priority_queues
% 7.17/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.17/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.17/1.49  --demod_completeness_check              fast
% 7.17/1.49  --demod_use_ground                      true
% 7.17/1.49  --sup_to_prop_solver                    passive
% 7.17/1.49  --sup_prop_simpl_new                    true
% 7.17/1.49  --sup_prop_simpl_given                  true
% 7.17/1.49  --sup_fun_splitting                     false
% 7.17/1.49  --sup_smt_interval                      50000
% 7.17/1.49  
% 7.17/1.49  ------ Superposition Simplification Setup
% 7.17/1.49  
% 7.17/1.49  --sup_indices_passive                   []
% 7.17/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.17/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.17/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.17/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.17/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.17/1.49  --sup_full_bw                           [BwDemod]
% 7.17/1.49  --sup_immed_triv                        [TrivRules]
% 7.17/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.17/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.17/1.49  --sup_immed_bw_main                     []
% 7.17/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.17/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.17/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.17/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.17/1.49  
% 7.17/1.49  ------ Combination Options
% 7.17/1.49  
% 7.17/1.49  --comb_res_mult                         3
% 7.17/1.49  --comb_sup_mult                         2
% 7.17/1.49  --comb_inst_mult                        10
% 7.17/1.49  
% 7.17/1.49  ------ Debug Options
% 7.17/1.49  
% 7.17/1.49  --dbg_backtrace                         false
% 7.17/1.49  --dbg_dump_prop_clauses                 false
% 7.17/1.49  --dbg_dump_prop_clauses_file            -
% 7.17/1.49  --dbg_out_stat                          false
% 7.17/1.49  ------ Parsing...
% 7.17/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.17/1.49  
% 7.17/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 7.17/1.49  
% 7.17/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.17/1.49  
% 7.17/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.17/1.49  ------ Proving...
% 7.17/1.49  ------ Problem Properties 
% 7.17/1.49  
% 7.17/1.49  
% 7.17/1.49  clauses                                 23
% 7.17/1.49  conjectures                             1
% 7.17/1.49  EPR                                     4
% 7.17/1.49  Horn                                    20
% 7.17/1.49  unary                                   7
% 7.17/1.49  binary                                  6
% 7.17/1.49  lits                                    53
% 7.17/1.49  lits eq                                 12
% 7.17/1.49  fd_pure                                 0
% 7.17/1.49  fd_pseudo                               0
% 7.17/1.49  fd_cond                                 3
% 7.17/1.49  fd_pseudo_cond                          1
% 7.17/1.49  AC symbols                              0
% 7.17/1.49  
% 7.17/1.49  ------ Schedule dynamic 5 is on 
% 7.17/1.49  
% 7.17/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.17/1.49  
% 7.17/1.49  
% 7.17/1.49  ------ 
% 7.17/1.49  Current options:
% 7.17/1.49  ------ 
% 7.17/1.49  
% 7.17/1.49  ------ Input Options
% 7.17/1.49  
% 7.17/1.49  --out_options                           all
% 7.17/1.49  --tptp_safe_out                         true
% 7.17/1.49  --problem_path                          ""
% 7.17/1.49  --include_path                          ""
% 7.17/1.49  --clausifier                            res/vclausify_rel
% 7.17/1.49  --clausifier_options                    --mode clausify
% 7.17/1.49  --stdin                                 false
% 7.17/1.49  --stats_out                             all
% 7.17/1.49  
% 7.17/1.49  ------ General Options
% 7.17/1.49  
% 7.17/1.49  --fof                                   false
% 7.17/1.49  --time_out_real                         305.
% 7.17/1.49  --time_out_virtual                      -1.
% 7.17/1.49  --symbol_type_check                     false
% 7.17/1.49  --clausify_out                          false
% 7.17/1.49  --sig_cnt_out                           false
% 7.17/1.49  --trig_cnt_out                          false
% 7.17/1.49  --trig_cnt_out_tolerance                1.
% 7.17/1.49  --trig_cnt_out_sk_spl                   false
% 7.17/1.49  --abstr_cl_out                          false
% 7.17/1.49  
% 7.17/1.49  ------ Global Options
% 7.17/1.49  
% 7.17/1.49  --schedule                              default
% 7.17/1.49  --add_important_lit                     false
% 7.17/1.49  --prop_solver_per_cl                    1000
% 7.17/1.49  --min_unsat_core                        false
% 7.17/1.49  --soft_assumptions                      false
% 7.17/1.49  --soft_lemma_size                       3
% 7.17/1.49  --prop_impl_unit_size                   0
% 7.17/1.49  --prop_impl_unit                        []
% 7.17/1.49  --share_sel_clauses                     true
% 7.17/1.49  --reset_solvers                         false
% 7.17/1.49  --bc_imp_inh                            [conj_cone]
% 7.17/1.49  --conj_cone_tolerance                   3.
% 7.17/1.49  --extra_neg_conj                        none
% 7.17/1.49  --large_theory_mode                     true
% 7.17/1.49  --prolific_symb_bound                   200
% 7.17/1.49  --lt_threshold                          2000
% 7.17/1.49  --clause_weak_htbl                      true
% 7.17/1.49  --gc_record_bc_elim                     false
% 7.17/1.49  
% 7.17/1.49  ------ Preprocessing Options
% 7.17/1.49  
% 7.17/1.49  --preprocessing_flag                    true
% 7.17/1.49  --time_out_prep_mult                    0.1
% 7.17/1.49  --splitting_mode                        input
% 7.17/1.49  --splitting_grd                         true
% 7.17/1.49  --splitting_cvd                         false
% 7.17/1.49  --splitting_cvd_svl                     false
% 7.17/1.49  --splitting_nvd                         32
% 7.17/1.49  --sub_typing                            true
% 7.17/1.49  --prep_gs_sim                           true
% 7.17/1.49  --prep_unflatten                        true
% 7.17/1.49  --prep_res_sim                          true
% 7.17/1.49  --prep_upred                            true
% 7.17/1.49  --prep_sem_filter                       exhaustive
% 7.17/1.49  --prep_sem_filter_out                   false
% 7.17/1.49  --pred_elim                             true
% 7.17/1.49  --res_sim_input                         true
% 7.17/1.49  --eq_ax_congr_red                       true
% 7.17/1.49  --pure_diseq_elim                       true
% 7.17/1.49  --brand_transform                       false
% 7.17/1.49  --non_eq_to_eq                          false
% 7.17/1.49  --prep_def_merge                        true
% 7.17/1.49  --prep_def_merge_prop_impl              false
% 7.17/1.49  --prep_def_merge_mbd                    true
% 7.17/1.49  --prep_def_merge_tr_red                 false
% 7.17/1.49  --prep_def_merge_tr_cl                  false
% 7.17/1.49  --smt_preprocessing                     true
% 7.17/1.49  --smt_ac_axioms                         fast
% 7.17/1.49  --preprocessed_out                      false
% 7.17/1.49  --preprocessed_stats                    false
% 7.17/1.49  
% 7.17/1.49  ------ Abstraction refinement Options
% 7.17/1.49  
% 7.17/1.49  --abstr_ref                             []
% 7.17/1.49  --abstr_ref_prep                        false
% 7.17/1.49  --abstr_ref_until_sat                   false
% 7.17/1.49  --abstr_ref_sig_restrict                funpre
% 7.17/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.17/1.49  --abstr_ref_under                       []
% 7.17/1.49  
% 7.17/1.49  ------ SAT Options
% 7.17/1.49  
% 7.17/1.49  --sat_mode                              false
% 7.17/1.49  --sat_fm_restart_options                ""
% 7.17/1.49  --sat_gr_def                            false
% 7.17/1.49  --sat_epr_types                         true
% 7.17/1.49  --sat_non_cyclic_types                  false
% 7.17/1.49  --sat_finite_models                     false
% 7.17/1.49  --sat_fm_lemmas                         false
% 7.17/1.49  --sat_fm_prep                           false
% 7.17/1.49  --sat_fm_uc_incr                        true
% 7.17/1.49  --sat_out_model                         small
% 7.17/1.49  --sat_out_clauses                       false
% 7.17/1.49  
% 7.17/1.49  ------ QBF Options
% 7.17/1.49  
% 7.17/1.49  --qbf_mode                              false
% 7.17/1.49  --qbf_elim_univ                         false
% 7.17/1.49  --qbf_dom_inst                          none
% 7.17/1.49  --qbf_dom_pre_inst                      false
% 7.17/1.49  --qbf_sk_in                             false
% 7.17/1.49  --qbf_pred_elim                         true
% 7.17/1.49  --qbf_split                             512
% 7.17/1.49  
% 7.17/1.49  ------ BMC1 Options
% 7.17/1.49  
% 7.17/1.49  --bmc1_incremental                      false
% 7.17/1.49  --bmc1_axioms                           reachable_all
% 7.17/1.49  --bmc1_min_bound                        0
% 7.17/1.49  --bmc1_max_bound                        -1
% 7.17/1.49  --bmc1_max_bound_default                -1
% 7.17/1.49  --bmc1_symbol_reachability              true
% 7.17/1.49  --bmc1_property_lemmas                  false
% 7.17/1.49  --bmc1_k_induction                      false
% 7.17/1.49  --bmc1_non_equiv_states                 false
% 7.17/1.49  --bmc1_deadlock                         false
% 7.17/1.49  --bmc1_ucm                              false
% 7.17/1.49  --bmc1_add_unsat_core                   none
% 7.17/1.49  --bmc1_unsat_core_children              false
% 7.17/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.17/1.49  --bmc1_out_stat                         full
% 7.17/1.49  --bmc1_ground_init                      false
% 7.17/1.49  --bmc1_pre_inst_next_state              false
% 7.17/1.49  --bmc1_pre_inst_state                   false
% 7.17/1.49  --bmc1_pre_inst_reach_state             false
% 7.17/1.49  --bmc1_out_unsat_core                   false
% 7.17/1.49  --bmc1_aig_witness_out                  false
% 7.17/1.49  --bmc1_verbose                          false
% 7.17/1.49  --bmc1_dump_clauses_tptp                false
% 7.17/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.17/1.49  --bmc1_dump_file                        -
% 7.17/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.17/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.17/1.49  --bmc1_ucm_extend_mode                  1
% 7.17/1.49  --bmc1_ucm_init_mode                    2
% 7.17/1.49  --bmc1_ucm_cone_mode                    none
% 7.17/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.17/1.49  --bmc1_ucm_relax_model                  4
% 7.17/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.17/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.17/1.49  --bmc1_ucm_layered_model                none
% 7.17/1.49  --bmc1_ucm_max_lemma_size               10
% 7.17/1.49  
% 7.17/1.49  ------ AIG Options
% 7.17/1.49  
% 7.17/1.49  --aig_mode                              false
% 7.17/1.49  
% 7.17/1.49  ------ Instantiation Options
% 7.17/1.49  
% 7.17/1.49  --instantiation_flag                    true
% 7.17/1.49  --inst_sos_flag                         false
% 7.17/1.49  --inst_sos_phase                        true
% 7.17/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.17/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.17/1.49  --inst_lit_sel_side                     none
% 7.17/1.49  --inst_solver_per_active                1400
% 7.17/1.49  --inst_solver_calls_frac                1.
% 7.17/1.49  --inst_passive_queue_type               priority_queues
% 7.17/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.17/1.49  --inst_passive_queues_freq              [25;2]
% 7.17/1.49  --inst_dismatching                      true
% 7.17/1.49  --inst_eager_unprocessed_to_passive     true
% 7.17/1.49  --inst_prop_sim_given                   true
% 7.17/1.49  --inst_prop_sim_new                     false
% 7.17/1.49  --inst_subs_new                         false
% 7.17/1.49  --inst_eq_res_simp                      false
% 7.17/1.49  --inst_subs_given                       false
% 7.17/1.49  --inst_orphan_elimination               true
% 7.17/1.49  --inst_learning_loop_flag               true
% 7.17/1.49  --inst_learning_start                   3000
% 7.17/1.49  --inst_learning_factor                  2
% 7.17/1.49  --inst_start_prop_sim_after_learn       3
% 7.17/1.49  --inst_sel_renew                        solver
% 7.17/1.49  --inst_lit_activity_flag                true
% 7.17/1.49  --inst_restr_to_given                   false
% 7.17/1.49  --inst_activity_threshold               500
% 7.17/1.49  --inst_out_proof                        true
% 7.17/1.49  
% 7.17/1.49  ------ Resolution Options
% 7.17/1.49  
% 7.17/1.49  --resolution_flag                       false
% 7.17/1.49  --res_lit_sel                           adaptive
% 7.17/1.49  --res_lit_sel_side                      none
% 7.17/1.49  --res_ordering                          kbo
% 7.17/1.49  --res_to_prop_solver                    active
% 7.17/1.49  --res_prop_simpl_new                    false
% 7.17/1.49  --res_prop_simpl_given                  true
% 7.17/1.49  --res_passive_queue_type                priority_queues
% 7.17/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.17/1.49  --res_passive_queues_freq               [15;5]
% 7.17/1.49  --res_forward_subs                      full
% 7.17/1.49  --res_backward_subs                     full
% 7.17/1.49  --res_forward_subs_resolution           true
% 7.17/1.49  --res_backward_subs_resolution          true
% 7.17/1.49  --res_orphan_elimination                true
% 7.17/1.49  --res_time_limit                        2.
% 7.17/1.49  --res_out_proof                         true
% 7.17/1.49  
% 7.17/1.49  ------ Superposition Options
% 7.17/1.49  
% 7.17/1.49  --superposition_flag                    true
% 7.17/1.49  --sup_passive_queue_type                priority_queues
% 7.17/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.17/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.17/1.49  --demod_completeness_check              fast
% 7.17/1.49  --demod_use_ground                      true
% 7.17/1.49  --sup_to_prop_solver                    passive
% 7.17/1.49  --sup_prop_simpl_new                    true
% 7.17/1.49  --sup_prop_simpl_given                  true
% 7.17/1.49  --sup_fun_splitting                     false
% 7.17/1.49  --sup_smt_interval                      50000
% 7.17/1.49  
% 7.17/1.49  ------ Superposition Simplification Setup
% 7.17/1.49  
% 7.17/1.49  --sup_indices_passive                   []
% 7.17/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.17/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.17/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.17/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.17/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.17/1.49  --sup_full_bw                           [BwDemod]
% 7.17/1.49  --sup_immed_triv                        [TrivRules]
% 7.17/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.17/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.17/1.49  --sup_immed_bw_main                     []
% 7.17/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.17/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.17/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.17/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.17/1.49  
% 7.17/1.49  ------ Combination Options
% 7.17/1.49  
% 7.17/1.49  --comb_res_mult                         3
% 7.17/1.49  --comb_sup_mult                         2
% 7.17/1.49  --comb_inst_mult                        10
% 7.17/1.49  
% 7.17/1.49  ------ Debug Options
% 7.17/1.49  
% 7.17/1.49  --dbg_backtrace                         false
% 7.17/1.49  --dbg_dump_prop_clauses                 false
% 7.17/1.49  --dbg_dump_prop_clauses_file            -
% 7.17/1.49  --dbg_out_stat                          false
% 7.17/1.49  
% 7.17/1.49  
% 7.17/1.49  
% 7.17/1.49  
% 7.17/1.49  ------ Proving...
% 7.17/1.49  
% 7.17/1.49  
% 7.17/1.49  % SZS status Theorem for theBenchmark.p
% 7.17/1.49  
% 7.17/1.49   Resolution empty clause
% 7.17/1.49  
% 7.17/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.17/1.49  
% 7.17/1.49  fof(f4,axiom,(
% 7.17/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.17/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.49  
% 7.17/1.49  fof(f35,plain,(
% 7.17/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.17/1.49    inference(nnf_transformation,[],[f4])).
% 7.17/1.49  
% 7.17/1.49  fof(f53,plain,(
% 7.17/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.17/1.49    inference(cnf_transformation,[],[f35])).
% 7.17/1.49  
% 7.17/1.49  fof(f7,axiom,(
% 7.17/1.49    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 7.17/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.49  
% 7.17/1.49  fof(f20,plain,(
% 7.17/1.49    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 7.17/1.49    inference(ennf_transformation,[],[f7])).
% 7.17/1.49  
% 7.17/1.49  fof(f36,plain,(
% 7.17/1.49    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 7.17/1.49    introduced(choice_axiom,[])).
% 7.17/1.49  
% 7.17/1.49  fof(f37,plain,(
% 7.17/1.49    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 7.17/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f36])).
% 7.17/1.49  
% 7.17/1.49  fof(f56,plain,(
% 7.17/1.49    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 7.17/1.49    inference(cnf_transformation,[],[f37])).
% 7.17/1.49  
% 7.17/1.49  fof(f13,axiom,(
% 7.17/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 7.17/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.49  
% 7.17/1.49  fof(f27,plain,(
% 7.17/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 7.17/1.49    inference(ennf_transformation,[],[f13])).
% 7.17/1.49  
% 7.17/1.49  fof(f28,plain,(
% 7.17/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.17/1.49    inference(flattening,[],[f27])).
% 7.17/1.49  
% 7.17/1.49  fof(f40,plain,(
% 7.17/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.17/1.49    inference(nnf_transformation,[],[f28])).
% 7.17/1.49  
% 7.17/1.49  fof(f41,plain,(
% 7.17/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.17/1.49    inference(rectify,[],[f40])).
% 7.17/1.49  
% 7.17/1.49  fof(f43,plain,(
% 7.17/1.49    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 7.17/1.49    introduced(choice_axiom,[])).
% 7.17/1.49  
% 7.17/1.49  fof(f42,plain,(
% 7.17/1.49    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 7.17/1.49    introduced(choice_axiom,[])).
% 7.17/1.49  
% 7.17/1.49  fof(f44,plain,(
% 7.17/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.17/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f43,f42])).
% 7.17/1.49  
% 7.17/1.49  fof(f66,plain,(
% 7.17/1.49    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 7.17/1.49    inference(cnf_transformation,[],[f44])).
% 7.17/1.49  
% 7.17/1.49  fof(f15,conjecture,(
% 7.17/1.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 7.17/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.49  
% 7.17/1.49  fof(f16,negated_conjecture,(
% 7.17/1.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 7.17/1.49    inference(negated_conjecture,[],[f15])).
% 7.17/1.49  
% 7.17/1.49  fof(f31,plain,(
% 7.17/1.49    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 7.17/1.49    inference(ennf_transformation,[],[f16])).
% 7.17/1.49  
% 7.17/1.49  fof(f32,plain,(
% 7.17/1.49    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 7.17/1.49    inference(flattening,[],[f31])).
% 7.17/1.49  
% 7.17/1.49  fof(f45,plain,(
% 7.17/1.49    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 7.17/1.49    introduced(choice_axiom,[])).
% 7.17/1.49  
% 7.17/1.49  fof(f46,plain,(
% 7.17/1.49    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 7.17/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f45])).
% 7.17/1.49  
% 7.17/1.49  fof(f76,plain,(
% 7.17/1.49    v5_orders_2(sK3)),
% 7.17/1.49    inference(cnf_transformation,[],[f46])).
% 7.17/1.49  
% 7.17/1.49  fof(f73,plain,(
% 7.17/1.49    ~v2_struct_0(sK3)),
% 7.17/1.49    inference(cnf_transformation,[],[f46])).
% 7.17/1.49  
% 7.17/1.49  fof(f74,plain,(
% 7.17/1.49    v3_orders_2(sK3)),
% 7.17/1.49    inference(cnf_transformation,[],[f46])).
% 7.17/1.49  
% 7.17/1.49  fof(f75,plain,(
% 7.17/1.49    v4_orders_2(sK3)),
% 7.17/1.49    inference(cnf_transformation,[],[f46])).
% 7.17/1.49  
% 7.17/1.49  fof(f77,plain,(
% 7.17/1.49    l1_orders_2(sK3)),
% 7.17/1.49    inference(cnf_transformation,[],[f46])).
% 7.17/1.49  
% 7.17/1.49  fof(f12,axiom,(
% 7.17/1.49    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 7.17/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.49  
% 7.17/1.49  fof(f26,plain,(
% 7.17/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 7.17/1.49    inference(ennf_transformation,[],[f12])).
% 7.17/1.49  
% 7.17/1.49  fof(f65,plain,(
% 7.17/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 7.17/1.49    inference(cnf_transformation,[],[f26])).
% 7.17/1.49  
% 7.17/1.49  fof(f9,axiom,(
% 7.17/1.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.17/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.49  
% 7.17/1.49  fof(f22,plain,(
% 7.17/1.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.17/1.49    inference(ennf_transformation,[],[f9])).
% 7.17/1.49  
% 7.17/1.49  fof(f60,plain,(
% 7.17/1.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.17/1.49    inference(cnf_transformation,[],[f22])).
% 7.17/1.49  
% 7.17/1.49  fof(f2,axiom,(
% 7.17/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.17/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.49  
% 7.17/1.49  fof(f50,plain,(
% 7.17/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.17/1.49    inference(cnf_transformation,[],[f2])).
% 7.17/1.49  
% 7.17/1.49  fof(f70,plain,(
% 7.17/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 7.17/1.49    inference(cnf_transformation,[],[f44])).
% 7.17/1.49  
% 7.17/1.49  fof(f83,plain,(
% 7.17/1.49    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_0_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 7.17/1.49    inference(equality_resolution,[],[f70])).
% 7.17/1.49  
% 7.17/1.49  fof(f6,axiom,(
% 7.17/1.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.17/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.49  
% 7.17/1.49  fof(f19,plain,(
% 7.17/1.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.17/1.49    inference(ennf_transformation,[],[f6])).
% 7.17/1.49  
% 7.17/1.49  fof(f55,plain,(
% 7.17/1.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.17/1.49    inference(cnf_transformation,[],[f19])).
% 7.17/1.49  
% 7.17/1.49  fof(f3,axiom,(
% 7.17/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.17/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.49  
% 7.17/1.49  fof(f51,plain,(
% 7.17/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.17/1.49    inference(cnf_transformation,[],[f3])).
% 7.17/1.49  
% 7.17/1.49  fof(f11,axiom,(
% 7.17/1.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 7.17/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.49  
% 7.17/1.49  fof(f24,plain,(
% 7.17/1.49    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 7.17/1.49    inference(ennf_transformation,[],[f11])).
% 7.17/1.49  
% 7.17/1.49  fof(f25,plain,(
% 7.17/1.49    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.17/1.49    inference(flattening,[],[f24])).
% 7.17/1.49  
% 7.17/1.49  fof(f64,plain,(
% 7.17/1.49    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.17/1.49    inference(cnf_transformation,[],[f25])).
% 7.17/1.49  
% 7.17/1.49  fof(f14,axiom,(
% 7.17/1.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)))),
% 7.17/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.49  
% 7.17/1.49  fof(f29,plain,(
% 7.17/1.49    ! [X0] : (u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 7.17/1.49    inference(ennf_transformation,[],[f14])).
% 7.17/1.49  
% 7.17/1.49  fof(f30,plain,(
% 7.17/1.49    ! [X0] : (u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.17/1.49    inference(flattening,[],[f29])).
% 7.17/1.49  
% 7.17/1.49  fof(f72,plain,(
% 7.17/1.49    ( ! [X0] : (u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.17/1.49    inference(cnf_transformation,[],[f30])).
% 7.17/1.49  
% 7.17/1.49  fof(f8,axiom,(
% 7.17/1.49    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 7.17/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.49  
% 7.17/1.49  fof(f21,plain,(
% 7.17/1.49    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.17/1.49    inference(ennf_transformation,[],[f8])).
% 7.17/1.49  
% 7.17/1.49  fof(f59,plain,(
% 7.17/1.49    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.17/1.49    inference(cnf_transformation,[],[f21])).
% 7.17/1.49  
% 7.17/1.49  fof(f68,plain,(
% 7.17/1.49    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 7.17/1.49    inference(cnf_transformation,[],[f44])).
% 7.17/1.49  
% 7.17/1.49  fof(f5,axiom,(
% 7.17/1.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.17/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.49  
% 7.17/1.49  fof(f17,plain,(
% 7.17/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.17/1.49    inference(ennf_transformation,[],[f5])).
% 7.17/1.49  
% 7.17/1.49  fof(f18,plain,(
% 7.17/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.17/1.49    inference(flattening,[],[f17])).
% 7.17/1.49  
% 7.17/1.49  fof(f54,plain,(
% 7.17/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.17/1.49    inference(cnf_transformation,[],[f18])).
% 7.17/1.49  
% 7.17/1.49  fof(f10,axiom,(
% 7.17/1.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 7.17/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.49  
% 7.17/1.49  fof(f23,plain,(
% 7.17/1.49    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.17/1.49    inference(ennf_transformation,[],[f10])).
% 7.17/1.49  
% 7.17/1.49  fof(f38,plain,(
% 7.17/1.49    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.17/1.49    inference(nnf_transformation,[],[f23])).
% 7.17/1.49  
% 7.17/1.49  fof(f39,plain,(
% 7.17/1.49    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.17/1.49    inference(flattening,[],[f38])).
% 7.17/1.49  
% 7.17/1.49  fof(f62,plain,(
% 7.17/1.49    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.17/1.49    inference(cnf_transformation,[],[f39])).
% 7.17/1.49  
% 7.17/1.49  fof(f81,plain,(
% 7.17/1.49    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.17/1.49    inference(equality_resolution,[],[f62])).
% 7.17/1.49  
% 7.17/1.49  fof(f1,axiom,(
% 7.17/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.17/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.17/1.49  
% 7.17/1.49  fof(f33,plain,(
% 7.17/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.17/1.49    inference(nnf_transformation,[],[f1])).
% 7.17/1.49  
% 7.17/1.49  fof(f34,plain,(
% 7.17/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.17/1.49    inference(flattening,[],[f33])).
% 7.17/1.49  
% 7.17/1.49  fof(f47,plain,(
% 7.17/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.17/1.49    inference(cnf_transformation,[],[f34])).
% 7.17/1.49  
% 7.17/1.49  fof(f80,plain,(
% 7.17/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.17/1.49    inference(equality_resolution,[],[f47])).
% 7.17/1.49  
% 7.17/1.49  fof(f78,plain,(
% 7.17/1.49    k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3))),
% 7.17/1.49    inference(cnf_transformation,[],[f46])).
% 7.17/1.49  
% 7.17/1.49  fof(f52,plain,(
% 7.17/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.17/1.49    inference(cnf_transformation,[],[f35])).
% 7.17/1.49  
% 7.17/1.49  fof(f49,plain,(
% 7.17/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.17/1.49    inference(cnf_transformation,[],[f34])).
% 7.17/1.49  
% 7.17/1.49  cnf(c_5,plain,
% 7.17/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.17/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_1567,plain,
% 7.17/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.17/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.17/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_11,plain,
% 7.17/1.49      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 7.17/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_1561,plain,
% 7.17/1.49      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 7.17/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_24,plain,
% 7.17/1.49      ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 7.17/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.17/1.49      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 7.17/1.49      | v2_struct_0(X1)
% 7.17/1.49      | ~ v3_orders_2(X1)
% 7.17/1.49      | ~ v4_orders_2(X1)
% 7.17/1.49      | ~ v5_orders_2(X1)
% 7.17/1.49      | ~ l1_orders_2(X1) ),
% 7.17/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_28,negated_conjecture,
% 7.17/1.49      ( v5_orders_2(sK3) ),
% 7.17/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_604,plain,
% 7.17/1.49      ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 7.17/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.17/1.49      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 7.17/1.49      | v2_struct_0(X1)
% 7.17/1.49      | ~ v3_orders_2(X1)
% 7.17/1.49      | ~ v4_orders_2(X1)
% 7.17/1.49      | ~ l1_orders_2(X1)
% 7.17/1.49      | sK3 != X1 ),
% 7.17/1.49      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_605,plain,
% 7.17/1.49      ( ~ r2_hidden(X0,a_2_0_orders_2(sK3,X1))
% 7.17/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.49      | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3))
% 7.17/1.49      | v2_struct_0(sK3)
% 7.17/1.49      | ~ v3_orders_2(sK3)
% 7.17/1.49      | ~ v4_orders_2(sK3)
% 7.17/1.49      | ~ l1_orders_2(sK3) ),
% 7.17/1.49      inference(unflattening,[status(thm)],[c_604]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_31,negated_conjecture,
% 7.17/1.49      ( ~ v2_struct_0(sK3) ),
% 7.17/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_30,negated_conjecture,
% 7.17/1.49      ( v3_orders_2(sK3) ),
% 7.17/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_29,negated_conjecture,
% 7.17/1.49      ( v4_orders_2(sK3) ),
% 7.17/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_27,negated_conjecture,
% 7.17/1.49      ( l1_orders_2(sK3) ),
% 7.17/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_609,plain,
% 7.17/1.49      ( ~ r2_hidden(X0,a_2_0_orders_2(sK3,X1))
% 7.17/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.49      | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) ),
% 7.17/1.49      inference(global_propositional_subsumption,
% 7.17/1.49                [status(thm)],
% 7.17/1.49                [c_605,c_31,c_30,c_29,c_27]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_1558,plain,
% 7.17/1.49      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 7.17/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.17/1.49      | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) = iProver_top ),
% 7.17/1.49      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_18,plain,
% 7.17/1.49      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 7.17/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_13,plain,
% 7.17/1.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.17/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_413,plain,
% 7.17/1.49      ( ~ l1_orders_2(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.17/1.49      inference(resolution,[status(thm)],[c_18,c_13]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_749,plain,
% 7.17/1.49      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 7.17/1.49      inference(resolution_lifted,[status(thm)],[c_413,c_27]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_750,plain,
% 7.17/1.49      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 7.17/1.49      inference(unflattening,[status(thm)],[c_749]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_1644,plain,
% 7.17/1.49      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 7.17/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.17/1.49      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top ),
% 7.17/1.49      inference(light_normalisation,[status(thm)],[c_1558,c_750]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_3,plain,
% 7.17/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.17/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_1569,plain,
% 7.17/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.17/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_20,plain,
% 7.17/1.49      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 7.17/1.49      | r2_hidden(sK1(X1,X2,X0),X2)
% 7.17/1.49      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.17/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.17/1.49      | v2_struct_0(X1)
% 7.17/1.49      | ~ v3_orders_2(X1)
% 7.17/1.49      | ~ v4_orders_2(X1)
% 7.17/1.49      | ~ v5_orders_2(X1)
% 7.17/1.49      | ~ l1_orders_2(X1) ),
% 7.17/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_670,plain,
% 7.17/1.49      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 7.17/1.49      | r2_hidden(sK1(X1,X2,X0),X2)
% 7.17/1.49      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.17/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.17/1.49      | v2_struct_0(X1)
% 7.17/1.49      | ~ v3_orders_2(X1)
% 7.17/1.49      | ~ v4_orders_2(X1)
% 7.17/1.49      | ~ l1_orders_2(X1)
% 7.17/1.49      | sK3 != X1 ),
% 7.17/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_671,plain,
% 7.17/1.49      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1))
% 7.17/1.49      | r2_hidden(sK1(sK3,X1,X0),X1)
% 7.17/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.17/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.49      | v2_struct_0(sK3)
% 7.17/1.49      | ~ v3_orders_2(sK3)
% 7.17/1.49      | ~ v4_orders_2(sK3)
% 7.17/1.49      | ~ l1_orders_2(sK3) ),
% 7.17/1.49      inference(unflattening,[status(thm)],[c_670]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_675,plain,
% 7.17/1.49      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1))
% 7.17/1.49      | r2_hidden(sK1(sK3,X1,X0),X1)
% 7.17/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.17/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.17/1.49      inference(global_propositional_subsumption,
% 7.17/1.49                [status(thm)],
% 7.17/1.49                [c_671,c_31,c_30,c_29,c_27]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_1555,plain,
% 7.17/1.49      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) = iProver_top
% 7.17/1.49      | r2_hidden(sK1(sK3,X1,X0),X1) = iProver_top
% 7.17/1.49      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 7.17/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 7.17/1.49      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 7.17/1.49  
% 7.17/1.49  cnf(c_1651,plain,
% 7.17/1.49      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) = iProver_top
% 7.17/1.49      | r2_hidden(sK1(sK3,X1,X0),X1) = iProver_top
% 7.17/1.49      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 7.17/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 7.17/1.50      inference(light_normalisation,[status(thm)],[c_1555,c_750]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_8,plain,
% 7.17/1.50      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.17/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_1564,plain,
% 7.17/1.50      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 7.17/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_2195,plain,
% 7.17/1.50      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) = iProver_top
% 7.17/1.50      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 7.17/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.17/1.50      | r1_tarski(X1,sK1(sK3,X1,X0)) != iProver_top ),
% 7.17/1.50      inference(superposition,[status(thm)],[c_1651,c_1564]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_2460,plain,
% 7.17/1.50      ( r2_hidden(X0,a_2_0_orders_2(sK3,k1_xboole_0)) = iProver_top
% 7.17/1.50      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 7.17/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 7.17/1.50      inference(superposition,[status(thm)],[c_1569,c_2195]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_4,plain,
% 7.17/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.17/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_1568,plain,
% 7.17/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.17/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_17,plain,
% 7.17/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.17/1.50      | v2_struct_0(X1)
% 7.17/1.50      | ~ v3_orders_2(X1)
% 7.17/1.50      | ~ v4_orders_2(X1)
% 7.17/1.50      | ~ v5_orders_2(X1)
% 7.17/1.50      | ~ l1_orders_2(X1)
% 7.17/1.50      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 7.17/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_694,plain,
% 7.17/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.17/1.50      | v2_struct_0(X1)
% 7.17/1.50      | ~ v3_orders_2(X1)
% 7.17/1.50      | ~ v4_orders_2(X1)
% 7.17/1.50      | ~ l1_orders_2(X1)
% 7.17/1.50      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0)
% 7.17/1.50      | sK3 != X1 ),
% 7.17/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_695,plain,
% 7.17/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.50      | v2_struct_0(sK3)
% 7.17/1.50      | ~ v3_orders_2(sK3)
% 7.17/1.50      | ~ v4_orders_2(sK3)
% 7.17/1.50      | ~ l1_orders_2(sK3)
% 7.17/1.50      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 7.17/1.50      inference(unflattening,[status(thm)],[c_694]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_699,plain,
% 7.17/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.50      | a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0) ),
% 7.17/1.50      inference(global_propositional_subsumption,
% 7.17/1.50                [status(thm)],
% 7.17/1.50                [c_695,c_31,c_30,c_29,c_27]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_1554,plain,
% 7.17/1.50      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 7.17/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 7.17/1.50      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_1608,plain,
% 7.17/1.50      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 7.17/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 7.17/1.50      inference(light_normalisation,[status(thm)],[c_1554,c_750]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_1966,plain,
% 7.17/1.50      ( a_2_0_orders_2(sK3,k1_xboole_0) = k1_orders_2(sK3,k1_xboole_0) ),
% 7.17/1.50      inference(superposition,[status(thm)],[c_1568,c_1608]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_25,plain,
% 7.17/1.50      ( v2_struct_0(X0)
% 7.17/1.50      | ~ v3_orders_2(X0)
% 7.17/1.50      | ~ v4_orders_2(X0)
% 7.17/1.50      | ~ v5_orders_2(X0)
% 7.17/1.50      | ~ l1_orders_2(X0)
% 7.17/1.50      | k1_orders_2(X0,k1_struct_0(X0)) = u1_struct_0(X0) ),
% 7.17/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_543,plain,
% 7.17/1.50      ( v2_struct_0(X0)
% 7.17/1.50      | ~ v3_orders_2(X0)
% 7.17/1.50      | ~ v4_orders_2(X0)
% 7.17/1.50      | ~ l1_orders_2(X0)
% 7.17/1.50      | k1_orders_2(X0,k1_struct_0(X0)) = u1_struct_0(X0)
% 7.17/1.50      | sK3 != X0 ),
% 7.17/1.50      inference(resolution_lifted,[status(thm)],[c_25,c_28]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_544,plain,
% 7.17/1.50      ( v2_struct_0(sK3)
% 7.17/1.50      | ~ v3_orders_2(sK3)
% 7.17/1.50      | ~ v4_orders_2(sK3)
% 7.17/1.50      | ~ l1_orders_2(sK3)
% 7.17/1.50      | k1_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 7.17/1.50      inference(unflattening,[status(thm)],[c_543]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_546,plain,
% 7.17/1.50      ( k1_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 7.17/1.50      inference(global_propositional_subsumption,
% 7.17/1.50                [status(thm)],
% 7.17/1.50                [c_544,c_31,c_30,c_29,c_27]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_12,plain,
% 7.17/1.50      ( ~ l1_struct_0(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 7.17/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_424,plain,
% 7.17/1.50      ( ~ l1_orders_2(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 7.17/1.50      inference(resolution,[status(thm)],[c_18,c_12]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_744,plain,
% 7.17/1.50      ( k1_struct_0(X0) = k1_xboole_0 | sK3 != X0 ),
% 7.17/1.50      inference(resolution_lifted,[status(thm)],[c_424,c_27]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_745,plain,
% 7.17/1.50      ( k1_struct_0(sK3) = k1_xboole_0 ),
% 7.17/1.50      inference(unflattening,[status(thm)],[c_744]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_1582,plain,
% 7.17/1.50      ( k1_orders_2(sK3,k1_xboole_0) = k2_struct_0(sK3) ),
% 7.17/1.50      inference(light_normalisation,[status(thm)],[c_546,c_745,c_750]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_1967,plain,
% 7.17/1.50      ( a_2_0_orders_2(sK3,k1_xboole_0) = k2_struct_0(sK3) ),
% 7.17/1.50      inference(light_normalisation,[status(thm)],[c_1966,c_1582]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_2461,plain,
% 7.17/1.50      ( r2_hidden(X0,k2_struct_0(sK3)) = iProver_top
% 7.17/1.50      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 7.17/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 7.17/1.50      inference(light_normalisation,[status(thm)],[c_2460,c_1967]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_3587,plain,
% 7.17/1.50      ( r2_hidden(X0,k2_struct_0(sK3)) = iProver_top
% 7.17/1.50      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 7.17/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_2461,c_1568]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_3591,plain,
% 7.17/1.50      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 7.17/1.50      | r2_hidden(sK2(X0,sK3,X1),k2_struct_0(sK3)) = iProver_top
% 7.17/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 7.17/1.50      inference(superposition,[status(thm)],[c_1644,c_3587]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_22,plain,
% 7.17/1.50      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 7.17/1.50      | ~ r2_hidden(X1,X3)
% 7.17/1.50      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 7.17/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.17/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 7.17/1.50      | v2_struct_0(X0)
% 7.17/1.50      | ~ v3_orders_2(X0)
% 7.17/1.50      | ~ v4_orders_2(X0)
% 7.17/1.50      | ~ v5_orders_2(X0)
% 7.17/1.50      | ~ l1_orders_2(X0) ),
% 7.17/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_551,plain,
% 7.17/1.50      ( r2_orders_2(X0,X1,sK2(X2,X0,X3))
% 7.17/1.50      | ~ r2_hidden(X1,X3)
% 7.17/1.50      | ~ r2_hidden(X2,a_2_0_orders_2(X0,X3))
% 7.17/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.17/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 7.17/1.50      | v2_struct_0(X0)
% 7.17/1.50      | ~ v3_orders_2(X0)
% 7.17/1.50      | ~ v4_orders_2(X0)
% 7.17/1.50      | ~ l1_orders_2(X0)
% 7.17/1.50      | sK3 != X0 ),
% 7.17/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_552,plain,
% 7.17/1.50      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 7.17/1.50      | ~ r2_hidden(X0,X2)
% 7.17/1.50      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
% 7.17/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.17/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.17/1.50      | v2_struct_0(sK3)
% 7.17/1.50      | ~ v3_orders_2(sK3)
% 7.17/1.50      | ~ v4_orders_2(sK3)
% 7.17/1.50      | ~ l1_orders_2(sK3) ),
% 7.17/1.50      inference(unflattening,[status(thm)],[c_551]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_556,plain,
% 7.17/1.50      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 7.17/1.50      | ~ r2_hidden(X0,X2)
% 7.17/1.50      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
% 7.17/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.17/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.17/1.50      inference(global_propositional_subsumption,
% 7.17/1.50                [status(thm)],
% 7.17/1.50                [c_552,c_31,c_30,c_29,c_27]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_7,plain,
% 7.17/1.50      ( ~ r2_hidden(X0,X1)
% 7.17/1.50      | m1_subset_1(X0,X2)
% 7.17/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 7.17/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_572,plain,
% 7.17/1.50      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2))
% 7.17/1.50      | ~ r2_hidden(X0,X2)
% 7.17/1.50      | ~ r2_hidden(X1,a_2_0_orders_2(sK3,X2))
% 7.17/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.17/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_556,c_7]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_1560,plain,
% 7.17/1.50      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
% 7.17/1.50      | r2_hidden(X0,X2) != iProver_top
% 7.17/1.50      | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top
% 7.17/1.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 7.17/1.50      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_1669,plain,
% 7.17/1.50      ( r2_orders_2(sK3,X0,sK2(X1,sK3,X2)) = iProver_top
% 7.17/1.50      | r2_hidden(X0,X2) != iProver_top
% 7.17/1.50      | r2_hidden(X1,a_2_0_orders_2(sK3,X2)) != iProver_top
% 7.17/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 7.17/1.50      inference(light_normalisation,[status(thm)],[c_1560,c_750]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_15,plain,
% 7.17/1.50      ( ~ r2_orders_2(X0,X1,X1)
% 7.17/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.17/1.50      | ~ l1_orders_2(X0) ),
% 7.17/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_754,plain,
% 7.17/1.50      ( ~ r2_orders_2(X0,X1,X1)
% 7.17/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.17/1.50      | sK3 != X0 ),
% 7.17/1.50      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_755,plain,
% 7.17/1.50      ( ~ r2_orders_2(sK3,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 7.17/1.50      inference(unflattening,[status(thm)],[c_754]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_1553,plain,
% 7.17/1.50      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 7.17/1.50      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 7.17/1.50      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_1603,plain,
% 7.17/1.50      ( r2_orders_2(sK3,X0,X0) != iProver_top
% 7.17/1.50      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 7.17/1.50      inference(light_normalisation,[status(thm)],[c_1553,c_750]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_2094,plain,
% 7.17/1.50      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 7.17/1.50      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 7.17/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.17/1.50      | m1_subset_1(sK2(X0,sK3,X1),k2_struct_0(sK3)) != iProver_top ),
% 7.17/1.50      inference(superposition,[status(thm)],[c_1669,c_1603]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_2508,plain,
% 7.17/1.50      ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.17/1.50      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 7.17/1.50      | r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top ),
% 7.17/1.50      inference(global_propositional_subsumption,[status(thm)],[c_2094,c_1644]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_2509,plain,
% 7.17/1.50      ( r2_hidden(X0,a_2_0_orders_2(sK3,X1)) != iProver_top
% 7.17/1.50      | r2_hidden(sK2(X0,sK3,X1),X1) != iProver_top
% 7.17/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 7.17/1.50      inference(renaming,[status(thm)],[c_2508]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_3763,plain,
% 7.17/1.50      ( r2_hidden(X0,a_2_0_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 7.17/1.50      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 7.17/1.50      inference(superposition,[status(thm)],[c_3591,c_2509]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f80]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_1570,plain,
% 7.17/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.17/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_2604,plain,
% 7.17/1.50      ( a_2_0_orders_2(sK3,X0) = k1_orders_2(sK3,X0)
% 7.17/1.50      | r1_tarski(X0,k2_struct_0(sK3)) != iProver_top ),
% 7.17/1.50      inference(superposition,[status(thm)],[c_1567,c_1608]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_2819,plain,
% 7.17/1.50      ( a_2_0_orders_2(sK3,k2_struct_0(sK3)) = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 7.17/1.50      inference(superposition,[status(thm)],[c_1570,c_2604]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_3773,plain,
% 7.17/1.50      ( r2_hidden(X0,k1_orders_2(sK3,k2_struct_0(sK3))) != iProver_top
% 7.17/1.50      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 7.17/1.50      inference(light_normalisation,[status(thm)],[c_3763,c_2819]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_22141,plain,
% 7.17/1.50      ( k1_orders_2(sK3,k2_struct_0(sK3)) = k1_xboole_0
% 7.17/1.50      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 7.17/1.50      inference(superposition,[status(thm)],[c_1561,c_3773]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_26,negated_conjecture,
% 7.17/1.50      ( k1_xboole_0 != k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 7.17/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_6,plain,
% 7.17/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.17/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_93,plain,
% 7.17/1.50      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 7.17/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.17/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_99,plain,
% 7.17/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 7.17/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_0,plain,
% 7.17/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.17/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_107,plain,
% 7.17/1.50      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 7.17/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_1057,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_1771,plain,
% 7.17/1.50      ( k1_orders_2(sK3,k2_struct_0(sK3)) != X0
% 7.17/1.50      | k1_xboole_0 != X0
% 7.17/1.50      | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3)) ),
% 7.17/1.50      inference(instantiation,[status(thm)],[c_1057]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_1772,plain,
% 7.17/1.50      ( k1_orders_2(sK3,k2_struct_0(sK3)) != k1_xboole_0
% 7.17/1.50      | k1_xboole_0 = k1_orders_2(sK3,k2_struct_0(sK3))
% 7.17/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.17/1.50      inference(instantiation,[status(thm)],[c_1771]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_22242,plain,
% 7.17/1.50      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 7.17/1.50      inference(global_propositional_subsumption,
% 7.17/1.50                [status(thm)],
% 7.17/1.50                [c_22141,c_26,c_93,c_99,c_107,c_1772]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_22247,plain,
% 7.17/1.50      ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK3)) != iProver_top ),
% 7.17/1.50      inference(superposition,[status(thm)],[c_1567,c_22242]) ).
% 7.17/1.50  
% 7.17/1.50  cnf(c_22251,plain,
% 7.17/1.50      ( $false ),
% 7.17/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_22247,c_1570]) ).
% 7.17/1.50  
% 7.17/1.50  
% 7.17/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.17/1.50  
% 7.17/1.50  ------                               Statistics
% 7.17/1.50  
% 7.17/1.50  ------ General
% 7.17/1.50  
% 7.17/1.50  abstr_ref_over_cycles:                  0
% 7.17/1.50  abstr_ref_under_cycles:                 0
% 7.17/1.50  gc_basic_clause_elim:                   0
% 7.17/1.50  forced_gc_time:                         0
% 7.17/1.50  parsing_time:                           0.011
% 7.17/1.50  unif_index_cands_time:                  0.
% 7.17/1.50  unif_index_add_time:                    0.
% 7.17/1.50  orderings_time:                         0.
% 7.17/1.50  out_proof_time:                         0.012
% 7.17/1.50  total_time:                             0.668
% 7.17/1.50  num_of_symbols:                         54
% 7.17/1.50  num_of_terms:                           13688
% 7.17/1.50  
% 7.17/1.50  ------ Preprocessing
% 7.17/1.50  
% 7.17/1.50  num_of_splits:                          0
% 7.17/1.50  num_of_split_atoms:                     0
% 7.17/1.50  num_of_reused_defs:                     0
% 7.17/1.50  num_eq_ax_congr_red:                    37
% 7.17/1.50  num_of_sem_filtered_clauses:            1
% 7.17/1.50  num_of_subtypes:                        0
% 7.17/1.50  monotx_restored_types:                  0
% 7.17/1.50  sat_num_of_epr_types:                   0
% 7.17/1.50  sat_num_of_non_cyclic_types:            0
% 7.17/1.50  sat_guarded_non_collapsed_types:        0
% 7.17/1.50  num_pure_diseq_elim:                    0
% 7.17/1.50  simp_replaced_by:                       0
% 7.17/1.50  res_preprocessed:                       129
% 7.17/1.50  prep_upred:                             0
% 7.17/1.50  prep_unflattend:                        25
% 7.17/1.50  smt_new_axioms:                         0
% 7.17/1.50  pred_elim_cands:                        4
% 7.17/1.50  pred_elim:                              7
% 7.17/1.50  pred_elim_cl:                           8
% 7.17/1.50  pred_elim_cycles:                       10
% 7.17/1.50  merged_defs:                            8
% 7.17/1.50  merged_defs_ncl:                        0
% 7.17/1.50  bin_hyper_res:                          8
% 7.17/1.50  prep_cycles:                            4
% 7.17/1.50  pred_elim_time:                         0.016
% 7.17/1.50  splitting_time:                         0.
% 7.17/1.50  sem_filter_time:                        0.
% 7.17/1.50  monotx_time:                            0.
% 7.17/1.50  subtype_inf_time:                       0.
% 7.17/1.50  
% 7.17/1.50  ------ Problem properties
% 7.17/1.50  
% 7.17/1.50  clauses:                                23
% 7.17/1.50  conjectures:                            1
% 7.17/1.50  epr:                                    4
% 7.17/1.50  horn:                                   20
% 7.17/1.50  ground:                                 4
% 7.17/1.50  unary:                                  7
% 7.17/1.50  binary:                                 6
% 7.17/1.50  lits:                                   53
% 7.17/1.50  lits_eq:                                12
% 7.17/1.50  fd_pure:                                0
% 7.17/1.50  fd_pseudo:                              0
% 7.17/1.50  fd_cond:                                3
% 7.17/1.50  fd_pseudo_cond:                         1
% 7.17/1.50  ac_symbols:                             0
% 7.17/1.50  
% 7.17/1.50  ------ Propositional Solver
% 7.17/1.50  
% 7.17/1.50  prop_solver_calls:                      31
% 7.17/1.50  prop_fast_solver_calls:                 1642
% 7.17/1.50  smt_solver_calls:                       0
% 7.17/1.50  smt_fast_solver_calls:                  0
% 7.17/1.50  prop_num_of_clauses:                    6518
% 7.17/1.50  prop_preprocess_simplified:             10853
% 7.17/1.50  prop_fo_subsumed:                       46
% 7.17/1.50  prop_solver_time:                       0.
% 7.17/1.50  smt_solver_time:                        0.
% 7.17/1.50  smt_fast_solver_time:                   0.
% 7.17/1.50  prop_fast_solver_time:                  0.
% 7.17/1.50  prop_unsat_core_time:                   0.
% 7.17/1.50  
% 7.17/1.50  ------ QBF
% 7.17/1.50  
% 7.17/1.50  qbf_q_res:                              0
% 7.17/1.50  qbf_num_tautologies:                    0
% 7.17/1.50  qbf_prep_cycles:                        0
% 7.17/1.50  
% 7.17/1.50  ------ BMC1
% 7.17/1.50  
% 7.17/1.50  bmc1_current_bound:                     -1
% 7.17/1.50  bmc1_last_solved_bound:                 -1
% 7.17/1.50  bmc1_unsat_core_size:                   -1
% 7.17/1.50  bmc1_unsat_core_parents_size:           -1
% 7.17/1.50  bmc1_merge_next_fun:                    0
% 7.17/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.17/1.50  
% 7.17/1.50  ------ Instantiation
% 7.17/1.50  
% 7.17/1.50  inst_num_of_clauses:                    1434
% 7.17/1.50  inst_num_in_passive:                    646
% 7.17/1.50  inst_num_in_active:                     680
% 7.17/1.50  inst_num_in_unprocessed:                108
% 7.17/1.50  inst_num_of_loops:                      930
% 7.17/1.50  inst_num_of_learning_restarts:          0
% 7.17/1.50  inst_num_moves_active_passive:          245
% 7.17/1.50  inst_lit_activity:                      0
% 7.17/1.50  inst_lit_activity_moves:                0
% 7.17/1.50  inst_num_tautologies:                   0
% 7.17/1.50  inst_num_prop_implied:                  0
% 7.17/1.50  inst_num_existing_simplified:           0
% 7.17/1.50  inst_num_eq_res_simplified:             0
% 7.17/1.50  inst_num_child_elim:                    0
% 7.17/1.50  inst_num_of_dismatching_blockings:      892
% 7.17/1.50  inst_num_of_non_proper_insts:           2093
% 7.17/1.50  inst_num_of_duplicates:                 0
% 7.17/1.50  inst_inst_num_from_inst_to_res:         0
% 7.17/1.50  inst_dismatching_checking_time:         0.
% 7.17/1.50  
% 7.17/1.50  ------ Resolution
% 7.17/1.50  
% 7.17/1.50  res_num_of_clauses:                     0
% 7.17/1.50  res_num_in_passive:                     0
% 7.17/1.50  res_num_in_active:                      0
% 7.17/1.50  res_num_of_loops:                       133
% 7.17/1.50  res_forward_subset_subsumed:            162
% 7.17/1.50  res_backward_subset_subsumed:           0
% 7.17/1.50  res_forward_subsumed:                   0
% 7.17/1.50  res_backward_subsumed:                  0
% 7.17/1.50  res_forward_subsumption_resolution:     2
% 7.17/1.50  res_backward_subsumption_resolution:    0
% 7.17/1.50  res_clause_to_clause_subsumption:       4653
% 7.17/1.50  res_orphan_elimination:                 0
% 7.17/1.50  res_tautology_del:                      162
% 7.17/1.50  res_num_eq_res_simplified:              0
% 7.17/1.50  res_num_sel_changes:                    0
% 7.17/1.50  res_moves_from_active_to_pass:          0
% 7.17/1.50  
% 7.17/1.50  ------ Superposition
% 7.17/1.50  
% 7.17/1.50  sup_time_total:                         0.
% 7.17/1.50  sup_time_generating:                    0.
% 7.17/1.50  sup_time_sim_full:                      0.
% 7.17/1.50  sup_time_sim_immed:                     0.
% 7.17/1.50  
% 7.17/1.50  sup_num_of_clauses:                     706
% 7.17/1.50  sup_num_in_active:                      183
% 7.17/1.50  sup_num_in_passive:                     523
% 7.17/1.50  sup_num_of_loops:                       185
% 7.17/1.50  sup_fw_superposition:                   609
% 7.17/1.50  sup_bw_superposition:                   284
% 7.17/1.50  sup_immediate_simplified:               212
% 7.17/1.50  sup_given_eliminated:                   0
% 7.17/1.50  comparisons_done:                       0
% 7.17/1.50  comparisons_avoided:                    103
% 7.17/1.50  
% 7.17/1.50  ------ Simplifications
% 7.17/1.50  
% 7.17/1.50  
% 7.17/1.50  sim_fw_subset_subsumed:                 37
% 7.17/1.50  sim_bw_subset_subsumed:                 8
% 7.17/1.50  sim_fw_subsumed:                        38
% 7.17/1.50  sim_bw_subsumed:                        2
% 7.17/1.50  sim_fw_subsumption_res:                 20
% 7.17/1.50  sim_bw_subsumption_res:                 0
% 7.17/1.50  sim_tautology_del:                      13
% 7.17/1.50  sim_eq_tautology_del:                   12
% 7.17/1.50  sim_eq_res_simp:                        0
% 7.17/1.50  sim_fw_demodulated:                     11
% 7.17/1.50  sim_bw_demodulated:                     1
% 7.17/1.50  sim_light_normalised:                   163
% 7.17/1.50  sim_joinable_taut:                      0
% 7.17/1.50  sim_joinable_simp:                      0
% 7.17/1.50  sim_ac_normalised:                      0
% 7.17/1.50  sim_smt_subsumption:                    0
% 7.17/1.50  
%------------------------------------------------------------------------------
