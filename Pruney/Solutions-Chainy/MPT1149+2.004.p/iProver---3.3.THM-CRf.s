%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:04 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 386 expanded)
%              Number of clauses        :   87 ( 134 expanded)
%              Number of leaves         :   16 (  75 expanded)
%              Depth                    :   21
%              Number of atoms          :  582 (1749 expanded)
%              Number of equality atoms :  198 ( 381 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => r2_hidden(X3,X2) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & m1_subset_1(X3,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & m1_subset_1(X3,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & m1_subset_1(X3,X1) )
     => ( ~ r2_hidden(sK0(X1,X2),X2)
        & m1_subset_1(sK0(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK0(X1,X2),X2)
            & m1_subset_1(sK0(X1,X2),X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f32])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK0(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f28,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k1_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k1_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f40,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k1_orders_2(X0,k1_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( u1_struct_0(sK3) != k1_orders_2(sK3,k1_struct_0(sK3))
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( u1_struct_0(sK3) != k1_orders_2(sK3,k1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f40])).

fof(f64,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
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

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f26])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f38,plain,(
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

fof(f37,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
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
    inference(equality_resolution,[],[f61])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK0(X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    u1_struct_0(sK3) != k1_orders_2(sK3,k1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1146,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1151,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2641,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_orders_2(X1,X0),u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_1151])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1155,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X2,X0),X2)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_173,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_174,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_173])).

cnf(c_231,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X0,X2),X0)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_174])).

cnf(c_357,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_358,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_357])).

cnf(c_418,plain,
    ( m1_subset_1(sK0(X0,X1),X0)
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_231,c_358])).

cnf(c_1132,plain,
    ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_3206,plain,
    ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1155,c_1132])).

cnf(c_25,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1135,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1153,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1147,plain,
    ( a_2_0_orders_2(X0,X1) = k1_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2600,plain,
    ( a_2_0_orders_2(X0,k1_xboole_0) = k1_orders_2(X0,k1_xboole_0)
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1153,c_1147])).

cnf(c_4734,plain,
    ( a_2_0_orders_2(sK3,k1_xboole_0) = k1_orders_2(sK3,k1_xboole_0)
    | v2_struct_0(sK3) = iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1135,c_2600])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_23,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1491,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1494,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1491])).

cnf(c_1581,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | a_2_0_orders_2(X0,k1_xboole_0) = k1_orders_2(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1588,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_0_orders_2(sK3,k1_xboole_0) = k1_orders_2(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1581])).

cnf(c_4737,plain,
    ( a_2_0_orders_2(sK3,k1_xboole_0) = k1_orders_2(sK3,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4734,c_26,c_25,c_24,c_23,c_22,c_1494,c_1588])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1154,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_0_orders_2(X1,X2))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1143,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(X1,X2)) = iProver_top
    | r2_hidden(sK1(X1,X2,X0),X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1149,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2868,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(X1,X2)) = iProver_top
    | r1_tarski(X2,sK1(X1,X2,X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_1149])).

cnf(c_12285,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(X1,k1_xboole_0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_2868])).

cnf(c_14046,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,a_2_0_orders_2(X1,k1_xboole_0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12285,c_1153])).

cnf(c_14050,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k1_xboole_0)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4737,c_14046])).

cnf(c_27,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_29,plain,
    ( v4_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_30,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_31,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14569,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,k1_xboole_0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14050,c_27,c_28,c_29,c_30,c_31])).

cnf(c_14570,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k1_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_14569])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X2,X0),X0)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X0,X2),X2)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_174])).

cnf(c_417,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_230,c_358])).

cnf(c_1133,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_14579,plain,
    ( m1_subset_1(sK0(X0,k1_orders_2(sK3,k1_xboole_0)),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_orders_2(sK3,k1_xboole_0)) = iProver_top
    | r1_tarski(k1_orders_2(sK3,k1_xboole_0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_14570,c_1133])).

cnf(c_15073,plain,
    ( r1_tarski(k1_orders_2(sK3,k1_xboole_0),X0) != iProver_top
    | r1_tarski(k1_orders_2(sK3,k1_xboole_0),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(u1_struct_0(sK3),X0) != iProver_top
    | r1_tarski(u1_struct_0(sK3),k1_orders_2(sK3,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3206,c_14579])).

cnf(c_1493,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1491])).

cnf(c_1495,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1493])).

cnf(c_1582,plain,
    ( m1_subset_1(k1_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1583,plain,
    ( m1_subset_1(k1_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1582])).

cnf(c_1585,plain,
    ( m1_subset_1(k1_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_1616,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2021,plain,
    ( ~ m1_subset_1(k1_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
    | r1_tarski(k1_orders_2(X0,k1_xboole_0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1616])).

cnf(c_2042,plain,
    ( m1_subset_1(k1_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(k1_orders_2(X0,k1_xboole_0),u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2021])).

cnf(c_2044,plain,
    ( m1_subset_1(k1_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k1_orders_2(sK3,k1_xboole_0),u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2042])).

cnf(c_1138,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1145,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1768,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_1145])).

cnf(c_11,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1148,plain,
    ( k1_struct_0(X0) = k1_xboole_0
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1876,plain,
    ( k1_struct_0(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1768,c_1148])).

cnf(c_21,negated_conjecture,
    ( u1_struct_0(sK3) != k1_orders_2(sK3,k1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2080,plain,
    ( k1_orders_2(sK3,k1_xboole_0) != u1_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_1876,c_21])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2270,plain,
    ( ~ r1_tarski(X0,u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(X1),X0)
    | X0 = u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5523,plain,
    ( ~ r1_tarski(k1_orders_2(X0,k1_xboole_0),u1_struct_0(X0))
    | ~ r1_tarski(u1_struct_0(X0),k1_orders_2(X0,k1_xboole_0))
    | k1_orders_2(X0,k1_xboole_0) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2270])).

cnf(c_5524,plain,
    ( k1_orders_2(X0,k1_xboole_0) = u1_struct_0(X0)
    | r1_tarski(k1_orders_2(X0,k1_xboole_0),u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(X0),k1_orders_2(X0,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5523])).

cnf(c_5526,plain,
    ( k1_orders_2(sK3,k1_xboole_0) = u1_struct_0(sK3)
    | r1_tarski(k1_orders_2(sK3,k1_xboole_0),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(u1_struct_0(sK3),k1_orders_2(sK3,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5524])).

cnf(c_16540,plain,
    ( r1_tarski(u1_struct_0(sK3),X0) != iProver_top
    | r1_tarski(k1_orders_2(sK3,k1_xboole_0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15073,c_27,c_28,c_29,c_30,c_31,c_1495,c_1585,c_2044,c_2080,c_5526])).

cnf(c_16541,plain,
    ( r1_tarski(k1_orders_2(sK3,k1_xboole_0),X0) != iProver_top
    | r1_tarski(u1_struct_0(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16540])).

cnf(c_16549,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2641,c_16541])).

cnf(c_1626,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1631,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1626])).

cnf(c_1633,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1631])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16549,c_1633,c_1495,c_31,c_30,c_29,c_28,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:59:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.58/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.58/1.48  
% 7.58/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.58/1.48  
% 7.58/1.48  ------  iProver source info
% 7.58/1.48  
% 7.58/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.58/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.58/1.48  git: non_committed_changes: false
% 7.58/1.48  git: last_make_outside_of_git: false
% 7.58/1.48  
% 7.58/1.48  ------ 
% 7.58/1.48  ------ Parsing...
% 7.58/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.58/1.48  
% 7.58/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.58/1.48  
% 7.58/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.58/1.48  
% 7.58/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.58/1.48  ------ Proving...
% 7.58/1.48  ------ Problem Properties 
% 7.58/1.48  
% 7.58/1.48  
% 7.58/1.48  clauses                                 26
% 7.58/1.48  conjectures                             6
% 7.58/1.48  EPR                                     10
% 7.58/1.48  Horn                                    17
% 7.58/1.48  unary                                   9
% 7.58/1.48  binary                                  5
% 7.58/1.48  lits                                    100
% 7.58/1.48  lits eq                                 5
% 7.58/1.48  fd_pure                                 0
% 7.58/1.48  fd_pseudo                               0
% 7.58/1.48  fd_cond                                 0
% 7.58/1.48  fd_pseudo_cond                          1
% 7.58/1.48  AC symbols                              0
% 7.58/1.48  
% 7.58/1.48  ------ Input Options Time Limit: Unbounded
% 7.58/1.48  
% 7.58/1.48  
% 7.58/1.48  ------ 
% 7.58/1.48  Current options:
% 7.58/1.48  ------ 
% 7.58/1.48  
% 7.58/1.48  
% 7.58/1.48  
% 7.58/1.48  
% 7.58/1.48  ------ Proving...
% 7.58/1.48  
% 7.58/1.48  
% 7.58/1.48  % SZS status Theorem for theBenchmark.p
% 7.58/1.48  
% 7.58/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.58/1.48  
% 7.58/1.48  fof(f10,axiom,(
% 7.58/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.58/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.48  
% 7.58/1.48  fof(f23,plain,(
% 7.58/1.48    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 7.58/1.48    inference(ennf_transformation,[],[f10])).
% 7.58/1.48  
% 7.58/1.48  fof(f24,plain,(
% 7.58/1.48    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.58/1.48    inference(flattening,[],[f23])).
% 7.58/1.48  
% 7.58/1.48  fof(f55,plain,(
% 7.58/1.48    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.58/1.48    inference(cnf_transformation,[],[f24])).
% 7.58/1.48  
% 7.58/1.48  fof(f5,axiom,(
% 7.58/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.58/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.48  
% 7.58/1.48  fof(f34,plain,(
% 7.58/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.58/1.48    inference(nnf_transformation,[],[f5])).
% 7.58/1.48  
% 7.58/1.48  fof(f49,plain,(
% 7.58/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.58/1.48    inference(cnf_transformation,[],[f34])).
% 7.58/1.48  
% 7.58/1.48  fof(f1,axiom,(
% 7.58/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.58/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.48  
% 7.58/1.48  fof(f30,plain,(
% 7.58/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.58/1.48    inference(nnf_transformation,[],[f1])).
% 7.58/1.48  
% 7.58/1.48  fof(f31,plain,(
% 7.58/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.58/1.48    inference(flattening,[],[f30])).
% 7.58/1.48  
% 7.58/1.48  fof(f42,plain,(
% 7.58/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.58/1.48    inference(cnf_transformation,[],[f31])).
% 7.58/1.48  
% 7.58/1.48  fof(f70,plain,(
% 7.58/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.58/1.48    inference(equality_resolution,[],[f42])).
% 7.58/1.48  
% 7.58/1.48  fof(f3,axiom,(
% 7.58/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X1) => r2_hidden(X3,X2)) => r1_tarski(X1,X2))))),
% 7.58/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.48  
% 7.58/1.48  fof(f15,plain,(
% 7.58/1.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & m1_subset_1(X3,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.58/1.48    inference(ennf_transformation,[],[f3])).
% 7.58/1.48  
% 7.58/1.48  fof(f16,plain,(
% 7.58/1.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & m1_subset_1(X3,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.58/1.48    inference(flattening,[],[f15])).
% 7.58/1.48  
% 7.58/1.48  fof(f32,plain,(
% 7.58/1.48    ! [X2,X1] : (? [X3] : (~r2_hidden(X3,X2) & m1_subset_1(X3,X1)) => (~r2_hidden(sK0(X1,X2),X2) & m1_subset_1(sK0(X1,X2),X1)))),
% 7.58/1.48    introduced(choice_axiom,[])).
% 7.58/1.48  
% 7.58/1.48  fof(f33,plain,(
% 7.58/1.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK0(X1,X2),X2) & m1_subset_1(sK0(X1,X2),X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.58/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f32])).
% 7.58/1.48  
% 7.58/1.48  fof(f46,plain,(
% 7.58/1.48    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | m1_subset_1(sK0(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.58/1.48    inference(cnf_transformation,[],[f33])).
% 7.58/1.48  
% 7.58/1.48  fof(f50,plain,(
% 7.58/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.58/1.48    inference(cnf_transformation,[],[f34])).
% 7.58/1.48  
% 7.58/1.48  fof(f13,conjecture,(
% 7.58/1.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)))),
% 7.58/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.48  
% 7.58/1.48  fof(f14,negated_conjecture,(
% 7.58/1.48    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)))),
% 7.58/1.48    inference(negated_conjecture,[],[f13])).
% 7.58/1.48  
% 7.58/1.48  fof(f28,plain,(
% 7.58/1.48    ? [X0] : (u1_struct_0(X0) != k1_orders_2(X0,k1_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 7.58/1.48    inference(ennf_transformation,[],[f14])).
% 7.58/1.48  
% 7.58/1.48  fof(f29,plain,(
% 7.58/1.48    ? [X0] : (u1_struct_0(X0) != k1_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 7.58/1.48    inference(flattening,[],[f28])).
% 7.58/1.48  
% 7.58/1.48  fof(f40,plain,(
% 7.58/1.48    ? [X0] : (u1_struct_0(X0) != k1_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (u1_struct_0(sK3) != k1_orders_2(sK3,k1_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 7.58/1.48    introduced(choice_axiom,[])).
% 7.58/1.48  
% 7.58/1.48  fof(f41,plain,(
% 7.58/1.48    u1_struct_0(sK3) != k1_orders_2(sK3,k1_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 7.58/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f40])).
% 7.58/1.48  
% 7.58/1.48  fof(f64,plain,(
% 7.58/1.48    v3_orders_2(sK3)),
% 7.58/1.48    inference(cnf_transformation,[],[f41])).
% 7.58/1.48  
% 7.58/1.48  fof(f4,axiom,(
% 7.58/1.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.58/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.48  
% 7.58/1.48  fof(f48,plain,(
% 7.58/1.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.58/1.48    inference(cnf_transformation,[],[f4])).
% 7.58/1.48  
% 7.58/1.48  fof(f9,axiom,(
% 7.58/1.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 7.58/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.48  
% 7.58/1.48  fof(f21,plain,(
% 7.58/1.48    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 7.58/1.48    inference(ennf_transformation,[],[f9])).
% 7.58/1.48  
% 7.58/1.48  fof(f22,plain,(
% 7.58/1.48    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.58/1.48    inference(flattening,[],[f21])).
% 7.58/1.48  
% 7.58/1.48  fof(f54,plain,(
% 7.58/1.48    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.58/1.48    inference(cnf_transformation,[],[f22])).
% 7.58/1.48  
% 7.58/1.48  fof(f63,plain,(
% 7.58/1.48    ~v2_struct_0(sK3)),
% 7.58/1.48    inference(cnf_transformation,[],[f41])).
% 7.58/1.48  
% 7.58/1.48  fof(f65,plain,(
% 7.58/1.48    v4_orders_2(sK3)),
% 7.58/1.48    inference(cnf_transformation,[],[f41])).
% 7.58/1.48  
% 7.58/1.48  fof(f66,plain,(
% 7.58/1.48    v5_orders_2(sK3)),
% 7.58/1.48    inference(cnf_transformation,[],[f41])).
% 7.58/1.48  
% 7.58/1.48  fof(f67,plain,(
% 7.58/1.48    l1_orders_2(sK3)),
% 7.58/1.48    inference(cnf_transformation,[],[f41])).
% 7.58/1.48  
% 7.58/1.48  fof(f2,axiom,(
% 7.58/1.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.58/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.48  
% 7.58/1.48  fof(f45,plain,(
% 7.58/1.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.58/1.48    inference(cnf_transformation,[],[f2])).
% 7.58/1.48  
% 7.58/1.48  fof(f12,axiom,(
% 7.58/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 7.58/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.48  
% 7.58/1.48  fof(f26,plain,(
% 7.58/1.48    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 7.58/1.48    inference(ennf_transformation,[],[f12])).
% 7.58/1.48  
% 7.58/1.48  fof(f27,plain,(
% 7.58/1.48    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.58/1.48    inference(flattening,[],[f26])).
% 7.58/1.48  
% 7.58/1.48  fof(f35,plain,(
% 7.58/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.58/1.48    inference(nnf_transformation,[],[f27])).
% 7.58/1.48  
% 7.58/1.48  fof(f36,plain,(
% 7.58/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.58/1.48    inference(rectify,[],[f35])).
% 7.58/1.48  
% 7.58/1.48  fof(f38,plain,(
% 7.58/1.48    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 7.58/1.48    introduced(choice_axiom,[])).
% 7.58/1.48  
% 7.58/1.48  fof(f37,plain,(
% 7.58/1.48    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 7.58/1.48    introduced(choice_axiom,[])).
% 7.58/1.48  
% 7.58/1.48  fof(f39,plain,(
% 7.58/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK1(X1,X2,X3),X3) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK2(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.58/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).
% 7.58/1.48  
% 7.58/1.48  fof(f61,plain,(
% 7.58/1.48    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 7.58/1.48    inference(cnf_transformation,[],[f39])).
% 7.58/1.48  
% 7.58/1.48  fof(f72,plain,(
% 7.58/1.48    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_0_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 7.58/1.48    inference(equality_resolution,[],[f61])).
% 7.58/1.48  
% 7.58/1.48  fof(f7,axiom,(
% 7.58/1.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.58/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.48  
% 7.58/1.48  fof(f19,plain,(
% 7.58/1.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.58/1.48    inference(ennf_transformation,[],[f7])).
% 7.58/1.48  
% 7.58/1.48  fof(f52,plain,(
% 7.58/1.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.58/1.48    inference(cnf_transformation,[],[f19])).
% 7.58/1.48  
% 7.58/1.48  fof(f47,plain,(
% 7.58/1.48    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK0(X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.58/1.48    inference(cnf_transformation,[],[f33])).
% 7.58/1.48  
% 7.58/1.48  fof(f11,axiom,(
% 7.58/1.48    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 7.58/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.48  
% 7.58/1.48  fof(f25,plain,(
% 7.58/1.48    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 7.58/1.48    inference(ennf_transformation,[],[f11])).
% 7.58/1.48  
% 7.58/1.48  fof(f56,plain,(
% 7.58/1.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 7.58/1.48    inference(cnf_transformation,[],[f25])).
% 7.58/1.48  
% 7.58/1.48  fof(f8,axiom,(
% 7.58/1.48    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 7.58/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.58/1.48  
% 7.58/1.48  fof(f20,plain,(
% 7.58/1.48    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.58/1.48    inference(ennf_transformation,[],[f8])).
% 7.58/1.48  
% 7.58/1.48  fof(f53,plain,(
% 7.58/1.48    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.58/1.48    inference(cnf_transformation,[],[f20])).
% 7.58/1.48  
% 7.58/1.48  fof(f68,plain,(
% 7.58/1.48    u1_struct_0(sK3) != k1_orders_2(sK3,k1_struct_0(sK3))),
% 7.58/1.48    inference(cnf_transformation,[],[f41])).
% 7.58/1.48  
% 7.58/1.48  fof(f44,plain,(
% 7.58/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.58/1.48    inference(cnf_transformation,[],[f31])).
% 7.58/1.48  
% 7.58/1.48  cnf(c_13,plain,
% 7.58/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.58/1.48      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.58/1.48      | v2_struct_0(X1)
% 7.58/1.48      | ~ v3_orders_2(X1)
% 7.58/1.48      | ~ v4_orders_2(X1)
% 7.58/1.48      | ~ v5_orders_2(X1)
% 7.58/1.48      | ~ l1_orders_2(X1) ),
% 7.58/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1146,plain,
% 7.58/1.48      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.58/1.48      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.58/1.48      | v2_struct_0(X1) = iProver_top
% 7.58/1.48      | v3_orders_2(X1) != iProver_top
% 7.58/1.48      | v4_orders_2(X1) != iProver_top
% 7.58/1.48      | v5_orders_2(X1) != iProver_top
% 7.58/1.48      | l1_orders_2(X1) != iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_8,plain,
% 7.58/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.58/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1151,plain,
% 7.58/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.58/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_2641,plain,
% 7.58/1.48      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.58/1.48      | r1_tarski(k1_orders_2(X1,X0),u1_struct_0(X1)) = iProver_top
% 7.58/1.48      | v2_struct_0(X1) = iProver_top
% 7.58/1.48      | v3_orders_2(X1) != iProver_top
% 7.58/1.48      | v4_orders_2(X1) != iProver_top
% 7.58/1.48      | v5_orders_2(X1) != iProver_top
% 7.58/1.48      | l1_orders_2(X1) != iProver_top ),
% 7.58/1.48      inference(superposition,[status(thm)],[c_1146,c_1151]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_2,plain,
% 7.58/1.48      ( r1_tarski(X0,X0) ),
% 7.58/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1155,plain,
% 7.58/1.48      ( r1_tarski(X0,X0) = iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_5,plain,
% 7.58/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.58/1.48      | m1_subset_1(sK0(X2,X0),X2)
% 7.58/1.48      | r1_tarski(X2,X0) ),
% 7.58/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_7,plain,
% 7.58/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.58/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_173,plain,
% 7.58/1.48      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.58/1.48      inference(prop_impl,[status(thm)],[c_7]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_174,plain,
% 7.58/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.58/1.48      inference(renaming,[status(thm)],[c_173]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_231,plain,
% 7.58/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.48      | m1_subset_1(sK0(X0,X2),X0)
% 7.58/1.48      | ~ r1_tarski(X2,X1)
% 7.58/1.48      | r1_tarski(X0,X2) ),
% 7.58/1.48      inference(bin_hyper_res,[status(thm)],[c_5,c_174]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_357,plain,
% 7.58/1.48      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.58/1.48      inference(prop_impl,[status(thm)],[c_7]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_358,plain,
% 7.58/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.58/1.48      inference(renaming,[status(thm)],[c_357]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_418,plain,
% 7.58/1.48      ( m1_subset_1(sK0(X0,X1),X0)
% 7.58/1.48      | ~ r1_tarski(X0,X2)
% 7.58/1.48      | ~ r1_tarski(X1,X2)
% 7.58/1.48      | r1_tarski(X0,X1) ),
% 7.58/1.48      inference(bin_hyper_res,[status(thm)],[c_231,c_358]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1132,plain,
% 7.58/1.48      ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
% 7.58/1.48      | r1_tarski(X0,X2) != iProver_top
% 7.58/1.48      | r1_tarski(X1,X2) != iProver_top
% 7.58/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_3206,plain,
% 7.58/1.48      ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
% 7.58/1.48      | r1_tarski(X1,X0) != iProver_top
% 7.58/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.58/1.48      inference(superposition,[status(thm)],[c_1155,c_1132]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_25,negated_conjecture,
% 7.58/1.48      ( v3_orders_2(sK3) ),
% 7.58/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1135,plain,
% 7.58/1.48      ( v3_orders_2(sK3) = iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_6,plain,
% 7.58/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.58/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1153,plain,
% 7.58/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_12,plain,
% 7.58/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.58/1.48      | v2_struct_0(X1)
% 7.58/1.48      | ~ v3_orders_2(X1)
% 7.58/1.48      | ~ v4_orders_2(X1)
% 7.58/1.48      | ~ v5_orders_2(X1)
% 7.58/1.48      | ~ l1_orders_2(X1)
% 7.58/1.48      | a_2_0_orders_2(X1,X0) = k1_orders_2(X1,X0) ),
% 7.58/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1147,plain,
% 7.58/1.48      ( a_2_0_orders_2(X0,X1) = k1_orders_2(X0,X1)
% 7.58/1.48      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.58/1.48      | v2_struct_0(X0) = iProver_top
% 7.58/1.48      | v3_orders_2(X0) != iProver_top
% 7.58/1.48      | v4_orders_2(X0) != iProver_top
% 7.58/1.48      | v5_orders_2(X0) != iProver_top
% 7.58/1.48      | l1_orders_2(X0) != iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_2600,plain,
% 7.58/1.48      ( a_2_0_orders_2(X0,k1_xboole_0) = k1_orders_2(X0,k1_xboole_0)
% 7.58/1.48      | v2_struct_0(X0) = iProver_top
% 7.58/1.48      | v3_orders_2(X0) != iProver_top
% 7.58/1.48      | v4_orders_2(X0) != iProver_top
% 7.58/1.48      | v5_orders_2(X0) != iProver_top
% 7.58/1.48      | l1_orders_2(X0) != iProver_top ),
% 7.58/1.48      inference(superposition,[status(thm)],[c_1153,c_1147]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_4734,plain,
% 7.58/1.48      ( a_2_0_orders_2(sK3,k1_xboole_0) = k1_orders_2(sK3,k1_xboole_0)
% 7.58/1.48      | v2_struct_0(sK3) = iProver_top
% 7.58/1.48      | v4_orders_2(sK3) != iProver_top
% 7.58/1.48      | v5_orders_2(sK3) != iProver_top
% 7.58/1.48      | l1_orders_2(sK3) != iProver_top ),
% 7.58/1.48      inference(superposition,[status(thm)],[c_1135,c_2600]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_26,negated_conjecture,
% 7.58/1.48      ( ~ v2_struct_0(sK3) ),
% 7.58/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_24,negated_conjecture,
% 7.58/1.48      ( v4_orders_2(sK3) ),
% 7.58/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_23,negated_conjecture,
% 7.58/1.48      ( v5_orders_2(sK3) ),
% 7.58/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_22,negated_conjecture,
% 7.58/1.48      ( l1_orders_2(sK3) ),
% 7.58/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1491,plain,
% 7.58/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
% 7.58/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1494,plain,
% 7.58/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.58/1.48      inference(instantiation,[status(thm)],[c_1491]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1581,plain,
% 7.58/1.48      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 7.58/1.48      | v2_struct_0(X0)
% 7.58/1.48      | ~ v3_orders_2(X0)
% 7.58/1.48      | ~ v4_orders_2(X0)
% 7.58/1.48      | ~ v5_orders_2(X0)
% 7.58/1.48      | ~ l1_orders_2(X0)
% 7.58/1.48      | a_2_0_orders_2(X0,k1_xboole_0) = k1_orders_2(X0,k1_xboole_0) ),
% 7.58/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1588,plain,
% 7.58/1.48      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.58/1.48      | v2_struct_0(sK3)
% 7.58/1.48      | ~ v3_orders_2(sK3)
% 7.58/1.48      | ~ v4_orders_2(sK3)
% 7.58/1.48      | ~ v5_orders_2(sK3)
% 7.58/1.48      | ~ l1_orders_2(sK3)
% 7.58/1.48      | a_2_0_orders_2(sK3,k1_xboole_0) = k1_orders_2(sK3,k1_xboole_0) ),
% 7.58/1.48      inference(instantiation,[status(thm)],[c_1581]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_4737,plain,
% 7.58/1.48      ( a_2_0_orders_2(sK3,k1_xboole_0) = k1_orders_2(sK3,k1_xboole_0) ),
% 7.58/1.48      inference(global_propositional_subsumption,
% 7.58/1.48                [status(thm)],
% 7.58/1.48                [c_4734,c_26,c_25,c_24,c_23,c_22,c_1494,c_1588]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_3,plain,
% 7.58/1.48      ( r1_tarski(k1_xboole_0,X0) ),
% 7.58/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1154,plain,
% 7.58/1.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_16,plain,
% 7.58/1.48      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.58/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.58/1.48      | r2_hidden(X0,a_2_0_orders_2(X1,X2))
% 7.58/1.48      | r2_hidden(sK1(X1,X2,X0),X2)
% 7.58/1.48      | v2_struct_0(X1)
% 7.58/1.48      | ~ v3_orders_2(X1)
% 7.58/1.48      | ~ v4_orders_2(X1)
% 7.58/1.48      | ~ v5_orders_2(X1)
% 7.58/1.48      | ~ l1_orders_2(X1) ),
% 7.58/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1143,plain,
% 7.58/1.48      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 7.58/1.48      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.58/1.48      | r2_hidden(X0,a_2_0_orders_2(X1,X2)) = iProver_top
% 7.58/1.48      | r2_hidden(sK1(X1,X2,X0),X2) = iProver_top
% 7.58/1.48      | v2_struct_0(X1) = iProver_top
% 7.58/1.48      | v3_orders_2(X1) != iProver_top
% 7.58/1.48      | v4_orders_2(X1) != iProver_top
% 7.58/1.48      | v5_orders_2(X1) != iProver_top
% 7.58/1.48      | l1_orders_2(X1) != iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_10,plain,
% 7.58/1.48      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.58/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1149,plain,
% 7.58/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.58/1.48      | r1_tarski(X1,X0) != iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_2868,plain,
% 7.58/1.48      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 7.58/1.48      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.58/1.48      | r2_hidden(X0,a_2_0_orders_2(X1,X2)) = iProver_top
% 7.58/1.48      | r1_tarski(X2,sK1(X1,X2,X0)) != iProver_top
% 7.58/1.48      | v2_struct_0(X1) = iProver_top
% 7.58/1.48      | v3_orders_2(X1) != iProver_top
% 7.58/1.48      | v4_orders_2(X1) != iProver_top
% 7.58/1.48      | v5_orders_2(X1) != iProver_top
% 7.58/1.48      | l1_orders_2(X1) != iProver_top ),
% 7.58/1.48      inference(superposition,[status(thm)],[c_1143,c_1149]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_12285,plain,
% 7.58/1.48      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 7.58/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.58/1.48      | r2_hidden(X0,a_2_0_orders_2(X1,k1_xboole_0)) = iProver_top
% 7.58/1.48      | v2_struct_0(X1) = iProver_top
% 7.58/1.48      | v3_orders_2(X1) != iProver_top
% 7.58/1.48      | v4_orders_2(X1) != iProver_top
% 7.58/1.48      | v5_orders_2(X1) != iProver_top
% 7.58/1.48      | l1_orders_2(X1) != iProver_top ),
% 7.58/1.48      inference(superposition,[status(thm)],[c_1154,c_2868]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_14046,plain,
% 7.58/1.48      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 7.58/1.48      | r2_hidden(X0,a_2_0_orders_2(X1,k1_xboole_0)) = iProver_top
% 7.58/1.48      | v2_struct_0(X1) = iProver_top
% 7.58/1.48      | v3_orders_2(X1) != iProver_top
% 7.58/1.48      | v4_orders_2(X1) != iProver_top
% 7.58/1.48      | v5_orders_2(X1) != iProver_top
% 7.58/1.48      | l1_orders_2(X1) != iProver_top ),
% 7.58/1.48      inference(forward_subsumption_resolution,
% 7.58/1.48                [status(thm)],
% 7.58/1.48                [c_12285,c_1153]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_14050,plain,
% 7.58/1.48      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 7.58/1.48      | r2_hidden(X0,k1_orders_2(sK3,k1_xboole_0)) = iProver_top
% 7.58/1.48      | v2_struct_0(sK3) = iProver_top
% 7.58/1.48      | v3_orders_2(sK3) != iProver_top
% 7.58/1.48      | v4_orders_2(sK3) != iProver_top
% 7.58/1.48      | v5_orders_2(sK3) != iProver_top
% 7.58/1.48      | l1_orders_2(sK3) != iProver_top ),
% 7.58/1.48      inference(superposition,[status(thm)],[c_4737,c_14046]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_27,plain,
% 7.58/1.48      ( v2_struct_0(sK3) != iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_28,plain,
% 7.58/1.48      ( v3_orders_2(sK3) = iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_29,plain,
% 7.58/1.48      ( v4_orders_2(sK3) = iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_30,plain,
% 7.58/1.48      ( v5_orders_2(sK3) = iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_31,plain,
% 7.58/1.48      ( l1_orders_2(sK3) = iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_14569,plain,
% 7.58/1.48      ( r2_hidden(X0,k1_orders_2(sK3,k1_xboole_0)) = iProver_top
% 7.58/1.48      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 7.58/1.48      inference(global_propositional_subsumption,
% 7.58/1.48                [status(thm)],
% 7.58/1.48                [c_14050,c_27,c_28,c_29,c_30,c_31]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_14570,plain,
% 7.58/1.48      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 7.58/1.48      | r2_hidden(X0,k1_orders_2(sK3,k1_xboole_0)) = iProver_top ),
% 7.58/1.48      inference(renaming,[status(thm)],[c_14569]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_4,plain,
% 7.58/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.58/1.48      | ~ r2_hidden(sK0(X2,X0),X0)
% 7.58/1.48      | r1_tarski(X2,X0) ),
% 7.58/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_230,plain,
% 7.58/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.48      | ~ r2_hidden(sK0(X0,X2),X2)
% 7.58/1.48      | ~ r1_tarski(X2,X1)
% 7.58/1.48      | r1_tarski(X0,X2) ),
% 7.58/1.48      inference(bin_hyper_res,[status(thm)],[c_4,c_174]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_417,plain,
% 7.58/1.48      ( ~ r2_hidden(sK0(X0,X1),X1)
% 7.58/1.48      | ~ r1_tarski(X0,X2)
% 7.58/1.48      | ~ r1_tarski(X1,X2)
% 7.58/1.48      | r1_tarski(X0,X1) ),
% 7.58/1.48      inference(bin_hyper_res,[status(thm)],[c_230,c_358]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1133,plain,
% 7.58/1.48      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.58/1.48      | r1_tarski(X0,X2) != iProver_top
% 7.58/1.48      | r1_tarski(X1,X2) != iProver_top
% 7.58/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_14579,plain,
% 7.58/1.48      ( m1_subset_1(sK0(X0,k1_orders_2(sK3,k1_xboole_0)),u1_struct_0(sK3)) != iProver_top
% 7.58/1.48      | r1_tarski(X0,X1) != iProver_top
% 7.58/1.48      | r1_tarski(X0,k1_orders_2(sK3,k1_xboole_0)) = iProver_top
% 7.58/1.48      | r1_tarski(k1_orders_2(sK3,k1_xboole_0),X1) != iProver_top ),
% 7.58/1.48      inference(superposition,[status(thm)],[c_14570,c_1133]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_15073,plain,
% 7.58/1.48      ( r1_tarski(k1_orders_2(sK3,k1_xboole_0),X0) != iProver_top
% 7.58/1.48      | r1_tarski(k1_orders_2(sK3,k1_xboole_0),u1_struct_0(sK3)) != iProver_top
% 7.58/1.48      | r1_tarski(u1_struct_0(sK3),X0) != iProver_top
% 7.58/1.48      | r1_tarski(u1_struct_0(sK3),k1_orders_2(sK3,k1_xboole_0)) = iProver_top ),
% 7.58/1.48      inference(superposition,[status(thm)],[c_3206,c_14579]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1493,plain,
% 7.58/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_1491]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1495,plain,
% 7.58/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.58/1.48      inference(instantiation,[status(thm)],[c_1493]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1582,plain,
% 7.58/1.48      ( m1_subset_1(k1_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
% 7.58/1.48      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 7.58/1.48      | v2_struct_0(X0)
% 7.58/1.48      | ~ v3_orders_2(X0)
% 7.58/1.48      | ~ v4_orders_2(X0)
% 7.58/1.48      | ~ v5_orders_2(X0)
% 7.58/1.48      | ~ l1_orders_2(X0) ),
% 7.58/1.48      inference(instantiation,[status(thm)],[c_13]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1583,plain,
% 7.58/1.48      ( m1_subset_1(k1_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.58/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.58/1.48      | v2_struct_0(X0) = iProver_top
% 7.58/1.48      | v3_orders_2(X0) != iProver_top
% 7.58/1.48      | v4_orders_2(X0) != iProver_top
% 7.58/1.48      | v5_orders_2(X0) != iProver_top
% 7.58/1.48      | l1_orders_2(X0) != iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_1582]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1585,plain,
% 7.58/1.48      ( m1_subset_1(k1_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.58/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.58/1.48      | v2_struct_0(sK3) = iProver_top
% 7.58/1.48      | v3_orders_2(sK3) != iProver_top
% 7.58/1.48      | v4_orders_2(sK3) != iProver_top
% 7.58/1.48      | v5_orders_2(sK3) != iProver_top
% 7.58/1.48      | l1_orders_2(sK3) != iProver_top ),
% 7.58/1.48      inference(instantiation,[status(thm)],[c_1583]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1616,plain,
% 7.58/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.58/1.48      | r1_tarski(X0,u1_struct_0(X1)) ),
% 7.58/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_2021,plain,
% 7.58/1.48      ( ~ m1_subset_1(k1_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
% 7.58/1.48      | r1_tarski(k1_orders_2(X0,k1_xboole_0),u1_struct_0(X0)) ),
% 7.58/1.48      inference(instantiation,[status(thm)],[c_1616]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_2042,plain,
% 7.58/1.48      ( m1_subset_1(k1_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.58/1.48      | r1_tarski(k1_orders_2(X0,k1_xboole_0),u1_struct_0(X0)) = iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_2021]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_2044,plain,
% 7.58/1.48      ( m1_subset_1(k1_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.58/1.48      | r1_tarski(k1_orders_2(sK3,k1_xboole_0),u1_struct_0(sK3)) = iProver_top ),
% 7.58/1.48      inference(instantiation,[status(thm)],[c_2042]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1138,plain,
% 7.58/1.48      ( l1_orders_2(sK3) = iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_14,plain,
% 7.58/1.48      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 7.58/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1145,plain,
% 7.58/1.48      ( l1_orders_2(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1768,plain,
% 7.58/1.48      ( l1_struct_0(sK3) = iProver_top ),
% 7.58/1.48      inference(superposition,[status(thm)],[c_1138,c_1145]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_11,plain,
% 7.58/1.48      ( ~ l1_struct_0(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 7.58/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1148,plain,
% 7.58/1.48      ( k1_struct_0(X0) = k1_xboole_0 | l1_struct_0(X0) != iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1876,plain,
% 7.58/1.48      ( k1_struct_0(sK3) = k1_xboole_0 ),
% 7.58/1.48      inference(superposition,[status(thm)],[c_1768,c_1148]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_21,negated_conjecture,
% 7.58/1.48      ( u1_struct_0(sK3) != k1_orders_2(sK3,k1_struct_0(sK3)) ),
% 7.58/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_2080,plain,
% 7.58/1.48      ( k1_orders_2(sK3,k1_xboole_0) != u1_struct_0(sK3) ),
% 7.58/1.48      inference(demodulation,[status(thm)],[c_1876,c_21]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_0,plain,
% 7.58/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.58/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_2270,plain,
% 7.58/1.48      ( ~ r1_tarski(X0,u1_struct_0(X1))
% 7.58/1.48      | ~ r1_tarski(u1_struct_0(X1),X0)
% 7.58/1.48      | X0 = u1_struct_0(X1) ),
% 7.58/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_5523,plain,
% 7.58/1.48      ( ~ r1_tarski(k1_orders_2(X0,k1_xboole_0),u1_struct_0(X0))
% 7.58/1.48      | ~ r1_tarski(u1_struct_0(X0),k1_orders_2(X0,k1_xboole_0))
% 7.58/1.48      | k1_orders_2(X0,k1_xboole_0) = u1_struct_0(X0) ),
% 7.58/1.48      inference(instantiation,[status(thm)],[c_2270]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_5524,plain,
% 7.58/1.48      ( k1_orders_2(X0,k1_xboole_0) = u1_struct_0(X0)
% 7.58/1.48      | r1_tarski(k1_orders_2(X0,k1_xboole_0),u1_struct_0(X0)) != iProver_top
% 7.58/1.48      | r1_tarski(u1_struct_0(X0),k1_orders_2(X0,k1_xboole_0)) != iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_5523]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_5526,plain,
% 7.58/1.48      ( k1_orders_2(sK3,k1_xboole_0) = u1_struct_0(sK3)
% 7.58/1.48      | r1_tarski(k1_orders_2(sK3,k1_xboole_0),u1_struct_0(sK3)) != iProver_top
% 7.58/1.48      | r1_tarski(u1_struct_0(sK3),k1_orders_2(sK3,k1_xboole_0)) != iProver_top ),
% 7.58/1.48      inference(instantiation,[status(thm)],[c_5524]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_16540,plain,
% 7.58/1.48      ( r1_tarski(u1_struct_0(sK3),X0) != iProver_top
% 7.58/1.48      | r1_tarski(k1_orders_2(sK3,k1_xboole_0),X0) != iProver_top ),
% 7.58/1.48      inference(global_propositional_subsumption,
% 7.58/1.48                [status(thm)],
% 7.58/1.48                [c_15073,c_27,c_28,c_29,c_30,c_31,c_1495,c_1585,c_2044,
% 7.58/1.48                 c_2080,c_5526]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_16541,plain,
% 7.58/1.48      ( r1_tarski(k1_orders_2(sK3,k1_xboole_0),X0) != iProver_top
% 7.58/1.48      | r1_tarski(u1_struct_0(sK3),X0) != iProver_top ),
% 7.58/1.48      inference(renaming,[status(thm)],[c_16540]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_16549,plain,
% 7.58/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.58/1.48      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 7.58/1.48      | v2_struct_0(sK3) = iProver_top
% 7.58/1.48      | v3_orders_2(sK3) != iProver_top
% 7.58/1.48      | v4_orders_2(sK3) != iProver_top
% 7.58/1.48      | v5_orders_2(sK3) != iProver_top
% 7.58/1.48      | l1_orders_2(sK3) != iProver_top ),
% 7.58/1.48      inference(superposition,[status(thm)],[c_2641,c_16541]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1626,plain,
% 7.58/1.48      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 7.58/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1631,plain,
% 7.58/1.48      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
% 7.58/1.48      inference(predicate_to_equality,[status(thm)],[c_1626]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(c_1633,plain,
% 7.58/1.48      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 7.58/1.48      inference(instantiation,[status(thm)],[c_1631]) ).
% 7.58/1.48  
% 7.58/1.48  cnf(contradiction,plain,
% 7.58/1.48      ( $false ),
% 7.58/1.48      inference(minisat,
% 7.58/1.48                [status(thm)],
% 7.58/1.48                [c_16549,c_1633,c_1495,c_31,c_30,c_29,c_28,c_27]) ).
% 7.58/1.48  
% 7.58/1.48  
% 7.58/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.58/1.48  
% 7.58/1.48  ------                               Statistics
% 7.58/1.48  
% 7.58/1.48  ------ Selected
% 7.58/1.48  
% 7.58/1.48  total_time:                             0.517
% 7.58/1.48  
%------------------------------------------------------------------------------
