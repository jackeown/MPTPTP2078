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
% DateTime   : Thu Dec  3 12:12:09 EST 2020

% Result     : Theorem 7.63s
% Output     : CNFRefutation 7.63s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 407 expanded)
%              Number of clauses        :   96 ( 146 expanded)
%              Number of leaves         :   19 (  81 expanded)
%              Depth                    :   21
%              Number of atoms          :  612 (1822 expanded)
%              Number of equality atoms :  223 ( 422 expanded)
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
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
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
     => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f28,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f40,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3))
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3))
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
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
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
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
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
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
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
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
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
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X3,X4)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X5,X6)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
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
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK2(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
                & r2_hidden(sK1(X1,X2,X3),X2)
                & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK2(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK2(X0,X1,X2) = X0
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
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
      ( r2_hidden(X3,a_2_1_orders_2(X1,X2))
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

fof(f68,plain,(
    u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1142,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
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

cnf(c_1147,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2669,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_orders_2(X1,X0),u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1142,c_1147])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1151,plain,
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

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X0,X2),X0)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_174])).

cnf(c_356,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_357,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_356])).

cnf(c_416,plain,
    ( m1_subset_1(sK0(X0,X1),X0)
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_230,c_357])).

cnf(c_1128,plain,
    ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_3178,plain,
    ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_1128])).

cnf(c_25,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1131,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1149,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1143,plain,
    ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2628,plain,
    ( a_2_1_orders_2(X0,k1_xboole_0) = k2_orders_2(X0,k1_xboole_0)
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1149,c_1143])).

cnf(c_4707,plain,
    ( a_2_1_orders_2(sK3,k1_xboole_0) = k2_orders_2(sK3,k1_xboole_0)
    | v2_struct_0(sK3) = iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1131,c_2628])).

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

cnf(c_1487,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1493,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1487])).

cnf(c_1490,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | a_2_1_orders_2(X0,k1_xboole_0) = k2_orders_2(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1501,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_1_orders_2(sK3,k1_xboole_0) = k2_orders_2(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1490])).

cnf(c_4710,plain,
    ( a_2_1_orders_2(sK3,k1_xboole_0) = k2_orders_2(sK3,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4707,c_26,c_25,c_24,c_23,c_22,c_1493,c_1501])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1150,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1139,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,X2)) = iProver_top
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

cnf(c_1145,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2873,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,X2)) = iProver_top
    | r1_tarski(X2,sK1(X1,X2,X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1145])).

cnf(c_12504,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_2873])).

cnf(c_14290,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12504,c_1149])).

cnf(c_14294,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k1_xboole_0)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4710,c_14290])).

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

cnf(c_14831,plain,
    ( r2_hidden(X0,k2_orders_2(sK3,k1_xboole_0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14294,c_27,c_28,c_29,c_30,c_31])).

cnf(c_14832,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k2_orders_2(sK3,k1_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_14831])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X2,X0),X0)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X0,X2),X2)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_174])).

cnf(c_415,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_229,c_357])).

cnf(c_1129,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_415])).

cnf(c_14841,plain,
    ( m1_subset_1(sK0(X0,k2_orders_2(sK3,k1_xboole_0)),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_orders_2(sK3,k1_xboole_0)) = iProver_top
    | r1_tarski(k2_orders_2(sK3,k1_xboole_0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_14832,c_1129])).

cnf(c_15273,plain,
    ( r1_tarski(k2_orders_2(sK3,k1_xboole_0),X0) != iProver_top
    | r1_tarski(k2_orders_2(sK3,k1_xboole_0),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(u1_struct_0(sK3),X0) != iProver_top
    | r1_tarski(u1_struct_0(sK3),k2_orders_2(sK3,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3178,c_14841])).

cnf(c_21,negated_conjecture,
    ( u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_14,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_51,plain,
    ( ~ l1_orders_2(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_11,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_60,plain,
    ( ~ l1_struct_0(sK3)
    | k1_struct_0(sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_83,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_87,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_492,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_505,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_1492,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1487])).

cnf(c_1494,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1492])).

cnf(c_1491,plain,
    ( m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1496,plain,
    ( m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1491])).

cnf(c_1498,plain,
    ( m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_485,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1442,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) != X0
    | u1_struct_0(sK3) != X0
    | u1_struct_0(sK3) = k2_orders_2(sK3,k1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_1582,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) != u1_struct_0(sK3)
    | u1_struct_0(sK3) = k2_orders_2(sK3,k1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1442])).

cnf(c_1613,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1894,plain,
    ( ~ m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
    | r1_tarski(k2_orders_2(X0,k1_xboole_0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1613])).

cnf(c_1895,plain,
    ( m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(k2_orders_2(X0,k1_xboole_0),u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1894])).

cnf(c_1897,plain,
    ( m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k2_orders_2(sK3,k1_xboole_0),u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1895])).

cnf(c_491,plain,
    ( X0 != X1
    | X2 != X3
    | k2_orders_2(X0,X2) = k2_orders_2(X1,X3) ),
    theory(equality)).

cnf(c_2222,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(X0,X1)
    | k1_struct_0(sK3) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_2969,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(X0,k1_xboole_0)
    | k1_struct_0(sK3) != k1_xboole_0
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_2222])).

cnf(c_2971,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(sK3,k1_xboole_0)
    | k1_struct_0(sK3) != k1_xboole_0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2969])).

cnf(c_1806,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) != X0
    | k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(X1)
    | u1_struct_0(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_5167,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(X0,k1_xboole_0)
    | k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(X1)
    | u1_struct_0(X1) != k2_orders_2(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1806])).

cnf(c_5174,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(sK3,k1_xboole_0)
    | k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3)
    | u1_struct_0(sK3) != k2_orders_2(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5167])).

cnf(c_1577,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),X0)
    | u1_struct_0(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_15206,plain,
    ( ~ r1_tarski(k2_orders_2(sK3,k1_xboole_0),u1_struct_0(sK3))
    | ~ r1_tarski(u1_struct_0(sK3),k2_orders_2(sK3,k1_xboole_0))
    | u1_struct_0(sK3) = k2_orders_2(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1577])).

cnf(c_15207,plain,
    ( u1_struct_0(sK3) = k2_orders_2(sK3,k1_xboole_0)
    | r1_tarski(k2_orders_2(sK3,k1_xboole_0),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(u1_struct_0(sK3),k2_orders_2(sK3,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15206])).

cnf(c_16593,plain,
    ( r1_tarski(u1_struct_0(sK3),X0) != iProver_top
    | r1_tarski(k2_orders_2(sK3,k1_xboole_0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15273,c_27,c_28,c_29,c_30,c_22,c_31,c_21,c_51,c_60,c_83,c_87,c_505,c_1494,c_1498,c_1582,c_1897,c_2971,c_5174,c_15207])).

cnf(c_16594,plain,
    ( r1_tarski(k2_orders_2(sK3,k1_xboole_0),X0) != iProver_top
    | r1_tarski(u1_struct_0(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16593])).

cnf(c_16602,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2669,c_16594])).

cnf(c_1623,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1628,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1623])).

cnf(c_1630,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1628])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16602,c_1630,c_1494,c_31,c_30,c_29,c_28,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n006.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 12:48:52 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 7.63/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.63/1.47  
% 7.63/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.63/1.47  
% 7.63/1.47  ------  iProver source info
% 7.63/1.47  
% 7.63/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.63/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.63/1.47  git: non_committed_changes: false
% 7.63/1.47  git: last_make_outside_of_git: false
% 7.63/1.47  
% 7.63/1.47  ------ 
% 7.63/1.47  ------ Parsing...
% 7.63/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.63/1.47  
% 7.63/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.63/1.47  
% 7.63/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.63/1.47  
% 7.63/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.63/1.47  ------ Proving...
% 7.63/1.47  ------ Problem Properties 
% 7.63/1.47  
% 7.63/1.47  
% 7.63/1.47  clauses                                 26
% 7.63/1.47  conjectures                             6
% 7.63/1.47  EPR                                     10
% 7.63/1.47  Horn                                    17
% 7.63/1.47  unary                                   9
% 7.63/1.47  binary                                  5
% 7.63/1.47  lits                                    100
% 7.63/1.47  lits eq                                 5
% 7.63/1.47  fd_pure                                 0
% 7.63/1.47  fd_pseudo                               0
% 7.63/1.47  fd_cond                                 0
% 7.63/1.47  fd_pseudo_cond                          1
% 7.63/1.47  AC symbols                              0
% 7.63/1.47  
% 7.63/1.47  ------ Input Options Time Limit: Unbounded
% 7.63/1.47  
% 7.63/1.47  
% 7.63/1.47  ------ 
% 7.63/1.47  Current options:
% 7.63/1.47  ------ 
% 7.63/1.47  
% 7.63/1.47  
% 7.63/1.47  
% 7.63/1.47  
% 7.63/1.47  ------ Proving...
% 7.63/1.47  
% 7.63/1.47  
% 7.63/1.47  % SZS status Theorem for theBenchmark.p
% 7.63/1.47  
% 7.63/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.63/1.47  
% 7.63/1.47  fof(f10,axiom,(
% 7.63/1.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.63/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.47  
% 7.63/1.47  fof(f23,plain,(
% 7.63/1.47    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 7.63/1.47    inference(ennf_transformation,[],[f10])).
% 7.63/1.47  
% 7.63/1.47  fof(f24,plain,(
% 7.63/1.47    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.63/1.47    inference(flattening,[],[f23])).
% 7.63/1.47  
% 7.63/1.47  fof(f55,plain,(
% 7.63/1.47    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.63/1.47    inference(cnf_transformation,[],[f24])).
% 7.63/1.47  
% 7.63/1.47  fof(f5,axiom,(
% 7.63/1.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.63/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.47  
% 7.63/1.47  fof(f34,plain,(
% 7.63/1.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.63/1.47    inference(nnf_transformation,[],[f5])).
% 7.63/1.47  
% 7.63/1.47  fof(f49,plain,(
% 7.63/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.63/1.47    inference(cnf_transformation,[],[f34])).
% 7.63/1.47  
% 7.63/1.47  fof(f1,axiom,(
% 7.63/1.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.63/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.47  
% 7.63/1.47  fof(f30,plain,(
% 7.63/1.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.63/1.47    inference(nnf_transformation,[],[f1])).
% 7.63/1.47  
% 7.63/1.47  fof(f31,plain,(
% 7.63/1.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.63/1.47    inference(flattening,[],[f30])).
% 7.63/1.47  
% 7.63/1.47  fof(f42,plain,(
% 7.63/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.63/1.47    inference(cnf_transformation,[],[f31])).
% 7.63/1.47  
% 7.63/1.47  fof(f70,plain,(
% 7.63/1.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.63/1.47    inference(equality_resolution,[],[f42])).
% 7.63/1.47  
% 7.63/1.47  fof(f3,axiom,(
% 7.63/1.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X1) => r2_hidden(X3,X2)) => r1_tarski(X1,X2))))),
% 7.63/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.47  
% 7.63/1.47  fof(f15,plain,(
% 7.63/1.47    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & m1_subset_1(X3,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.63/1.47    inference(ennf_transformation,[],[f3])).
% 7.63/1.47  
% 7.63/1.47  fof(f16,plain,(
% 7.63/1.47    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & m1_subset_1(X3,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.63/1.47    inference(flattening,[],[f15])).
% 7.63/1.47  
% 7.63/1.47  fof(f32,plain,(
% 7.63/1.47    ! [X2,X1] : (? [X3] : (~r2_hidden(X3,X2) & m1_subset_1(X3,X1)) => (~r2_hidden(sK0(X1,X2),X2) & m1_subset_1(sK0(X1,X2),X1)))),
% 7.63/1.47    introduced(choice_axiom,[])).
% 7.63/1.47  
% 7.63/1.47  fof(f33,plain,(
% 7.63/1.47    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK0(X1,X2),X2) & m1_subset_1(sK0(X1,X2),X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.63/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f32])).
% 7.63/1.47  
% 7.63/1.47  fof(f46,plain,(
% 7.63/1.47    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | m1_subset_1(sK0(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.63/1.47    inference(cnf_transformation,[],[f33])).
% 7.63/1.47  
% 7.63/1.47  fof(f50,plain,(
% 7.63/1.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.63/1.47    inference(cnf_transformation,[],[f34])).
% 7.63/1.47  
% 7.63/1.47  fof(f13,conjecture,(
% 7.63/1.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 7.63/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.47  
% 7.63/1.47  fof(f14,negated_conjecture,(
% 7.63/1.47    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 7.63/1.47    inference(negated_conjecture,[],[f13])).
% 7.63/1.47  
% 7.63/1.47  fof(f28,plain,(
% 7.63/1.47    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 7.63/1.47    inference(ennf_transformation,[],[f14])).
% 7.63/1.47  
% 7.63/1.47  fof(f29,plain,(
% 7.63/1.47    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 7.63/1.47    inference(flattening,[],[f28])).
% 7.63/1.47  
% 7.63/1.47  fof(f40,plain,(
% 7.63/1.47    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 7.63/1.47    introduced(choice_axiom,[])).
% 7.63/1.47  
% 7.63/1.47  fof(f41,plain,(
% 7.63/1.47    u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 7.63/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f40])).
% 7.63/1.47  
% 7.63/1.47  fof(f64,plain,(
% 7.63/1.47    v3_orders_2(sK3)),
% 7.63/1.47    inference(cnf_transformation,[],[f41])).
% 7.63/1.47  
% 7.63/1.47  fof(f4,axiom,(
% 7.63/1.47    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.63/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.47  
% 7.63/1.47  fof(f48,plain,(
% 7.63/1.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.63/1.47    inference(cnf_transformation,[],[f4])).
% 7.63/1.47  
% 7.63/1.47  fof(f9,axiom,(
% 7.63/1.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 7.63/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.47  
% 7.63/1.47  fof(f21,plain,(
% 7.63/1.47    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 7.63/1.47    inference(ennf_transformation,[],[f9])).
% 7.63/1.47  
% 7.63/1.47  fof(f22,plain,(
% 7.63/1.47    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.63/1.47    inference(flattening,[],[f21])).
% 7.63/1.47  
% 7.63/1.47  fof(f54,plain,(
% 7.63/1.47    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.63/1.47    inference(cnf_transformation,[],[f22])).
% 7.63/1.47  
% 7.63/1.47  fof(f63,plain,(
% 7.63/1.47    ~v2_struct_0(sK3)),
% 7.63/1.47    inference(cnf_transformation,[],[f41])).
% 7.63/1.47  
% 7.63/1.47  fof(f65,plain,(
% 7.63/1.47    v4_orders_2(sK3)),
% 7.63/1.47    inference(cnf_transformation,[],[f41])).
% 7.63/1.47  
% 7.63/1.47  fof(f66,plain,(
% 7.63/1.47    v5_orders_2(sK3)),
% 7.63/1.47    inference(cnf_transformation,[],[f41])).
% 7.63/1.47  
% 7.63/1.47  fof(f67,plain,(
% 7.63/1.47    l1_orders_2(sK3)),
% 7.63/1.47    inference(cnf_transformation,[],[f41])).
% 7.63/1.47  
% 7.63/1.47  fof(f2,axiom,(
% 7.63/1.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.63/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.47  
% 7.63/1.47  fof(f45,plain,(
% 7.63/1.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.63/1.47    inference(cnf_transformation,[],[f2])).
% 7.63/1.47  
% 7.63/1.47  fof(f12,axiom,(
% 7.63/1.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 7.63/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.47  
% 7.63/1.47  fof(f26,plain,(
% 7.63/1.47    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 7.63/1.47    inference(ennf_transformation,[],[f12])).
% 7.63/1.47  
% 7.63/1.47  fof(f27,plain,(
% 7.63/1.47    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.63/1.47    inference(flattening,[],[f26])).
% 7.63/1.47  
% 7.63/1.47  fof(f35,plain,(
% 7.63/1.47    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.63/1.47    inference(nnf_transformation,[],[f27])).
% 7.63/1.47  
% 7.63/1.47  fof(f36,plain,(
% 7.63/1.47    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.63/1.47    inference(rectify,[],[f35])).
% 7.63/1.47  
% 7.63/1.47  fof(f38,plain,(
% 7.63/1.47    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 7.63/1.47    introduced(choice_axiom,[])).
% 7.63/1.47  
% 7.63/1.47  fof(f37,plain,(
% 7.63/1.47    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 7.63/1.47    introduced(choice_axiom,[])).
% 7.63/1.47  
% 7.63/1.47  fof(f39,plain,(
% 7.63/1.47    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 7.63/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).
% 7.63/1.47  
% 7.63/1.47  fof(f61,plain,(
% 7.63/1.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 7.63/1.47    inference(cnf_transformation,[],[f39])).
% 7.63/1.47  
% 7.63/1.47  fof(f72,plain,(
% 7.63/1.47    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 7.63/1.47    inference(equality_resolution,[],[f61])).
% 7.63/1.47  
% 7.63/1.47  fof(f7,axiom,(
% 7.63/1.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.63/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.47  
% 7.63/1.47  fof(f19,plain,(
% 7.63/1.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.63/1.47    inference(ennf_transformation,[],[f7])).
% 7.63/1.47  
% 7.63/1.47  fof(f52,plain,(
% 7.63/1.47    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.63/1.47    inference(cnf_transformation,[],[f19])).
% 7.63/1.47  
% 7.63/1.47  fof(f47,plain,(
% 7.63/1.47    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK0(X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.63/1.47    inference(cnf_transformation,[],[f33])).
% 7.63/1.47  
% 7.63/1.47  fof(f68,plain,(
% 7.63/1.47    u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3))),
% 7.63/1.47    inference(cnf_transformation,[],[f41])).
% 7.63/1.47  
% 7.63/1.47  fof(f11,axiom,(
% 7.63/1.47    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 7.63/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.47  
% 7.63/1.47  fof(f25,plain,(
% 7.63/1.47    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 7.63/1.47    inference(ennf_transformation,[],[f11])).
% 7.63/1.47  
% 7.63/1.47  fof(f56,plain,(
% 7.63/1.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 7.63/1.47    inference(cnf_transformation,[],[f25])).
% 7.63/1.47  
% 7.63/1.47  fof(f8,axiom,(
% 7.63/1.47    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 7.63/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.47  
% 7.63/1.47  fof(f20,plain,(
% 7.63/1.47    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.63/1.47    inference(ennf_transformation,[],[f8])).
% 7.63/1.47  
% 7.63/1.47  fof(f53,plain,(
% 7.63/1.47    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.63/1.47    inference(cnf_transformation,[],[f20])).
% 7.63/1.47  
% 7.63/1.47  fof(f44,plain,(
% 7.63/1.47    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.63/1.47    inference(cnf_transformation,[],[f31])).
% 7.63/1.47  
% 7.63/1.47  cnf(c_13,plain,
% 7.63/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.63/1.47      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.63/1.47      | v2_struct_0(X1)
% 7.63/1.47      | ~ v3_orders_2(X1)
% 7.63/1.47      | ~ v4_orders_2(X1)
% 7.63/1.47      | ~ v5_orders_2(X1)
% 7.63/1.47      | ~ l1_orders_2(X1) ),
% 7.63/1.47      inference(cnf_transformation,[],[f55]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1142,plain,
% 7.63/1.47      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.63/1.47      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.63/1.47      | v2_struct_0(X1) = iProver_top
% 7.63/1.47      | v3_orders_2(X1) != iProver_top
% 7.63/1.47      | v4_orders_2(X1) != iProver_top
% 7.63/1.47      | v5_orders_2(X1) != iProver_top
% 7.63/1.47      | l1_orders_2(X1) != iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_8,plain,
% 7.63/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.63/1.47      inference(cnf_transformation,[],[f49]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1147,plain,
% 7.63/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.63/1.47      | r1_tarski(X0,X1) = iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_2669,plain,
% 7.63/1.47      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.63/1.47      | r1_tarski(k2_orders_2(X1,X0),u1_struct_0(X1)) = iProver_top
% 7.63/1.47      | v2_struct_0(X1) = iProver_top
% 7.63/1.47      | v3_orders_2(X1) != iProver_top
% 7.63/1.47      | v4_orders_2(X1) != iProver_top
% 7.63/1.47      | v5_orders_2(X1) != iProver_top
% 7.63/1.47      | l1_orders_2(X1) != iProver_top ),
% 7.63/1.47      inference(superposition,[status(thm)],[c_1142,c_1147]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_2,plain,
% 7.63/1.47      ( r1_tarski(X0,X0) ),
% 7.63/1.47      inference(cnf_transformation,[],[f70]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1151,plain,
% 7.63/1.47      ( r1_tarski(X0,X0) = iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_5,plain,
% 7.63/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.63/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.63/1.47      | m1_subset_1(sK0(X2,X0),X2)
% 7.63/1.47      | r1_tarski(X2,X0) ),
% 7.63/1.47      inference(cnf_transformation,[],[f46]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_7,plain,
% 7.63/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.63/1.47      inference(cnf_transformation,[],[f50]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_173,plain,
% 7.63/1.47      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.63/1.47      inference(prop_impl,[status(thm)],[c_7]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_174,plain,
% 7.63/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.63/1.47      inference(renaming,[status(thm)],[c_173]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_230,plain,
% 7.63/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.63/1.47      | m1_subset_1(sK0(X0,X2),X0)
% 7.63/1.47      | ~ r1_tarski(X2,X1)
% 7.63/1.47      | r1_tarski(X0,X2) ),
% 7.63/1.47      inference(bin_hyper_res,[status(thm)],[c_5,c_174]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_356,plain,
% 7.63/1.47      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.63/1.47      inference(prop_impl,[status(thm)],[c_7]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_357,plain,
% 7.63/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.63/1.47      inference(renaming,[status(thm)],[c_356]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_416,plain,
% 7.63/1.47      ( m1_subset_1(sK0(X0,X1),X0)
% 7.63/1.47      | ~ r1_tarski(X0,X2)
% 7.63/1.47      | ~ r1_tarski(X1,X2)
% 7.63/1.47      | r1_tarski(X0,X1) ),
% 7.63/1.47      inference(bin_hyper_res,[status(thm)],[c_230,c_357]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1128,plain,
% 7.63/1.47      ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
% 7.63/1.47      | r1_tarski(X0,X2) != iProver_top
% 7.63/1.47      | r1_tarski(X1,X2) != iProver_top
% 7.63/1.47      | r1_tarski(X0,X1) = iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_3178,plain,
% 7.63/1.47      ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
% 7.63/1.47      | r1_tarski(X1,X0) != iProver_top
% 7.63/1.47      | r1_tarski(X0,X1) = iProver_top ),
% 7.63/1.47      inference(superposition,[status(thm)],[c_1151,c_1128]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_25,negated_conjecture,
% 7.63/1.47      ( v3_orders_2(sK3) ),
% 7.63/1.47      inference(cnf_transformation,[],[f64]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1131,plain,
% 7.63/1.47      ( v3_orders_2(sK3) = iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_6,plain,
% 7.63/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.63/1.47      inference(cnf_transformation,[],[f48]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1149,plain,
% 7.63/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_12,plain,
% 7.63/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.63/1.47      | v2_struct_0(X1)
% 7.63/1.47      | ~ v3_orders_2(X1)
% 7.63/1.47      | ~ v4_orders_2(X1)
% 7.63/1.47      | ~ v5_orders_2(X1)
% 7.63/1.47      | ~ l1_orders_2(X1)
% 7.63/1.47      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 7.63/1.47      inference(cnf_transformation,[],[f54]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1143,plain,
% 7.63/1.47      ( a_2_1_orders_2(X0,X1) = k2_orders_2(X0,X1)
% 7.63/1.47      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.63/1.47      | v2_struct_0(X0) = iProver_top
% 7.63/1.47      | v3_orders_2(X0) != iProver_top
% 7.63/1.47      | v4_orders_2(X0) != iProver_top
% 7.63/1.47      | v5_orders_2(X0) != iProver_top
% 7.63/1.47      | l1_orders_2(X0) != iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_2628,plain,
% 7.63/1.47      ( a_2_1_orders_2(X0,k1_xboole_0) = k2_orders_2(X0,k1_xboole_0)
% 7.63/1.47      | v2_struct_0(X0) = iProver_top
% 7.63/1.47      | v3_orders_2(X0) != iProver_top
% 7.63/1.47      | v4_orders_2(X0) != iProver_top
% 7.63/1.47      | v5_orders_2(X0) != iProver_top
% 7.63/1.47      | l1_orders_2(X0) != iProver_top ),
% 7.63/1.47      inference(superposition,[status(thm)],[c_1149,c_1143]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_4707,plain,
% 7.63/1.47      ( a_2_1_orders_2(sK3,k1_xboole_0) = k2_orders_2(sK3,k1_xboole_0)
% 7.63/1.47      | v2_struct_0(sK3) = iProver_top
% 7.63/1.47      | v4_orders_2(sK3) != iProver_top
% 7.63/1.47      | v5_orders_2(sK3) != iProver_top
% 7.63/1.47      | l1_orders_2(sK3) != iProver_top ),
% 7.63/1.47      inference(superposition,[status(thm)],[c_1131,c_2628]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_26,negated_conjecture,
% 7.63/1.47      ( ~ v2_struct_0(sK3) ),
% 7.63/1.47      inference(cnf_transformation,[],[f63]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_24,negated_conjecture,
% 7.63/1.47      ( v4_orders_2(sK3) ),
% 7.63/1.47      inference(cnf_transformation,[],[f65]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_23,negated_conjecture,
% 7.63/1.47      ( v5_orders_2(sK3) ),
% 7.63/1.47      inference(cnf_transformation,[],[f66]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_22,negated_conjecture,
% 7.63/1.47      ( l1_orders_2(sK3) ),
% 7.63/1.47      inference(cnf_transformation,[],[f67]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1487,plain,
% 7.63/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_6]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1493,plain,
% 7.63/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_1487]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1490,plain,
% 7.63/1.47      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 7.63/1.47      | v2_struct_0(X0)
% 7.63/1.47      | ~ v3_orders_2(X0)
% 7.63/1.47      | ~ v4_orders_2(X0)
% 7.63/1.47      | ~ v5_orders_2(X0)
% 7.63/1.47      | ~ l1_orders_2(X0)
% 7.63/1.47      | a_2_1_orders_2(X0,k1_xboole_0) = k2_orders_2(X0,k1_xboole_0) ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_12]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1501,plain,
% 7.63/1.47      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.63/1.47      | v2_struct_0(sK3)
% 7.63/1.47      | ~ v3_orders_2(sK3)
% 7.63/1.47      | ~ v4_orders_2(sK3)
% 7.63/1.47      | ~ v5_orders_2(sK3)
% 7.63/1.47      | ~ l1_orders_2(sK3)
% 7.63/1.47      | a_2_1_orders_2(sK3,k1_xboole_0) = k2_orders_2(sK3,k1_xboole_0) ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_1490]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_4710,plain,
% 7.63/1.47      ( a_2_1_orders_2(sK3,k1_xboole_0) = k2_orders_2(sK3,k1_xboole_0) ),
% 7.63/1.47      inference(global_propositional_subsumption,
% 7.63/1.47                [status(thm)],
% 7.63/1.47                [c_4707,c_26,c_25,c_24,c_23,c_22,c_1493,c_1501]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_3,plain,
% 7.63/1.47      ( r1_tarski(k1_xboole_0,X0) ),
% 7.63/1.47      inference(cnf_transformation,[],[f45]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1150,plain,
% 7.63/1.47      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_16,plain,
% 7.63/1.47      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.63/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.63/1.47      | r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 7.63/1.47      | r2_hidden(sK1(X1,X2,X0),X2)
% 7.63/1.47      | v2_struct_0(X1)
% 7.63/1.47      | ~ v3_orders_2(X1)
% 7.63/1.47      | ~ v4_orders_2(X1)
% 7.63/1.47      | ~ v5_orders_2(X1)
% 7.63/1.47      | ~ l1_orders_2(X1) ),
% 7.63/1.47      inference(cnf_transformation,[],[f72]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1139,plain,
% 7.63/1.47      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 7.63/1.47      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.63/1.47      | r2_hidden(X0,a_2_1_orders_2(X1,X2)) = iProver_top
% 7.63/1.47      | r2_hidden(sK1(X1,X2,X0),X2) = iProver_top
% 7.63/1.47      | v2_struct_0(X1) = iProver_top
% 7.63/1.47      | v3_orders_2(X1) != iProver_top
% 7.63/1.47      | v4_orders_2(X1) != iProver_top
% 7.63/1.47      | v5_orders_2(X1) != iProver_top
% 7.63/1.47      | l1_orders_2(X1) != iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_10,plain,
% 7.63/1.47      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.63/1.47      inference(cnf_transformation,[],[f52]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1145,plain,
% 7.63/1.47      ( r2_hidden(X0,X1) != iProver_top
% 7.63/1.47      | r1_tarski(X1,X0) != iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_2873,plain,
% 7.63/1.47      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 7.63/1.47      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.63/1.47      | r2_hidden(X0,a_2_1_orders_2(X1,X2)) = iProver_top
% 7.63/1.47      | r1_tarski(X2,sK1(X1,X2,X0)) != iProver_top
% 7.63/1.47      | v2_struct_0(X1) = iProver_top
% 7.63/1.47      | v3_orders_2(X1) != iProver_top
% 7.63/1.47      | v4_orders_2(X1) != iProver_top
% 7.63/1.47      | v5_orders_2(X1) != iProver_top
% 7.63/1.47      | l1_orders_2(X1) != iProver_top ),
% 7.63/1.47      inference(superposition,[status(thm)],[c_1139,c_1145]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_12504,plain,
% 7.63/1.47      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 7.63/1.47      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.63/1.47      | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0)) = iProver_top
% 7.63/1.47      | v2_struct_0(X1) = iProver_top
% 7.63/1.47      | v3_orders_2(X1) != iProver_top
% 7.63/1.47      | v4_orders_2(X1) != iProver_top
% 7.63/1.47      | v5_orders_2(X1) != iProver_top
% 7.63/1.47      | l1_orders_2(X1) != iProver_top ),
% 7.63/1.47      inference(superposition,[status(thm)],[c_1150,c_2873]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_14290,plain,
% 7.63/1.47      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 7.63/1.47      | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0)) = iProver_top
% 7.63/1.47      | v2_struct_0(X1) = iProver_top
% 7.63/1.47      | v3_orders_2(X1) != iProver_top
% 7.63/1.47      | v4_orders_2(X1) != iProver_top
% 7.63/1.47      | v5_orders_2(X1) != iProver_top
% 7.63/1.47      | l1_orders_2(X1) != iProver_top ),
% 7.63/1.47      inference(forward_subsumption_resolution,
% 7.63/1.47                [status(thm)],
% 7.63/1.47                [c_12504,c_1149]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_14294,plain,
% 7.63/1.47      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 7.63/1.47      | r2_hidden(X0,k2_orders_2(sK3,k1_xboole_0)) = iProver_top
% 7.63/1.47      | v2_struct_0(sK3) = iProver_top
% 7.63/1.47      | v3_orders_2(sK3) != iProver_top
% 7.63/1.47      | v4_orders_2(sK3) != iProver_top
% 7.63/1.47      | v5_orders_2(sK3) != iProver_top
% 7.63/1.47      | l1_orders_2(sK3) != iProver_top ),
% 7.63/1.47      inference(superposition,[status(thm)],[c_4710,c_14290]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_27,plain,
% 7.63/1.47      ( v2_struct_0(sK3) != iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_28,plain,
% 7.63/1.47      ( v3_orders_2(sK3) = iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_29,plain,
% 7.63/1.47      ( v4_orders_2(sK3) = iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_30,plain,
% 7.63/1.47      ( v5_orders_2(sK3) = iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_31,plain,
% 7.63/1.47      ( l1_orders_2(sK3) = iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_14831,plain,
% 7.63/1.47      ( r2_hidden(X0,k2_orders_2(sK3,k1_xboole_0)) = iProver_top
% 7.63/1.47      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 7.63/1.47      inference(global_propositional_subsumption,
% 7.63/1.47                [status(thm)],
% 7.63/1.47                [c_14294,c_27,c_28,c_29,c_30,c_31]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_14832,plain,
% 7.63/1.47      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 7.63/1.47      | r2_hidden(X0,k2_orders_2(sK3,k1_xboole_0)) = iProver_top ),
% 7.63/1.47      inference(renaming,[status(thm)],[c_14831]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_4,plain,
% 7.63/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.63/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.63/1.47      | ~ r2_hidden(sK0(X2,X0),X0)
% 7.63/1.47      | r1_tarski(X2,X0) ),
% 7.63/1.47      inference(cnf_transformation,[],[f47]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_229,plain,
% 7.63/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.63/1.47      | ~ r2_hidden(sK0(X0,X2),X2)
% 7.63/1.47      | ~ r1_tarski(X2,X1)
% 7.63/1.47      | r1_tarski(X0,X2) ),
% 7.63/1.47      inference(bin_hyper_res,[status(thm)],[c_4,c_174]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_415,plain,
% 7.63/1.47      ( ~ r2_hidden(sK0(X0,X1),X1)
% 7.63/1.47      | ~ r1_tarski(X0,X2)
% 7.63/1.47      | ~ r1_tarski(X1,X2)
% 7.63/1.47      | r1_tarski(X0,X1) ),
% 7.63/1.47      inference(bin_hyper_res,[status(thm)],[c_229,c_357]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1129,plain,
% 7.63/1.47      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.63/1.47      | r1_tarski(X0,X2) != iProver_top
% 7.63/1.47      | r1_tarski(X1,X2) != iProver_top
% 7.63/1.47      | r1_tarski(X0,X1) = iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_415]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_14841,plain,
% 7.63/1.47      ( m1_subset_1(sK0(X0,k2_orders_2(sK3,k1_xboole_0)),u1_struct_0(sK3)) != iProver_top
% 7.63/1.47      | r1_tarski(X0,X1) != iProver_top
% 7.63/1.47      | r1_tarski(X0,k2_orders_2(sK3,k1_xboole_0)) = iProver_top
% 7.63/1.47      | r1_tarski(k2_orders_2(sK3,k1_xboole_0),X1) != iProver_top ),
% 7.63/1.47      inference(superposition,[status(thm)],[c_14832,c_1129]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_15273,plain,
% 7.63/1.47      ( r1_tarski(k2_orders_2(sK3,k1_xboole_0),X0) != iProver_top
% 7.63/1.47      | r1_tarski(k2_orders_2(sK3,k1_xboole_0),u1_struct_0(sK3)) != iProver_top
% 7.63/1.47      | r1_tarski(u1_struct_0(sK3),X0) != iProver_top
% 7.63/1.47      | r1_tarski(u1_struct_0(sK3),k2_orders_2(sK3,k1_xboole_0)) = iProver_top ),
% 7.63/1.47      inference(superposition,[status(thm)],[c_3178,c_14841]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_21,negated_conjecture,
% 7.63/1.47      ( u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) ),
% 7.63/1.47      inference(cnf_transformation,[],[f68]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_14,plain,
% 7.63/1.47      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 7.63/1.47      inference(cnf_transformation,[],[f56]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_51,plain,
% 7.63/1.47      ( ~ l1_orders_2(sK3) | l1_struct_0(sK3) ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_14]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_11,plain,
% 7.63/1.47      ( ~ l1_struct_0(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 7.63/1.47      inference(cnf_transformation,[],[f53]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_60,plain,
% 7.63/1.47      ( ~ l1_struct_0(sK3) | k1_struct_0(sK3) = k1_xboole_0 ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_11]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_83,plain,
% 7.63/1.47      ( r1_tarski(sK3,sK3) ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_2]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_0,plain,
% 7.63/1.47      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.63/1.47      inference(cnf_transformation,[],[f44]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_87,plain,
% 7.63/1.47      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_0]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_492,plain,
% 7.63/1.47      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 7.63/1.47      theory(equality) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_505,plain,
% 7.63/1.47      ( u1_struct_0(sK3) = u1_struct_0(sK3) | sK3 != sK3 ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_492]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1492,plain,
% 7.63/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_1487]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1494,plain,
% 7.63/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_1492]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1491,plain,
% 7.63/1.47      ( m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
% 7.63/1.47      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 7.63/1.47      | v2_struct_0(X0)
% 7.63/1.47      | ~ v3_orders_2(X0)
% 7.63/1.47      | ~ v4_orders_2(X0)
% 7.63/1.47      | ~ v5_orders_2(X0)
% 7.63/1.47      | ~ l1_orders_2(X0) ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_13]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1496,plain,
% 7.63/1.47      ( m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.63/1.47      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.63/1.47      | v2_struct_0(X0) = iProver_top
% 7.63/1.47      | v3_orders_2(X0) != iProver_top
% 7.63/1.47      | v4_orders_2(X0) != iProver_top
% 7.63/1.47      | v5_orders_2(X0) != iProver_top
% 7.63/1.47      | l1_orders_2(X0) != iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_1491]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1498,plain,
% 7.63/1.47      ( m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.63/1.47      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.63/1.47      | v2_struct_0(sK3) = iProver_top
% 7.63/1.47      | v3_orders_2(sK3) != iProver_top
% 7.63/1.47      | v4_orders_2(sK3) != iProver_top
% 7.63/1.47      | v5_orders_2(sK3) != iProver_top
% 7.63/1.47      | l1_orders_2(sK3) != iProver_top ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_1496]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_485,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1442,plain,
% 7.63/1.47      ( k2_orders_2(sK3,k1_struct_0(sK3)) != X0
% 7.63/1.47      | u1_struct_0(sK3) != X0
% 7.63/1.47      | u1_struct_0(sK3) = k2_orders_2(sK3,k1_struct_0(sK3)) ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_485]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1582,plain,
% 7.63/1.47      ( k2_orders_2(sK3,k1_struct_0(sK3)) != u1_struct_0(sK3)
% 7.63/1.47      | u1_struct_0(sK3) = k2_orders_2(sK3,k1_struct_0(sK3))
% 7.63/1.47      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_1442]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1613,plain,
% 7.63/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.63/1.47      | r1_tarski(X0,u1_struct_0(X1)) ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_8]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1894,plain,
% 7.63/1.47      ( ~ m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
% 7.63/1.47      | r1_tarski(k2_orders_2(X0,k1_xboole_0),u1_struct_0(X0)) ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_1613]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1895,plain,
% 7.63/1.47      ( m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.63/1.47      | r1_tarski(k2_orders_2(X0,k1_xboole_0),u1_struct_0(X0)) = iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_1894]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1897,plain,
% 7.63/1.47      ( m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.63/1.47      | r1_tarski(k2_orders_2(sK3,k1_xboole_0),u1_struct_0(sK3)) = iProver_top ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_1895]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_491,plain,
% 7.63/1.47      ( X0 != X1 | X2 != X3 | k2_orders_2(X0,X2) = k2_orders_2(X1,X3) ),
% 7.63/1.47      theory(equality) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_2222,plain,
% 7.63/1.47      ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(X0,X1)
% 7.63/1.47      | k1_struct_0(sK3) != X1
% 7.63/1.47      | sK3 != X0 ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_491]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_2969,plain,
% 7.63/1.47      ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(X0,k1_xboole_0)
% 7.63/1.47      | k1_struct_0(sK3) != k1_xboole_0
% 7.63/1.47      | sK3 != X0 ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_2222]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_2971,plain,
% 7.63/1.47      ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(sK3,k1_xboole_0)
% 7.63/1.47      | k1_struct_0(sK3) != k1_xboole_0
% 7.63/1.47      | sK3 != sK3 ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_2969]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1806,plain,
% 7.63/1.47      ( k2_orders_2(sK3,k1_struct_0(sK3)) != X0
% 7.63/1.47      | k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(X1)
% 7.63/1.47      | u1_struct_0(X1) != X0 ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_485]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_5167,plain,
% 7.63/1.47      ( k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(X0,k1_xboole_0)
% 7.63/1.47      | k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(X1)
% 7.63/1.47      | u1_struct_0(X1) != k2_orders_2(X0,k1_xboole_0) ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_1806]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_5174,plain,
% 7.63/1.47      ( k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(sK3,k1_xboole_0)
% 7.63/1.47      | k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3)
% 7.63/1.47      | u1_struct_0(sK3) != k2_orders_2(sK3,k1_xboole_0) ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_5167]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1577,plain,
% 7.63/1.47      ( ~ r1_tarski(X0,u1_struct_0(sK3))
% 7.63/1.47      | ~ r1_tarski(u1_struct_0(sK3),X0)
% 7.63/1.47      | u1_struct_0(sK3) = X0 ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_0]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_15206,plain,
% 7.63/1.47      ( ~ r1_tarski(k2_orders_2(sK3,k1_xboole_0),u1_struct_0(sK3))
% 7.63/1.47      | ~ r1_tarski(u1_struct_0(sK3),k2_orders_2(sK3,k1_xboole_0))
% 7.63/1.47      | u1_struct_0(sK3) = k2_orders_2(sK3,k1_xboole_0) ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_1577]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_15207,plain,
% 7.63/1.47      ( u1_struct_0(sK3) = k2_orders_2(sK3,k1_xboole_0)
% 7.63/1.47      | r1_tarski(k2_orders_2(sK3,k1_xboole_0),u1_struct_0(sK3)) != iProver_top
% 7.63/1.47      | r1_tarski(u1_struct_0(sK3),k2_orders_2(sK3,k1_xboole_0)) != iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_15206]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_16593,plain,
% 7.63/1.47      ( r1_tarski(u1_struct_0(sK3),X0) != iProver_top
% 7.63/1.47      | r1_tarski(k2_orders_2(sK3,k1_xboole_0),X0) != iProver_top ),
% 7.63/1.47      inference(global_propositional_subsumption,
% 7.63/1.47                [status(thm)],
% 7.63/1.47                [c_15273,c_27,c_28,c_29,c_30,c_22,c_31,c_21,c_51,c_60,
% 7.63/1.47                 c_83,c_87,c_505,c_1494,c_1498,c_1582,c_1897,c_2971,
% 7.63/1.47                 c_5174,c_15207]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_16594,plain,
% 7.63/1.47      ( r1_tarski(k2_orders_2(sK3,k1_xboole_0),X0) != iProver_top
% 7.63/1.47      | r1_tarski(u1_struct_0(sK3),X0) != iProver_top ),
% 7.63/1.47      inference(renaming,[status(thm)],[c_16593]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_16602,plain,
% 7.63/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.63/1.47      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 7.63/1.47      | v2_struct_0(sK3) = iProver_top
% 7.63/1.47      | v3_orders_2(sK3) != iProver_top
% 7.63/1.47      | v4_orders_2(sK3) != iProver_top
% 7.63/1.47      | v5_orders_2(sK3) != iProver_top
% 7.63/1.47      | l1_orders_2(sK3) != iProver_top ),
% 7.63/1.47      inference(superposition,[status(thm)],[c_2669,c_16594]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1623,plain,
% 7.63/1.47      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_2]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1628,plain,
% 7.63/1.47      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
% 7.63/1.47      inference(predicate_to_equality,[status(thm)],[c_1623]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(c_1630,plain,
% 7.63/1.47      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 7.63/1.47      inference(instantiation,[status(thm)],[c_1628]) ).
% 7.63/1.47  
% 7.63/1.47  cnf(contradiction,plain,
% 7.63/1.47      ( $false ),
% 7.63/1.47      inference(minisat,
% 7.63/1.47                [status(thm)],
% 7.63/1.47                [c_16602,c_1630,c_1494,c_31,c_30,c_29,c_28,c_27]) ).
% 7.63/1.47  
% 7.63/1.47  
% 7.63/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.63/1.47  
% 7.63/1.47  ------                               Statistics
% 7.63/1.47  
% 7.63/1.47  ------ Selected
% 7.63/1.47  
% 7.63/1.47  total_time:                             0.546
% 7.63/1.47  
%------------------------------------------------------------------------------
