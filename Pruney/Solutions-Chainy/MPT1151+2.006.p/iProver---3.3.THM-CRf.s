%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:09 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 212 expanded)
%              Number of clauses        :   77 (  88 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :   16
%              Number of atoms          :  527 ( 993 expanded)
%              Number of equality atoms :  210 ( 293 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f28])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | m1_subset_1(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f33,plain,(
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

fof(f32,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK1(X1,X2,X3))
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f33,f32])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
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
    inference(equality_resolution,[],[f51])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
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

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f26,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f35,plain,
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

fof(f36,plain,
    ( u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f35])).

fof(f58,plain,(
    u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X0),X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_635,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_637,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,a_2_1_orders_2(X1,X2))
    | r2_hidden(sK1(X1,X2,X0),X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_626,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,X2)) = iProver_top
    | r2_hidden(sK1(X1,X2,X0),X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_632,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1994,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,X2)) = iProver_top
    | r1_tarski(X2,sK1(X1,X2,X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_626,c_632])).

cnf(c_7931,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_637,c_1994])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_634,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10164,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v3_orders_2(X1) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v5_orders_2(X1) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7931,c_634])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X0),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_636,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK0(X1,X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10169,plain,
    ( a_2_1_orders_2(X0,k1_xboole_0) = X1
    | m1_subset_1(a_2_1_orders_2(X0,k1_xboole_0),k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK0(X1,a_2_1_orders_2(X0,k1_xboole_0)),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10164,c_636])).

cnf(c_10477,plain,
    ( a_2_1_orders_2(X0,k1_xboole_0) = u1_struct_0(X0)
    | m1_subset_1(a_2_1_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_10169])).

cnf(c_10512,plain,
    ( a_2_1_orders_2(sK3,k1_xboole_0) = u1_struct_0(sK3)
    | m1_subset_1(a_2_1_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10477])).

cnf(c_201,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_975,plain,
    ( X0 != X1
    | u1_struct_0(sK3) != X1
    | u1_struct_0(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_1106,plain,
    ( X0 != u1_struct_0(sK3)
    | u1_struct_0(sK3) = X0
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_975])).

cnf(c_8221,plain,
    ( a_2_1_orders_2(sK3,k1_xboole_0) != u1_struct_0(sK3)
    | u1_struct_0(sK3) = a_2_1_orders_2(sK3,k1_xboole_0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1106])).

cnf(c_1068,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) != X0
    | k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3)
    | u1_struct_0(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_5129,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) != a_2_1_orders_2(X0,k1_xboole_0)
    | k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3)
    | u1_struct_0(sK3) != a_2_1_orders_2(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1068])).

cnf(c_5130,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) != a_2_1_orders_2(sK3,k1_xboole_0)
    | k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3)
    | u1_struct_0(sK3) != a_2_1_orders_2(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5129])).

cnf(c_1223,plain,
    ( X0 != X1
    | k2_orders_2(sK3,k1_struct_0(sK3)) != X1
    | k2_orders_2(sK3,k1_struct_0(sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_2234,plain,
    ( X0 != k2_orders_2(X1,X2)
    | k2_orders_2(sK3,k1_struct_0(sK3)) = X0
    | k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1223])).

cnf(c_3528,plain,
    ( a_2_1_orders_2(X0,k1_xboole_0) != k2_orders_2(X0,k1_xboole_0)
    | k2_orders_2(sK3,k1_struct_0(sK3)) = a_2_1_orders_2(X0,k1_xboole_0)
    | k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2234])).

cnf(c_3529,plain,
    ( a_2_1_orders_2(sK3,k1_xboole_0) != k2_orders_2(sK3,k1_xboole_0)
    | k2_orders_2(sK3,k1_struct_0(sK3)) = a_2_1_orders_2(sK3,k1_xboole_0)
    | k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3528])).

cnf(c_205,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1063,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_orders_2(X2,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X2)))
    | X0 != k2_orders_2(X2,k1_xboole_0)
    | X1 != k1_zfmisc_1(u1_struct_0(X2)) ),
    inference(instantiation,[status(thm)],[c_205])).

cnf(c_1195,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k2_orders_2(X2,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X2)))
    | X0 != k2_orders_2(X2,k1_xboole_0)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(u1_struct_0(X2)) ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(c_1459,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_orders_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
    | X0 != k2_orders_2(X1,k1_xboole_0)
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_1195])).

cnf(c_2857,plain,
    ( m1_subset_1(a_2_1_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
    | a_2_1_orders_2(X0,k1_xboole_0) != k2_orders_2(X0,k1_xboole_0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_2858,plain,
    ( a_2_1_orders_2(X0,k1_xboole_0) != k2_orders_2(X0,k1_xboole_0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(X0))
    | m1_subset_1(a_2_1_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2857])).

cnf(c_2860,plain,
    ( a_2_1_orders_2(sK3,k1_xboole_0) != k2_orders_2(sK3,k1_xboole_0)
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | m1_subset_1(a_2_1_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2858])).

cnf(c_207,plain,
    ( X0 != X1
    | X2 != X3
    | k2_orders_2(X0,X2) = k2_orders_2(X1,X3) ),
    theory(equality)).

cnf(c_1225,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(X0,X1)
    | k1_struct_0(sK3) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_1700,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(X0,k1_xboole_0)
    | k1_struct_0(sK3) != k1_xboole_0
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1225])).

cnf(c_1702,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(sK3,k1_xboole_0)
    | k1_struct_0(sK3) != k1_xboole_0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_204,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1196,plain,
    ( X0 != u1_struct_0(X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_1310,plain,
    ( u1_struct_0(X0) != u1_struct_0(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_1312,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1310])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_980,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | a_2_1_orders_2(X0,k1_xboole_0) = k2_orders_2(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_983,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_1_orders_2(sK3,k1_xboole_0) = k2_orders_2(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_980])).

cnf(c_896,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) != X0
    | u1_struct_0(sK3) != X0
    | u1_struct_0(sK3) = k2_orders_2(sK3,k1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_973,plain,
    ( k2_orders_2(sK3,k1_struct_0(sK3)) != u1_struct_0(sK3)
    | u1_struct_0(sK3) = k2_orders_2(sK3,k1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_896])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_930,plain,
    ( m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_935,plain,
    ( m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_930])).

cnf(c_937,plain,
    ( m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_orders_2(sK3) != iProver_top
    | v4_orders_2(sK3) != iProver_top
    | v5_orders_2(sK3) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_929,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_931,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_929])).

cnf(c_933,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_931])).

cnf(c_932,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_200,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_229,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_208,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_221,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_208])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_55,plain,
    ( ~ l1_struct_0(sK3)
    | k1_struct_0(sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_46,plain,
    ( ~ l1_orders_2(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_16,negated_conjecture,
    ( u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_17,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_26,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_25,plain,
    ( v5_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,plain,
    ( v4_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,plain,
    ( v3_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10512,c_8221,c_5130,c_3529,c_2860,c_1702,c_1312,c_983,c_973,c_937,c_933,c_932,c_229,c_221,c_55,c_46,c_16,c_26,c_17,c_25,c_18,c_24,c_19,c_23,c_20,c_22,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:14:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.18/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.01  
% 3.18/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/1.01  
% 3.18/1.01  ------  iProver source info
% 3.18/1.01  
% 3.18/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.18/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/1.01  git: non_committed_changes: false
% 3.18/1.01  git: last_make_outside_of_git: false
% 3.18/1.01  
% 3.18/1.01  ------ 
% 3.18/1.01  ------ Parsing...
% 3.18/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/1.01  
% 3.18/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.18/1.01  
% 3.18/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/1.01  
% 3.18/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.18/1.01  ------ Proving...
% 3.18/1.01  ------ Problem Properties 
% 3.18/1.01  
% 3.18/1.01  
% 3.18/1.01  clauses                                 22
% 3.18/1.01  conjectures                             6
% 3.18/1.01  EPR                                     8
% 3.18/1.01  Horn                                    13
% 3.18/1.01  unary                                   8
% 3.18/1.01  binary                                  3
% 3.18/1.01  lits                                    90
% 3.18/1.01  lits eq                                 6
% 3.18/1.01  fd_pure                                 0
% 3.18/1.01  fd_pseudo                               0
% 3.18/1.01  fd_cond                                 0
% 3.18/1.01  fd_pseudo_cond                          2
% 3.18/1.01  AC symbols                              0
% 3.18/1.01  
% 3.18/1.01  ------ Input Options Time Limit: Unbounded
% 3.18/1.01  
% 3.18/1.01  
% 3.18/1.01  ------ 
% 3.18/1.01  Current options:
% 3.18/1.01  ------ 
% 3.18/1.01  
% 3.18/1.01  
% 3.18/1.01  
% 3.18/1.01  
% 3.18/1.01  ------ Proving...
% 3.18/1.01  
% 3.18/1.01  
% 3.18/1.01  % SZS status Theorem for theBenchmark.p
% 3.18/1.01  
% 3.18/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/1.01  
% 3.18/1.01  fof(f2,axiom,(
% 3.18/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 3.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f13,plain,(
% 3.18/1.01    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.18/1.01    inference(ennf_transformation,[],[f2])).
% 3.18/1.01  
% 3.18/1.01  fof(f14,plain,(
% 3.18/1.01    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.18/1.01    inference(flattening,[],[f13])).
% 3.18/1.01  
% 3.18/1.01  fof(f28,plain,(
% 3.18/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)))),
% 3.18/1.01    introduced(choice_axiom,[])).
% 3.18/1.01  
% 3.18/1.01  fof(f29,plain,(
% 3.18/1.01    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f28])).
% 3.18/1.01  
% 3.18/1.01  fof(f38,plain,(
% 3.18/1.01    ( ! [X0,X1] : (X0 = X1 | m1_subset_1(sK0(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.18/1.01    inference(cnf_transformation,[],[f29])).
% 3.18/1.01  
% 3.18/1.01  fof(f1,axiom,(
% 3.18/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f37,plain,(
% 3.18/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.18/1.01    inference(cnf_transformation,[],[f1])).
% 3.18/1.01  
% 3.18/1.01  fof(f10,axiom,(
% 3.18/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f24,plain,(
% 3.18/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 3.18/1.01    inference(ennf_transformation,[],[f10])).
% 3.18/1.01  
% 3.18/1.01  fof(f25,plain,(
% 3.18/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.18/1.01    inference(flattening,[],[f24])).
% 3.18/1.01  
% 3.18/1.01  fof(f30,plain,(
% 3.18/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.18/1.01    inference(nnf_transformation,[],[f25])).
% 3.18/1.01  
% 3.18/1.01  fof(f31,plain,(
% 3.18/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.18/1.01    inference(rectify,[],[f30])).
% 3.18/1.01  
% 3.18/1.01  fof(f33,plain,(
% 3.18/1.01    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.18/1.01    introduced(choice_axiom,[])).
% 3.18/1.01  
% 3.18/1.01  fof(f32,plain,(
% 3.18/1.01    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))))),
% 3.18/1.01    introduced(choice_axiom,[])).
% 3.18/1.01  
% 3.18/1.01  fof(f34,plain,(
% 3.18/1.01    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK1(X1,X2,X3)) & r2_hidden(sK1(X1,X2,X3),X2) & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK2(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 3.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f33,f32])).
% 3.18/1.01  
% 3.18/1.01  fof(f51,plain,(
% 3.18/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.18/1.01    inference(cnf_transformation,[],[f34])).
% 3.18/1.01  
% 3.18/1.01  fof(f60,plain,(
% 3.18/1.01    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_1_orders_2(X1,X2)) | r2_hidden(sK1(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 3.18/1.01    inference(equality_resolution,[],[f51])).
% 3.18/1.01  
% 3.18/1.01  fof(f5,axiom,(
% 3.18/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f17,plain,(
% 3.18/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.18/1.01    inference(ennf_transformation,[],[f5])).
% 3.18/1.01  
% 3.18/1.01  fof(f42,plain,(
% 3.18/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.18/1.01    inference(cnf_transformation,[],[f17])).
% 3.18/1.01  
% 3.18/1.01  fof(f3,axiom,(
% 3.18/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f40,plain,(
% 3.18/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.18/1.01    inference(cnf_transformation,[],[f3])).
% 3.18/1.01  
% 3.18/1.01  fof(f39,plain,(
% 3.18/1.01    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.18/1.01    inference(cnf_transformation,[],[f29])).
% 3.18/1.01  
% 3.18/1.01  fof(f7,axiom,(
% 3.18/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 3.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f19,plain,(
% 3.18/1.01    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.18/1.01    inference(ennf_transformation,[],[f7])).
% 3.18/1.01  
% 3.18/1.01  fof(f20,plain,(
% 3.18/1.01    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.18/1.01    inference(flattening,[],[f19])).
% 3.18/1.01  
% 3.18/1.01  fof(f44,plain,(
% 3.18/1.01    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.18/1.01    inference(cnf_transformation,[],[f20])).
% 3.18/1.01  
% 3.18/1.01  fof(f8,axiom,(
% 3.18/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f21,plain,(
% 3.18/1.01    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.18/1.01    inference(ennf_transformation,[],[f8])).
% 3.18/1.01  
% 3.18/1.01  fof(f22,plain,(
% 3.18/1.01    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.18/1.01    inference(flattening,[],[f21])).
% 3.18/1.01  
% 3.18/1.01  fof(f45,plain,(
% 3.18/1.01    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.18/1.01    inference(cnf_transformation,[],[f22])).
% 3.18/1.01  
% 3.18/1.01  fof(f6,axiom,(
% 3.18/1.01    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 3.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f18,plain,(
% 3.18/1.01    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.18/1.01    inference(ennf_transformation,[],[f6])).
% 3.18/1.01  
% 3.18/1.01  fof(f43,plain,(
% 3.18/1.01    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.18/1.01    inference(cnf_transformation,[],[f18])).
% 3.18/1.01  
% 3.18/1.01  fof(f9,axiom,(
% 3.18/1.01    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f23,plain,(
% 3.18/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.18/1.01    inference(ennf_transformation,[],[f9])).
% 3.18/1.01  
% 3.18/1.01  fof(f46,plain,(
% 3.18/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.18/1.01    inference(cnf_transformation,[],[f23])).
% 3.18/1.01  
% 3.18/1.01  fof(f11,conjecture,(
% 3.18/1.01    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 3.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.01  
% 3.18/1.01  fof(f12,negated_conjecture,(
% 3.18/1.01    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 3.18/1.01    inference(negated_conjecture,[],[f11])).
% 3.18/1.01  
% 3.18/1.01  fof(f26,plain,(
% 3.18/1.01    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.18/1.01    inference(ennf_transformation,[],[f12])).
% 3.18/1.01  
% 3.18/1.01  fof(f27,plain,(
% 3.18/1.01    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 3.18/1.01    inference(flattening,[],[f26])).
% 3.18/1.01  
% 3.18/1.01  fof(f35,plain,(
% 3.18/1.01    ? [X0] : (u1_struct_0(X0) != k2_orders_2(X0,k1_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 3.18/1.01    introduced(choice_axiom,[])).
% 3.18/1.01  
% 3.18/1.01  fof(f36,plain,(
% 3.18/1.01    u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 3.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f35])).
% 3.18/1.01  
% 3.18/1.01  fof(f58,plain,(
% 3.18/1.01    u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3))),
% 3.18/1.01    inference(cnf_transformation,[],[f36])).
% 3.18/1.01  
% 3.18/1.01  fof(f57,plain,(
% 3.18/1.01    l1_orders_2(sK3)),
% 3.18/1.01    inference(cnf_transformation,[],[f36])).
% 3.18/1.01  
% 3.18/1.01  fof(f56,plain,(
% 3.18/1.01    v5_orders_2(sK3)),
% 3.18/1.01    inference(cnf_transformation,[],[f36])).
% 3.18/1.01  
% 3.18/1.01  fof(f55,plain,(
% 3.18/1.01    v4_orders_2(sK3)),
% 3.18/1.01    inference(cnf_transformation,[],[f36])).
% 3.18/1.01  
% 3.18/1.01  fof(f54,plain,(
% 3.18/1.01    v3_orders_2(sK3)),
% 3.18/1.01    inference(cnf_transformation,[],[f36])).
% 3.18/1.01  
% 3.18/1.01  fof(f53,plain,(
% 3.18/1.01    ~v2_struct_0(sK3)),
% 3.18/1.01    inference(cnf_transformation,[],[f36])).
% 3.18/1.01  
% 3.18/1.01  cnf(c_2,plain,
% 3.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.18/1.01      | m1_subset_1(sK0(X1,X0),X1)
% 3.18/1.01      | X0 = X1 ),
% 3.18/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_635,plain,
% 3.18/1.01      ( X0 = X1
% 3.18/1.01      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.18/1.01      | m1_subset_1(sK0(X1,X0),X1) = iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_0,plain,
% 3.18/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.18/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_637,plain,
% 3.18/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_11,plain,
% 3.18/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.18/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.18/1.01      | r2_hidden(X0,a_2_1_orders_2(X1,X2))
% 3.18/1.01      | r2_hidden(sK1(X1,X2,X0),X2)
% 3.18/1.01      | v2_struct_0(X1)
% 3.18/1.01      | ~ v3_orders_2(X1)
% 3.18/1.01      | ~ v4_orders_2(X1)
% 3.18/1.01      | ~ v5_orders_2(X1)
% 3.18/1.01      | ~ l1_orders_2(X1) ),
% 3.18/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_626,plain,
% 3.18/1.01      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.18/1.01      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.18/1.01      | r2_hidden(X0,a_2_1_orders_2(X1,X2)) = iProver_top
% 3.18/1.01      | r2_hidden(sK1(X1,X2,X0),X2) = iProver_top
% 3.18/1.01      | v2_struct_0(X1) = iProver_top
% 3.18/1.01      | v3_orders_2(X1) != iProver_top
% 3.18/1.01      | v4_orders_2(X1) != iProver_top
% 3.18/1.01      | v5_orders_2(X1) != iProver_top
% 3.18/1.01      | l1_orders_2(X1) != iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_5,plain,
% 3.18/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.18/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_632,plain,
% 3.18/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.18/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1994,plain,
% 3.18/1.01      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.18/1.01      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.18/1.01      | r2_hidden(X0,a_2_1_orders_2(X1,X2)) = iProver_top
% 3.18/1.01      | r1_tarski(X2,sK1(X1,X2,X0)) != iProver_top
% 3.18/1.01      | v2_struct_0(X1) = iProver_top
% 3.18/1.01      | v3_orders_2(X1) != iProver_top
% 3.18/1.01      | v4_orders_2(X1) != iProver_top
% 3.18/1.01      | v5_orders_2(X1) != iProver_top
% 3.18/1.01      | l1_orders_2(X1) != iProver_top ),
% 3.18/1.01      inference(superposition,[status(thm)],[c_626,c_632]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_7931,plain,
% 3.18/1.01      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.18/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.18/1.01      | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0)) = iProver_top
% 3.18/1.01      | v2_struct_0(X1) = iProver_top
% 3.18/1.01      | v3_orders_2(X1) != iProver_top
% 3.18/1.01      | v4_orders_2(X1) != iProver_top
% 3.18/1.01      | v5_orders_2(X1) != iProver_top
% 3.18/1.01      | l1_orders_2(X1) != iProver_top ),
% 3.18/1.01      inference(superposition,[status(thm)],[c_637,c_1994]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_3,plain,
% 3.18/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.18/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_634,plain,
% 3.18/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_10164,plain,
% 3.18/1.01      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.18/1.01      | r2_hidden(X0,a_2_1_orders_2(X1,k1_xboole_0)) = iProver_top
% 3.18/1.01      | v2_struct_0(X1) = iProver_top
% 3.18/1.01      | v3_orders_2(X1) != iProver_top
% 3.18/1.01      | v4_orders_2(X1) != iProver_top
% 3.18/1.01      | v5_orders_2(X1) != iProver_top
% 3.18/1.01      | l1_orders_2(X1) != iProver_top ),
% 3.18/1.01      inference(forward_subsumption_resolution,
% 3.18/1.01                [status(thm)],
% 3.18/1.01                [c_7931,c_634]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1,plain,
% 3.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.18/1.01      | ~ r2_hidden(sK0(X1,X0),X0)
% 3.18/1.01      | X0 = X1 ),
% 3.18/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_636,plain,
% 3.18/1.01      ( X0 = X1
% 3.18/1.01      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.18/1.01      | r2_hidden(sK0(X1,X0),X0) != iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_10169,plain,
% 3.18/1.01      ( a_2_1_orders_2(X0,k1_xboole_0) = X1
% 3.18/1.01      | m1_subset_1(a_2_1_orders_2(X0,k1_xboole_0),k1_zfmisc_1(X1)) != iProver_top
% 3.18/1.01      | m1_subset_1(sK0(X1,a_2_1_orders_2(X0,k1_xboole_0)),u1_struct_0(X0)) != iProver_top
% 3.18/1.01      | v2_struct_0(X0) = iProver_top
% 3.18/1.01      | v3_orders_2(X0) != iProver_top
% 3.18/1.01      | v4_orders_2(X0) != iProver_top
% 3.18/1.01      | v5_orders_2(X0) != iProver_top
% 3.18/1.01      | l1_orders_2(X0) != iProver_top ),
% 3.18/1.01      inference(superposition,[status(thm)],[c_10164,c_636]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_10477,plain,
% 3.18/1.01      ( a_2_1_orders_2(X0,k1_xboole_0) = u1_struct_0(X0)
% 3.18/1.01      | m1_subset_1(a_2_1_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.18/1.01      | v2_struct_0(X0) = iProver_top
% 3.18/1.01      | v3_orders_2(X0) != iProver_top
% 3.18/1.01      | v4_orders_2(X0) != iProver_top
% 3.18/1.01      | v5_orders_2(X0) != iProver_top
% 3.18/1.01      | l1_orders_2(X0) != iProver_top ),
% 3.18/1.01      inference(superposition,[status(thm)],[c_635,c_10169]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_10512,plain,
% 3.18/1.01      ( a_2_1_orders_2(sK3,k1_xboole_0) = u1_struct_0(sK3)
% 3.18/1.01      | m1_subset_1(a_2_1_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.18/1.01      | v2_struct_0(sK3) = iProver_top
% 3.18/1.01      | v3_orders_2(sK3) != iProver_top
% 3.18/1.01      | v4_orders_2(sK3) != iProver_top
% 3.18/1.01      | v5_orders_2(sK3) != iProver_top
% 3.18/1.01      | l1_orders_2(sK3) != iProver_top ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_10477]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_201,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_975,plain,
% 3.18/1.01      ( X0 != X1 | u1_struct_0(sK3) != X1 | u1_struct_0(sK3) = X0 ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_201]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1106,plain,
% 3.18/1.01      ( X0 != u1_struct_0(sK3)
% 3.18/1.01      | u1_struct_0(sK3) = X0
% 3.18/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_975]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_8221,plain,
% 3.18/1.01      ( a_2_1_orders_2(sK3,k1_xboole_0) != u1_struct_0(sK3)
% 3.18/1.01      | u1_struct_0(sK3) = a_2_1_orders_2(sK3,k1_xboole_0)
% 3.18/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_1106]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1068,plain,
% 3.18/1.01      ( k2_orders_2(sK3,k1_struct_0(sK3)) != X0
% 3.18/1.01      | k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3)
% 3.18/1.01      | u1_struct_0(sK3) != X0 ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_201]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_5129,plain,
% 3.18/1.01      ( k2_orders_2(sK3,k1_struct_0(sK3)) != a_2_1_orders_2(X0,k1_xboole_0)
% 3.18/1.01      | k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3)
% 3.18/1.01      | u1_struct_0(sK3) != a_2_1_orders_2(X0,k1_xboole_0) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_1068]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_5130,plain,
% 3.18/1.01      ( k2_orders_2(sK3,k1_struct_0(sK3)) != a_2_1_orders_2(sK3,k1_xboole_0)
% 3.18/1.01      | k2_orders_2(sK3,k1_struct_0(sK3)) = u1_struct_0(sK3)
% 3.18/1.01      | u1_struct_0(sK3) != a_2_1_orders_2(sK3,k1_xboole_0) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_5129]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1223,plain,
% 3.18/1.01      ( X0 != X1
% 3.18/1.01      | k2_orders_2(sK3,k1_struct_0(sK3)) != X1
% 3.18/1.01      | k2_orders_2(sK3,k1_struct_0(sK3)) = X0 ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_201]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_2234,plain,
% 3.18/1.01      ( X0 != k2_orders_2(X1,X2)
% 3.18/1.01      | k2_orders_2(sK3,k1_struct_0(sK3)) = X0
% 3.18/1.01      | k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(X1,X2) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_1223]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_3528,plain,
% 3.18/1.01      ( a_2_1_orders_2(X0,k1_xboole_0) != k2_orders_2(X0,k1_xboole_0)
% 3.18/1.01      | k2_orders_2(sK3,k1_struct_0(sK3)) = a_2_1_orders_2(X0,k1_xboole_0)
% 3.18/1.01      | k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(X0,k1_xboole_0) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_2234]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_3529,plain,
% 3.18/1.01      ( a_2_1_orders_2(sK3,k1_xboole_0) != k2_orders_2(sK3,k1_xboole_0)
% 3.18/1.01      | k2_orders_2(sK3,k1_struct_0(sK3)) = a_2_1_orders_2(sK3,k1_xboole_0)
% 3.18/1.01      | k2_orders_2(sK3,k1_struct_0(sK3)) != k2_orders_2(sK3,k1_xboole_0) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_3528]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_205,plain,
% 3.18/1.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.18/1.01      theory(equality) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1063,plain,
% 3.18/1.01      ( m1_subset_1(X0,X1)
% 3.18/1.01      | ~ m1_subset_1(k2_orders_2(X2,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X2)))
% 3.18/1.01      | X0 != k2_orders_2(X2,k1_xboole_0)
% 3.18/1.01      | X1 != k1_zfmisc_1(u1_struct_0(X2)) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_205]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1195,plain,
% 3.18/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.18/1.01      | ~ m1_subset_1(k2_orders_2(X2,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X2)))
% 3.18/1.01      | X0 != k2_orders_2(X2,k1_xboole_0)
% 3.18/1.01      | k1_zfmisc_1(X1) != k1_zfmisc_1(u1_struct_0(X2)) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_1063]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1459,plain,
% 3.18/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.18/1.01      | ~ m1_subset_1(k2_orders_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.18/1.01      | X0 != k2_orders_2(X1,k1_xboole_0)
% 3.18/1.01      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_1195]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_2857,plain,
% 3.18/1.01      ( m1_subset_1(a_2_1_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.18/1.01      | ~ m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.18/1.01      | a_2_1_orders_2(X0,k1_xboole_0) != k2_orders_2(X0,k1_xboole_0)
% 3.18/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(X0)) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_1459]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_2858,plain,
% 3.18/1.01      ( a_2_1_orders_2(X0,k1_xboole_0) != k2_orders_2(X0,k1_xboole_0)
% 3.18/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(X0))
% 3.18/1.01      | m1_subset_1(a_2_1_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.18/1.01      | m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2857]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_2860,plain,
% 3.18/1.01      ( a_2_1_orders_2(sK3,k1_xboole_0) != k2_orders_2(sK3,k1_xboole_0)
% 3.18/1.01      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
% 3.18/1.01      | m1_subset_1(a_2_1_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.18/1.01      | m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_2858]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_207,plain,
% 3.18/1.01      ( X0 != X1 | X2 != X3 | k2_orders_2(X0,X2) = k2_orders_2(X1,X3) ),
% 3.18/1.01      theory(equality) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1225,plain,
% 3.18/1.01      ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(X0,X1)
% 3.18/1.01      | k1_struct_0(sK3) != X1
% 3.18/1.01      | sK3 != X0 ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_207]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1700,plain,
% 3.18/1.01      ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(X0,k1_xboole_0)
% 3.18/1.01      | k1_struct_0(sK3) != k1_xboole_0
% 3.18/1.01      | sK3 != X0 ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_1225]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1702,plain,
% 3.18/1.01      ( k2_orders_2(sK3,k1_struct_0(sK3)) = k2_orders_2(sK3,k1_xboole_0)
% 3.18/1.01      | k1_struct_0(sK3) != k1_xboole_0
% 3.18/1.01      | sK3 != sK3 ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_1700]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_204,plain,
% 3.18/1.01      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.18/1.01      theory(equality) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1196,plain,
% 3.18/1.01      ( X0 != u1_struct_0(X1)
% 3.18/1.01      | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(X1)) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_204]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1310,plain,
% 3.18/1.01      ( u1_struct_0(X0) != u1_struct_0(X0)
% 3.18/1.01      | k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(X0)) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_1196]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_1312,plain,
% 3.18/1.01      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.18/1.01      | k1_zfmisc_1(u1_struct_0(sK3)) = k1_zfmisc_1(u1_struct_0(sK3)) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_1310]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_7,plain,
% 3.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.18/1.01      | v2_struct_0(X1)
% 3.18/1.01      | ~ v3_orders_2(X1)
% 3.18/1.01      | ~ v4_orders_2(X1)
% 3.18/1.01      | ~ v5_orders_2(X1)
% 3.18/1.01      | ~ l1_orders_2(X1)
% 3.18/1.01      | a_2_1_orders_2(X1,X0) = k2_orders_2(X1,X0) ),
% 3.18/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_980,plain,
% 3.18/1.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 3.18/1.01      | v2_struct_0(X0)
% 3.18/1.01      | ~ v3_orders_2(X0)
% 3.18/1.01      | ~ v4_orders_2(X0)
% 3.18/1.01      | ~ v5_orders_2(X0)
% 3.18/1.01      | ~ l1_orders_2(X0)
% 3.18/1.01      | a_2_1_orders_2(X0,k1_xboole_0) = k2_orders_2(X0,k1_xboole_0) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_983,plain,
% 3.18/1.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.18/1.01      | v2_struct_0(sK3)
% 3.18/1.01      | ~ v3_orders_2(sK3)
% 3.18/1.01      | ~ v4_orders_2(sK3)
% 3.18/1.01      | ~ v5_orders_2(sK3)
% 3.18/1.01      | ~ l1_orders_2(sK3)
% 3.18/1.01      | a_2_1_orders_2(sK3,k1_xboole_0) = k2_orders_2(sK3,k1_xboole_0) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_980]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_896,plain,
% 3.18/1.01      ( k2_orders_2(sK3,k1_struct_0(sK3)) != X0
% 3.18/1.01      | u1_struct_0(sK3) != X0
% 3.18/1.01      | u1_struct_0(sK3) = k2_orders_2(sK3,k1_struct_0(sK3)) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_201]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_973,plain,
% 3.18/1.01      ( k2_orders_2(sK3,k1_struct_0(sK3)) != u1_struct_0(sK3)
% 3.18/1.01      | u1_struct_0(sK3) = k2_orders_2(sK3,k1_struct_0(sK3))
% 3.18/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_896]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_8,plain,
% 3.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.18/1.01      | m1_subset_1(k2_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.18/1.01      | v2_struct_0(X1)
% 3.18/1.01      | ~ v3_orders_2(X1)
% 3.18/1.01      | ~ v4_orders_2(X1)
% 3.18/1.01      | ~ v5_orders_2(X1)
% 3.18/1.01      | ~ l1_orders_2(X1) ),
% 3.18/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_930,plain,
% 3.18/1.01      ( m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.18/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 3.18/1.01      | v2_struct_0(X0)
% 3.18/1.01      | ~ v3_orders_2(X0)
% 3.18/1.01      | ~ v4_orders_2(X0)
% 3.18/1.01      | ~ v5_orders_2(X0)
% 3.18/1.01      | ~ l1_orders_2(X0) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_935,plain,
% 3.18/1.01      ( m1_subset_1(k2_orders_2(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.18/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.18/1.01      | v2_struct_0(X0) = iProver_top
% 3.18/1.01      | v3_orders_2(X0) != iProver_top
% 3.18/1.01      | v4_orders_2(X0) != iProver_top
% 3.18/1.01      | v5_orders_2(X0) != iProver_top
% 3.18/1.01      | l1_orders_2(X0) != iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_930]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_937,plain,
% 3.18/1.01      ( m1_subset_1(k2_orders_2(sK3,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.18/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.18/1.01      | v2_struct_0(sK3) = iProver_top
% 3.18/1.01      | v3_orders_2(sK3) != iProver_top
% 3.18/1.01      | v4_orders_2(sK3) != iProver_top
% 3.18/1.01      | v5_orders_2(sK3) != iProver_top
% 3.18/1.01      | l1_orders_2(sK3) != iProver_top ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_935]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_929,plain,
% 3.18/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_931,plain,
% 3.18/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_929]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_933,plain,
% 3.18/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_931]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_932,plain,
% 3.18/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_929]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_200,plain,( X0 = X0 ),theory(equality) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_229,plain,
% 3.18/1.01      ( sK3 = sK3 ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_200]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_208,plain,
% 3.18/1.01      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.18/1.01      theory(equality) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_221,plain,
% 3.18/1.01      ( u1_struct_0(sK3) = u1_struct_0(sK3) | sK3 != sK3 ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_208]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_6,plain,
% 3.18/1.01      ( ~ l1_struct_0(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 3.18/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_55,plain,
% 3.18/1.01      ( ~ l1_struct_0(sK3) | k1_struct_0(sK3) = k1_xboole_0 ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_9,plain,
% 3.18/1.01      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.18/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_46,plain,
% 3.18/1.01      ( ~ l1_orders_2(sK3) | l1_struct_0(sK3) ),
% 3.18/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_16,negated_conjecture,
% 3.18/1.01      ( u1_struct_0(sK3) != k2_orders_2(sK3,k1_struct_0(sK3)) ),
% 3.18/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_17,negated_conjecture,
% 3.18/1.01      ( l1_orders_2(sK3) ),
% 3.18/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_26,plain,
% 3.18/1.01      ( l1_orders_2(sK3) = iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_18,negated_conjecture,
% 3.18/1.01      ( v5_orders_2(sK3) ),
% 3.18/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_25,plain,
% 3.18/1.01      ( v5_orders_2(sK3) = iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_19,negated_conjecture,
% 3.18/1.01      ( v4_orders_2(sK3) ),
% 3.18/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_24,plain,
% 3.18/1.01      ( v4_orders_2(sK3) = iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_20,negated_conjecture,
% 3.18/1.01      ( v3_orders_2(sK3) ),
% 3.18/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_23,plain,
% 3.18/1.01      ( v3_orders_2(sK3) = iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_21,negated_conjecture,
% 3.18/1.01      ( ~ v2_struct_0(sK3) ),
% 3.18/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(c_22,plain,
% 3.18/1.01      ( v2_struct_0(sK3) != iProver_top ),
% 3.18/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.18/1.01  
% 3.18/1.01  cnf(contradiction,plain,
% 3.18/1.01      ( $false ),
% 3.18/1.01      inference(minisat,
% 3.18/1.01                [status(thm)],
% 3.18/1.01                [c_10512,c_8221,c_5130,c_3529,c_2860,c_1702,c_1312,c_983,
% 3.18/1.01                 c_973,c_937,c_933,c_932,c_229,c_221,c_55,c_46,c_16,c_26,
% 3.18/1.01                 c_17,c_25,c_18,c_24,c_19,c_23,c_20,c_22,c_21]) ).
% 3.18/1.01  
% 3.18/1.01  
% 3.18/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/1.01  
% 3.18/1.01  ------                               Statistics
% 3.18/1.01  
% 3.18/1.01  ------ Selected
% 3.18/1.01  
% 3.18/1.01  total_time:                             0.385
% 3.18/1.01  
%------------------------------------------------------------------------------
