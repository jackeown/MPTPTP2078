%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:04 EST 2020

% Result     : Theorem 1.37s
% Output     : CNFRefutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 837 expanded)
%              Number of clauses        :   85 ( 281 expanded)
%              Number of leaves         :   18 ( 195 expanded)
%              Depth                    :   27
%              Number of atoms          :  715 (3973 expanded)
%              Number of equality atoms :  198 ( 626 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f60,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                <=> r1_tarski(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <~> r1_tarski(X1,X2) )
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(X1,X2)
                | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
              & ( r1_tarski(X1,X2)
                | r3_orders_2(k2_yellow_1(X0),X1,X2) )
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(X1,X2)
                | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
              & ( r1_tarski(X1,X2)
                | r3_orders_2(k2_yellow_1(X0),X1,X2) )
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
          & ( r1_tarski(X1,X2)
            | r3_orders_2(k2_yellow_1(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
     => ( ( ~ r1_tarski(X1,sK4)
          | ~ r3_orders_2(k2_yellow_1(X0),X1,sK4) )
        & ( r1_tarski(X1,sK4)
          | r3_orders_2(k2_yellow_1(X0),X1,sK4) )
        & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(X1,X2)
                | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
              & ( r1_tarski(X1,X2)
                | r3_orders_2(k2_yellow_1(X0),X1,X2) )
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
     => ( ? [X2] :
            ( ( ~ r1_tarski(sK3,X2)
              | ~ r3_orders_2(k2_yellow_1(X0),sK3,X2) )
            & ( r1_tarski(sK3,X2)
              | r3_orders_2(k2_yellow_1(X0),sK3,X2) )
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
        & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
                & ( r1_tarski(X1,X2)
                  | r3_orders_2(k2_yellow_1(X0),X1,X2) )
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(X1,X2)
                | ~ r3_orders_2(k2_yellow_1(sK2),X1,X2) )
              & ( r1_tarski(X1,X2)
                | r3_orders_2(k2_yellow_1(sK2),X1,X2) )
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ~ r1_tarski(sK3,sK4)
      | ~ r3_orders_2(k2_yellow_1(sK2),sK3,sK4) )
    & ( r1_tarski(sK3,sK4)
      | r3_orders_2(k2_yellow_1(sK2),sK3,sK4) )
    & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f40,f39,f38])).

fof(f68,plain,
    ( r1_tarski(sK3,sK4)
    | r3_orders_2(k2_yellow_1(sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

fof(f58,plain,(
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
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f15,plain,(
    ! [X0] :
      ( v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f17,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f61,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK0(X0,X1),sK1(X0,X1))
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( r1_tarski(sK0(X0,X1),sK1(X0,X1))
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK0(X0,X1),sK1(X0,X1))
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( r1_tarski(sK0(X0,X1),sK1(X0,X1))
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & r2_hidden(sK1(X0,X1),X0)
            & r2_hidden(sK0(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).

fof(f48,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] : k1_wellord2(X0) = k1_yellow_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k1_wellord2(X0) = k1_yellow_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0] : u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0] : k1_wellord2(X0) = u1_orders_2(k2_yellow_1(X0)) ),
    inference(definition_unfolding,[],[f62,f64])).

fof(f75,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | u1_orders_2(k2_yellow_1(X0)) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f48,f70])).

fof(f83,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),u1_orders_2(k2_yellow_1(X0)))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(u1_orders_2(k2_yellow_1(X0))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f78,plain,(
    ! [X0] : v1_relat_1(u1_orders_2(k2_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f53,f70])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ r3_orders_2(k2_yellow_1(sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f47,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | u1_orders_2(k2_yellow_1(X0)) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f47,f70])).

fof(f84,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),u1_orders_2(k2_yellow_1(X0)))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(u1_orders_2(k2_yellow_1(X0))) ) ),
    inference(equality_resolution,[],[f76])).

cnf(c_14,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_435,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_436,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_22,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(sK2),sK3,sK4)
    | r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_195,plain,
    ( r1_tarski(sK3,sK4)
    | r3_orders_2(k2_yellow_1(sK2),sK3,sK4) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_196,plain,
    ( r3_orders_2(k2_yellow_1(sK2),sK3,sK4)
    | r1_tarski(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_17,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_19,plain,
    ( v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_357,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_19])).

cnf(c_358,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_18])).

cnf(c_363,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_362])).

cnf(c_15,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_12,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_339,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_15,c_12])).

cnf(c_423,plain,
    ( ~ v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_339,c_18])).

cnf(c_424,plain,
    ( ~ v2_struct_0(k2_yellow_1(X0))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_504,plain,
    ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
    | r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(resolution,[status(thm)],[c_363,c_424])).

cnf(c_658,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r1_tarski(sK3,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))
    | k2_yellow_1(X0) != k2_yellow_1(sK2)
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_196,c_504])).

cnf(c_659,plain,
    ( r1_orders_2(k2_yellow_1(X0),sK3,sK4)
    | r1_tarski(sK3,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0)))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))
    | k2_yellow_1(X0) != k2_yellow_1(sK2) ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_755,plain,
    ( r1_tarski(sK3,sK4)
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(k2_yellow_1(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X2)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X3)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X3)))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X3)))
    | k2_yellow_1(X3) != k2_yellow_1(X2)
    | k2_yellow_1(X3) != k2_yellow_1(sK2)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_436,c_659])).

cnf(c_756,plain,
    ( r1_tarski(sK3,sK4)
    | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X0)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0)))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X1)))
    | k2_yellow_1(X1) != k2_yellow_1(X0)
    | k2_yellow_1(X1) != k2_yellow_1(sK2) ),
    inference(unflattening,[status(thm)],[c_755])).

cnf(c_1821,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(X1)
    | k2_yellow_1(X0) != k2_yellow_1(sK2)
    | r1_tarski(sK3,sK4) = iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X1))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X1))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X1))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_756])).

cnf(c_20,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1896,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(X1)
    | k2_yellow_1(X0) != k2_yellow_1(sK2)
    | r1_tarski(sK3,sK4) = iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X1))) = iProver_top
    | m1_subset_1(sK4,X0) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X1))) != iProver_top
    | m1_subset_1(sK3,X0) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1821,c_20])).

cnf(c_1897,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(X1)
    | k2_yellow_1(X0) != k2_yellow_1(sK2)
    | r1_tarski(sK3,sK4) = iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X1))) = iProver_top
    | m1_subset_1(sK4,X0) != iProver_top
    | m1_subset_1(sK4,X1) != iProver_top
    | m1_subset_1(sK3,X0) != iProver_top
    | m1_subset_1(sK3,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1896,c_20])).

cnf(c_2262,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK2)
    | r1_tarski(sK3,sK4) = iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X0))) = iProver_top
    | m1_subset_1(sK4,X0) != iProver_top
    | m1_subset_1(sK3,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1897])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1831,plain,
    ( m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1845,plain,
    ( m1_subset_1(sK4,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1831,c_20])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2162,plain,
    ( r2_hidden(sK4,X0)
    | ~ m1_subset_1(sK4,X0)
    | v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2163,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | m1_subset_1(sK4,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2162])).

cnf(c_2165,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | m1_subset_1(sK4,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2163])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1830,plain,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1842,plain,
    ( m1_subset_1(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1830,c_20])).

cnf(c_1832,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2194,plain,
    ( r2_hidden(sK3,sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_1832])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(k2_yellow_1(X2)))
    | ~ v1_relat_1(u1_orders_2(k2_yellow_1(X2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_11,plain,
    ( v1_relat_1(u1_orders_2(k2_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_610,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(k2_yellow_1(X2)))
    | u1_orders_2(k2_yellow_1(X3)) != u1_orders_2(k2_yellow_1(X2)) ),
    inference(resolution_lifted,[status(thm)],[c_8,c_11])).

cnf(c_1823,plain,
    ( u1_orders_2(k2_yellow_1(X0)) != u1_orders_2(k2_yellow_1(X1))
    | r1_tarski(X2,X3) != iProver_top
    | r2_hidden(X3,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_2106,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(k2_yellow_1(X2))) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1823])).

cnf(c_13,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_453,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_454,plain,
    ( r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_21,negated_conjecture,
    ( ~ r3_orders_2(k2_yellow_1(sK2),sK3,sK4)
    | ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_193,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ r3_orders_2(k2_yellow_1(sK2),sK3,sK4) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_194,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK2),sK3,sK4)
    | ~ r1_tarski(sK3,sK4) ),
    inference(renaming,[status(thm)],[c_193])).

cnf(c_16,plain,
    ( r3_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_384,plain,
    ( r3_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_385,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ l1_orders_2(k2_yellow_1(X0))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | r3_orders_2(k2_yellow_1(X0),X1,X2)
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_18])).

cnf(c_390,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v2_struct_0(k2_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_389])).

cnf(c_484,plain,
    ( r3_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
    inference(resolution,[status(thm)],[c_390,c_424])).

cnf(c_682,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
    | ~ r1_tarski(sK3,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))
    | k2_yellow_1(X0) != k2_yellow_1(sK2)
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_194,c_484])).

cnf(c_683,plain,
    ( ~ r1_orders_2(k2_yellow_1(X0),sK3,sK4)
    | ~ r1_tarski(sK3,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0)))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))
    | k2_yellow_1(X0) != k2_yellow_1(sK2) ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_722,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(k2_yellow_1(X2)))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X2)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X3)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X3)))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X3)))
    | k2_yellow_1(X3) != k2_yellow_1(X2)
    | k2_yellow_1(X3) != k2_yellow_1(sK2)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_454,c_683])).

cnf(c_723,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X0)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0)))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X1)))
    | k2_yellow_1(X1) != k2_yellow_1(X0)
    | k2_yellow_1(X1) != k2_yellow_1(sK2) ),
    inference(unflattening,[status(thm)],[c_722])).

cnf(c_1822,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(X1)
    | k2_yellow_1(X0) != k2_yellow_1(sK2)
    | r1_tarski(sK3,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X1))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X1))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X1))) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) != iProver_top
    | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_1916,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(X1)
    | k2_yellow_1(X0) != k2_yellow_1(sK2)
    | r1_tarski(sK3,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X1))) != iProver_top
    | m1_subset_1(sK4,X0) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X1))) != iProver_top
    | m1_subset_1(sK3,X0) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1822,c_20])).

cnf(c_1917,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(X1)
    | k2_yellow_1(X0) != k2_yellow_1(sK2)
    | r1_tarski(sK3,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X1))) != iProver_top
    | m1_subset_1(sK4,X0) != iProver_top
    | m1_subset_1(sK4,X1) != iProver_top
    | m1_subset_1(sK3,X0) != iProver_top
    | m1_subset_1(sK3,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1916,c_20])).

cnf(c_2274,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK2)
    | r1_tarski(sK3,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X0))) != iProver_top
    | m1_subset_1(sK4,X0) != iProver_top
    | m1_subset_1(sK3,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1917])).

cnf(c_2604,plain,
    ( r1_tarski(sK3,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(sK2))) != iProver_top
    | m1_subset_1(sK4,sK2) != iProver_top
    | m1_subset_1(sK3,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2274])).

cnf(c_2657,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(sK2))) != iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2604,c_26,c_1842,c_1845])).

cnf(c_2658,plain,
    ( r1_tarski(sK3,sK4) != iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2657])).

cnf(c_2663,plain,
    ( r1_tarski(sK3,sK4) != iProver_top
    | r2_hidden(sK4,sK2) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2106,c_2658])).

cnf(c_2666,plain,
    ( k2_yellow_1(X0) != k2_yellow_1(sK2)
    | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X0))) = iProver_top
    | m1_subset_1(sK4,X0) != iProver_top
    | m1_subset_1(sK3,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2262,c_26,c_1845,c_2165,c_2194,c_2663])).

cnf(c_2677,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(sK2))) = iProver_top
    | m1_subset_1(sK4,sK2) != iProver_top
    | m1_subset_1(sK3,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2666])).

cnf(c_1535,plain,
    ( X0 != X1
    | k2_yellow_1(X0) = k2_yellow_1(X1) ),
    theory(equality)).

cnf(c_1546,plain,
    ( k2_yellow_1(sK2) = k2_yellow_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_1529,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1554,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_1938,plain,
    ( k2_yellow_1(sK2) != k2_yellow_1(sK2)
    | r1_tarski(sK3,sK4) = iProver_top
    | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(sK2))) = iProver_top
    | m1_subset_1(sK4,sK2) != iProver_top
    | m1_subset_1(sK3,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1897])).

cnf(c_2814,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2677,c_26,c_1546,c_1554,c_1842,c_1938,c_1845,c_2165,c_2194,c_2663])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(k2_yellow_1(X2)))
    | ~ v1_relat_1(u1_orders_2(k2_yellow_1(X2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_590,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(k2_yellow_1(X2)))
    | u1_orders_2(k2_yellow_1(X3)) != u1_orders_2(k2_yellow_1(X2)) ),
    inference(resolution_lifted,[status(thm)],[c_9,c_11])).

cnf(c_1824,plain,
    ( u1_orders_2(k2_yellow_1(X0)) != u1_orders_2(k2_yellow_1(X1))
    | r1_tarski(X2,X3) = iProver_top
    | r2_hidden(X3,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_2489,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(k2_yellow_1(X2))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1824])).

cnf(c_2820,plain,
    ( r1_tarski(sK3,sK4) = iProver_top
    | r2_hidden(sK4,sK2) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2814,c_2489])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2820,c_2663,c_2194,c_2165,c_1845,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:49:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.37/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.37/0.99  
% 1.37/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.37/0.99  
% 1.37/0.99  ------  iProver source info
% 1.37/0.99  
% 1.37/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.37/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.37/0.99  git: non_committed_changes: false
% 1.37/0.99  git: last_make_outside_of_git: false
% 1.37/0.99  
% 1.37/0.99  ------ 
% 1.37/0.99  
% 1.37/0.99  ------ Input Options
% 1.37/0.99  
% 1.37/0.99  --out_options                           all
% 1.37/0.99  --tptp_safe_out                         true
% 1.37/0.99  --problem_path                          ""
% 1.37/0.99  --include_path                          ""
% 1.37/0.99  --clausifier                            res/vclausify_rel
% 1.37/0.99  --clausifier_options                    --mode clausify
% 1.37/0.99  --stdin                                 false
% 1.37/0.99  --stats_out                             all
% 1.37/0.99  
% 1.37/0.99  ------ General Options
% 1.37/0.99  
% 1.37/0.99  --fof                                   false
% 1.37/0.99  --time_out_real                         305.
% 1.37/0.99  --time_out_virtual                      -1.
% 1.37/0.99  --symbol_type_check                     false
% 1.37/0.99  --clausify_out                          false
% 1.37/0.99  --sig_cnt_out                           false
% 1.37/0.99  --trig_cnt_out                          false
% 1.37/0.99  --trig_cnt_out_tolerance                1.
% 1.37/0.99  --trig_cnt_out_sk_spl                   false
% 1.37/0.99  --abstr_cl_out                          false
% 1.37/0.99  
% 1.37/0.99  ------ Global Options
% 1.37/0.99  
% 1.37/0.99  --schedule                              default
% 1.37/0.99  --add_important_lit                     false
% 1.37/0.99  --prop_solver_per_cl                    1000
% 1.37/0.99  --min_unsat_core                        false
% 1.37/0.99  --soft_assumptions                      false
% 1.37/0.99  --soft_lemma_size                       3
% 1.37/0.99  --prop_impl_unit_size                   0
% 1.37/0.99  --prop_impl_unit                        []
% 1.37/0.99  --share_sel_clauses                     true
% 1.37/0.99  --reset_solvers                         false
% 1.37/0.99  --bc_imp_inh                            [conj_cone]
% 1.37/0.99  --conj_cone_tolerance                   3.
% 1.37/0.99  --extra_neg_conj                        none
% 1.37/0.99  --large_theory_mode                     true
% 1.37/0.99  --prolific_symb_bound                   200
% 1.37/0.99  --lt_threshold                          2000
% 1.37/0.99  --clause_weak_htbl                      true
% 1.37/0.99  --gc_record_bc_elim                     false
% 1.37/0.99  
% 1.37/0.99  ------ Preprocessing Options
% 1.37/0.99  
% 1.37/0.99  --preprocessing_flag                    true
% 1.37/0.99  --time_out_prep_mult                    0.1
% 1.37/0.99  --splitting_mode                        input
% 1.37/0.99  --splitting_grd                         true
% 1.37/0.99  --splitting_cvd                         false
% 1.37/0.99  --splitting_cvd_svl                     false
% 1.37/0.99  --splitting_nvd                         32
% 1.37/0.99  --sub_typing                            true
% 1.37/0.99  --prep_gs_sim                           true
% 1.37/0.99  --prep_unflatten                        true
% 1.37/0.99  --prep_res_sim                          true
% 1.37/0.99  --prep_upred                            true
% 1.37/0.99  --prep_sem_filter                       exhaustive
% 1.37/0.99  --prep_sem_filter_out                   false
% 1.37/0.99  --pred_elim                             true
% 1.37/0.99  --res_sim_input                         true
% 1.37/0.99  --eq_ax_congr_red                       true
% 1.37/0.99  --pure_diseq_elim                       true
% 1.37/0.99  --brand_transform                       false
% 1.37/0.99  --non_eq_to_eq                          false
% 1.37/0.99  --prep_def_merge                        true
% 1.37/0.99  --prep_def_merge_prop_impl              false
% 1.37/0.99  --prep_def_merge_mbd                    true
% 1.37/0.99  --prep_def_merge_tr_red                 false
% 1.37/0.99  --prep_def_merge_tr_cl                  false
% 1.37/0.99  --smt_preprocessing                     true
% 1.37/0.99  --smt_ac_axioms                         fast
% 1.37/0.99  --preprocessed_out                      false
% 1.37/0.99  --preprocessed_stats                    false
% 1.37/0.99  
% 1.37/0.99  ------ Abstraction refinement Options
% 1.37/0.99  
% 1.37/0.99  --abstr_ref                             []
% 1.37/0.99  --abstr_ref_prep                        false
% 1.37/0.99  --abstr_ref_until_sat                   false
% 1.37/0.99  --abstr_ref_sig_restrict                funpre
% 1.37/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.37/0.99  --abstr_ref_under                       []
% 1.37/0.99  
% 1.37/0.99  ------ SAT Options
% 1.37/0.99  
% 1.37/0.99  --sat_mode                              false
% 1.37/0.99  --sat_fm_restart_options                ""
% 1.37/0.99  --sat_gr_def                            false
% 1.37/0.99  --sat_epr_types                         true
% 1.37/0.99  --sat_non_cyclic_types                  false
% 1.37/0.99  --sat_finite_models                     false
% 1.37/0.99  --sat_fm_lemmas                         false
% 1.37/0.99  --sat_fm_prep                           false
% 1.37/0.99  --sat_fm_uc_incr                        true
% 1.37/0.99  --sat_out_model                         small
% 1.37/0.99  --sat_out_clauses                       false
% 1.37/0.99  
% 1.37/0.99  ------ QBF Options
% 1.37/0.99  
% 1.37/0.99  --qbf_mode                              false
% 1.37/0.99  --qbf_elim_univ                         false
% 1.37/0.99  --qbf_dom_inst                          none
% 1.37/0.99  --qbf_dom_pre_inst                      false
% 1.37/0.99  --qbf_sk_in                             false
% 1.37/0.99  --qbf_pred_elim                         true
% 1.37/0.99  --qbf_split                             512
% 1.37/0.99  
% 1.37/0.99  ------ BMC1 Options
% 1.37/0.99  
% 1.37/0.99  --bmc1_incremental                      false
% 1.37/0.99  --bmc1_axioms                           reachable_all
% 1.37/0.99  --bmc1_min_bound                        0
% 1.37/0.99  --bmc1_max_bound                        -1
% 1.37/0.99  --bmc1_max_bound_default                -1
% 1.37/0.99  --bmc1_symbol_reachability              true
% 1.37/0.99  --bmc1_property_lemmas                  false
% 1.37/0.99  --bmc1_k_induction                      false
% 1.37/0.99  --bmc1_non_equiv_states                 false
% 1.37/0.99  --bmc1_deadlock                         false
% 1.37/0.99  --bmc1_ucm                              false
% 1.37/0.99  --bmc1_add_unsat_core                   none
% 1.37/0.99  --bmc1_unsat_core_children              false
% 1.37/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.37/0.99  --bmc1_out_stat                         full
% 1.37/0.99  --bmc1_ground_init                      false
% 1.37/0.99  --bmc1_pre_inst_next_state              false
% 1.37/0.99  --bmc1_pre_inst_state                   false
% 1.37/0.99  --bmc1_pre_inst_reach_state             false
% 1.37/0.99  --bmc1_out_unsat_core                   false
% 1.37/0.99  --bmc1_aig_witness_out                  false
% 1.37/0.99  --bmc1_verbose                          false
% 1.37/0.99  --bmc1_dump_clauses_tptp                false
% 1.37/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.37/0.99  --bmc1_dump_file                        -
% 1.37/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.37/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.37/0.99  --bmc1_ucm_extend_mode                  1
% 1.37/0.99  --bmc1_ucm_init_mode                    2
% 1.37/0.99  --bmc1_ucm_cone_mode                    none
% 1.37/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.37/0.99  --bmc1_ucm_relax_model                  4
% 1.37/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.37/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.37/0.99  --bmc1_ucm_layered_model                none
% 1.37/0.99  --bmc1_ucm_max_lemma_size               10
% 1.37/0.99  
% 1.37/0.99  ------ AIG Options
% 1.37/0.99  
% 1.37/0.99  --aig_mode                              false
% 1.37/0.99  
% 1.37/0.99  ------ Instantiation Options
% 1.37/0.99  
% 1.37/0.99  --instantiation_flag                    true
% 1.37/0.99  --inst_sos_flag                         false
% 1.37/0.99  --inst_sos_phase                        true
% 1.37/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.37/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.37/0.99  --inst_lit_sel_side                     num_symb
% 1.37/0.99  --inst_solver_per_active                1400
% 1.37/0.99  --inst_solver_calls_frac                1.
% 1.37/0.99  --inst_passive_queue_type               priority_queues
% 1.37/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.37/0.99  --inst_passive_queues_freq              [25;2]
% 1.37/0.99  --inst_dismatching                      true
% 1.37/0.99  --inst_eager_unprocessed_to_passive     true
% 1.37/0.99  --inst_prop_sim_given                   true
% 1.37/0.99  --inst_prop_sim_new                     false
% 1.37/0.99  --inst_subs_new                         false
% 1.37/0.99  --inst_eq_res_simp                      false
% 1.37/0.99  --inst_subs_given                       false
% 1.37/0.99  --inst_orphan_elimination               true
% 1.37/0.99  --inst_learning_loop_flag               true
% 1.37/0.99  --inst_learning_start                   3000
% 1.37/0.99  --inst_learning_factor                  2
% 1.37/0.99  --inst_start_prop_sim_after_learn       3
% 1.37/0.99  --inst_sel_renew                        solver
% 1.37/0.99  --inst_lit_activity_flag                true
% 1.37/0.99  --inst_restr_to_given                   false
% 1.37/0.99  --inst_activity_threshold               500
% 1.37/0.99  --inst_out_proof                        true
% 1.37/0.99  
% 1.37/0.99  ------ Resolution Options
% 1.37/0.99  
% 1.37/0.99  --resolution_flag                       true
% 1.37/0.99  --res_lit_sel                           adaptive
% 1.37/0.99  --res_lit_sel_side                      none
% 1.37/0.99  --res_ordering                          kbo
% 1.37/0.99  --res_to_prop_solver                    active
% 1.37/0.99  --res_prop_simpl_new                    false
% 1.37/0.99  --res_prop_simpl_given                  true
% 1.37/0.99  --res_passive_queue_type                priority_queues
% 1.37/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.37/0.99  --res_passive_queues_freq               [15;5]
% 1.37/0.99  --res_forward_subs                      full
% 1.37/0.99  --res_backward_subs                     full
% 1.37/0.99  --res_forward_subs_resolution           true
% 1.37/0.99  --res_backward_subs_resolution          true
% 1.37/0.99  --res_orphan_elimination                true
% 1.37/0.99  --res_time_limit                        2.
% 1.37/0.99  --res_out_proof                         true
% 1.37/0.99  
% 1.37/0.99  ------ Superposition Options
% 1.37/0.99  
% 1.37/0.99  --superposition_flag                    true
% 1.37/0.99  --sup_passive_queue_type                priority_queues
% 1.37/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.37/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.37/0.99  --demod_completeness_check              fast
% 1.37/0.99  --demod_use_ground                      true
% 1.37/0.99  --sup_to_prop_solver                    passive
% 1.37/0.99  --sup_prop_simpl_new                    true
% 1.37/0.99  --sup_prop_simpl_given                  true
% 1.37/0.99  --sup_fun_splitting                     false
% 1.37/0.99  --sup_smt_interval                      50000
% 1.37/0.99  
% 1.37/0.99  ------ Superposition Simplification Setup
% 1.37/0.99  
% 1.37/0.99  --sup_indices_passive                   []
% 1.37/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.37/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.37/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.37/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.37/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.37/0.99  --sup_full_bw                           [BwDemod]
% 1.37/0.99  --sup_immed_triv                        [TrivRules]
% 1.37/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.37/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.37/0.99  --sup_immed_bw_main                     []
% 1.37/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.37/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.37/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.37/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.37/0.99  
% 1.37/0.99  ------ Combination Options
% 1.37/0.99  
% 1.37/0.99  --comb_res_mult                         3
% 1.37/0.99  --comb_sup_mult                         2
% 1.37/0.99  --comb_inst_mult                        10
% 1.37/0.99  
% 1.37/0.99  ------ Debug Options
% 1.37/0.99  
% 1.37/0.99  --dbg_backtrace                         false
% 1.37/0.99  --dbg_dump_prop_clauses                 false
% 1.37/0.99  --dbg_dump_prop_clauses_file            -
% 1.37/0.99  --dbg_out_stat                          false
% 1.37/0.99  ------ Parsing...
% 1.37/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.37/0.99  
% 1.37/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.37/0.99  
% 1.37/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.37/0.99  
% 1.37/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.37/0.99  ------ Proving...
% 1.37/0.99  ------ Problem Properties 
% 1.37/0.99  
% 1.37/0.99  
% 1.37/0.99  clauses                                 17
% 1.37/0.99  conjectures                             3
% 1.37/0.99  EPR                                     5
% 1.37/0.99  Horn                                    11
% 1.37/0.99  unary                                   5
% 1.37/0.99  binary                                  2
% 1.37/0.99  lits                                    55
% 1.37/0.99  lits eq                                 12
% 1.37/0.99  fd_pure                                 0
% 1.37/0.99  fd_pseudo                               0
% 1.37/0.99  fd_cond                                 0
% 1.37/0.99  fd_pseudo_cond                          0
% 1.37/0.99  AC symbols                              0
% 1.37/0.99  
% 1.37/0.99  ------ Schedule dynamic 5 is on 
% 1.37/0.99  
% 1.37/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.37/0.99  
% 1.37/0.99  
% 1.37/0.99  ------ 
% 1.37/0.99  Current options:
% 1.37/0.99  ------ 
% 1.37/0.99  
% 1.37/0.99  ------ Input Options
% 1.37/0.99  
% 1.37/0.99  --out_options                           all
% 1.37/0.99  --tptp_safe_out                         true
% 1.37/0.99  --problem_path                          ""
% 1.37/0.99  --include_path                          ""
% 1.37/0.99  --clausifier                            res/vclausify_rel
% 1.37/0.99  --clausifier_options                    --mode clausify
% 1.37/0.99  --stdin                                 false
% 1.37/0.99  --stats_out                             all
% 1.37/0.99  
% 1.37/0.99  ------ General Options
% 1.37/0.99  
% 1.37/0.99  --fof                                   false
% 1.37/0.99  --time_out_real                         305.
% 1.37/0.99  --time_out_virtual                      -1.
% 1.37/0.99  --symbol_type_check                     false
% 1.37/0.99  --clausify_out                          false
% 1.37/0.99  --sig_cnt_out                           false
% 1.37/0.99  --trig_cnt_out                          false
% 1.37/0.99  --trig_cnt_out_tolerance                1.
% 1.37/0.99  --trig_cnt_out_sk_spl                   false
% 1.37/0.99  --abstr_cl_out                          false
% 1.37/0.99  
% 1.37/0.99  ------ Global Options
% 1.37/0.99  
% 1.37/0.99  --schedule                              default
% 1.37/0.99  --add_important_lit                     false
% 1.37/0.99  --prop_solver_per_cl                    1000
% 1.37/0.99  --min_unsat_core                        false
% 1.37/0.99  --soft_assumptions                      false
% 1.37/0.99  --soft_lemma_size                       3
% 1.37/0.99  --prop_impl_unit_size                   0
% 1.37/0.99  --prop_impl_unit                        []
% 1.37/0.99  --share_sel_clauses                     true
% 1.37/0.99  --reset_solvers                         false
% 1.37/0.99  --bc_imp_inh                            [conj_cone]
% 1.37/0.99  --conj_cone_tolerance                   3.
% 1.37/0.99  --extra_neg_conj                        none
% 1.37/0.99  --large_theory_mode                     true
% 1.37/0.99  --prolific_symb_bound                   200
% 1.37/0.99  --lt_threshold                          2000
% 1.37/0.99  --clause_weak_htbl                      true
% 1.37/0.99  --gc_record_bc_elim                     false
% 1.37/0.99  
% 1.37/0.99  ------ Preprocessing Options
% 1.37/0.99  
% 1.37/0.99  --preprocessing_flag                    true
% 1.37/0.99  --time_out_prep_mult                    0.1
% 1.37/0.99  --splitting_mode                        input
% 1.37/0.99  --splitting_grd                         true
% 1.37/0.99  --splitting_cvd                         false
% 1.37/0.99  --splitting_cvd_svl                     false
% 1.37/0.99  --splitting_nvd                         32
% 1.37/0.99  --sub_typing                            true
% 1.37/0.99  --prep_gs_sim                           true
% 1.37/0.99  --prep_unflatten                        true
% 1.37/0.99  --prep_res_sim                          true
% 1.37/0.99  --prep_upred                            true
% 1.37/0.99  --prep_sem_filter                       exhaustive
% 1.37/0.99  --prep_sem_filter_out                   false
% 1.37/0.99  --pred_elim                             true
% 1.37/0.99  --res_sim_input                         true
% 1.37/0.99  --eq_ax_congr_red                       true
% 1.37/0.99  --pure_diseq_elim                       true
% 1.37/0.99  --brand_transform                       false
% 1.37/0.99  --non_eq_to_eq                          false
% 1.37/0.99  --prep_def_merge                        true
% 1.37/0.99  --prep_def_merge_prop_impl              false
% 1.37/0.99  --prep_def_merge_mbd                    true
% 1.37/0.99  --prep_def_merge_tr_red                 false
% 1.37/0.99  --prep_def_merge_tr_cl                  false
% 1.37/0.99  --smt_preprocessing                     true
% 1.37/0.99  --smt_ac_axioms                         fast
% 1.37/0.99  --preprocessed_out                      false
% 1.37/0.99  --preprocessed_stats                    false
% 1.37/0.99  
% 1.37/0.99  ------ Abstraction refinement Options
% 1.37/0.99  
% 1.37/0.99  --abstr_ref                             []
% 1.37/0.99  --abstr_ref_prep                        false
% 1.37/0.99  --abstr_ref_until_sat                   false
% 1.37/0.99  --abstr_ref_sig_restrict                funpre
% 1.37/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.37/0.99  --abstr_ref_under                       []
% 1.37/0.99  
% 1.37/0.99  ------ SAT Options
% 1.37/0.99  
% 1.37/0.99  --sat_mode                              false
% 1.37/0.99  --sat_fm_restart_options                ""
% 1.37/0.99  --sat_gr_def                            false
% 1.37/0.99  --sat_epr_types                         true
% 1.37/0.99  --sat_non_cyclic_types                  false
% 1.37/0.99  --sat_finite_models                     false
% 1.37/0.99  --sat_fm_lemmas                         false
% 1.37/0.99  --sat_fm_prep                           false
% 1.37/0.99  --sat_fm_uc_incr                        true
% 1.37/0.99  --sat_out_model                         small
% 1.37/0.99  --sat_out_clauses                       false
% 1.37/0.99  
% 1.37/0.99  ------ QBF Options
% 1.37/0.99  
% 1.37/0.99  --qbf_mode                              false
% 1.37/0.99  --qbf_elim_univ                         false
% 1.37/0.99  --qbf_dom_inst                          none
% 1.37/0.99  --qbf_dom_pre_inst                      false
% 1.37/0.99  --qbf_sk_in                             false
% 1.37/0.99  --qbf_pred_elim                         true
% 1.37/0.99  --qbf_split                             512
% 1.37/0.99  
% 1.37/0.99  ------ BMC1 Options
% 1.37/0.99  
% 1.37/0.99  --bmc1_incremental                      false
% 1.37/0.99  --bmc1_axioms                           reachable_all
% 1.37/0.99  --bmc1_min_bound                        0
% 1.37/0.99  --bmc1_max_bound                        -1
% 1.37/0.99  --bmc1_max_bound_default                -1
% 1.37/0.99  --bmc1_symbol_reachability              true
% 1.37/0.99  --bmc1_property_lemmas                  false
% 1.37/0.99  --bmc1_k_induction                      false
% 1.37/0.99  --bmc1_non_equiv_states                 false
% 1.37/0.99  --bmc1_deadlock                         false
% 1.37/0.99  --bmc1_ucm                              false
% 1.37/0.99  --bmc1_add_unsat_core                   none
% 1.37/0.99  --bmc1_unsat_core_children              false
% 1.37/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.37/0.99  --bmc1_out_stat                         full
% 1.37/0.99  --bmc1_ground_init                      false
% 1.37/0.99  --bmc1_pre_inst_next_state              false
% 1.37/0.99  --bmc1_pre_inst_state                   false
% 1.37/0.99  --bmc1_pre_inst_reach_state             false
% 1.37/0.99  --bmc1_out_unsat_core                   false
% 1.37/0.99  --bmc1_aig_witness_out                  false
% 1.37/0.99  --bmc1_verbose                          false
% 1.37/0.99  --bmc1_dump_clauses_tptp                false
% 1.37/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.37/0.99  --bmc1_dump_file                        -
% 1.37/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.37/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.37/0.99  --bmc1_ucm_extend_mode                  1
% 1.37/0.99  --bmc1_ucm_init_mode                    2
% 1.37/0.99  --bmc1_ucm_cone_mode                    none
% 1.37/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.37/0.99  --bmc1_ucm_relax_model                  4
% 1.37/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.37/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.37/0.99  --bmc1_ucm_layered_model                none
% 1.37/0.99  --bmc1_ucm_max_lemma_size               10
% 1.37/0.99  
% 1.37/0.99  ------ AIG Options
% 1.37/0.99  
% 1.37/0.99  --aig_mode                              false
% 1.37/0.99  
% 1.37/0.99  ------ Instantiation Options
% 1.37/0.99  
% 1.37/0.99  --instantiation_flag                    true
% 1.37/0.99  --inst_sos_flag                         false
% 1.37/0.99  --inst_sos_phase                        true
% 1.37/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.37/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.37/0.99  --inst_lit_sel_side                     none
% 1.37/0.99  --inst_solver_per_active                1400
% 1.37/0.99  --inst_solver_calls_frac                1.
% 1.37/0.99  --inst_passive_queue_type               priority_queues
% 1.37/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.37/0.99  --inst_passive_queues_freq              [25;2]
% 1.37/0.99  --inst_dismatching                      true
% 1.37/0.99  --inst_eager_unprocessed_to_passive     true
% 1.37/0.99  --inst_prop_sim_given                   true
% 1.37/0.99  --inst_prop_sim_new                     false
% 1.37/0.99  --inst_subs_new                         false
% 1.37/0.99  --inst_eq_res_simp                      false
% 1.37/0.99  --inst_subs_given                       false
% 1.37/0.99  --inst_orphan_elimination               true
% 1.37/0.99  --inst_learning_loop_flag               true
% 1.37/0.99  --inst_learning_start                   3000
% 1.37/0.99  --inst_learning_factor                  2
% 1.37/0.99  --inst_start_prop_sim_after_learn       3
% 1.37/0.99  --inst_sel_renew                        solver
% 1.37/0.99  --inst_lit_activity_flag                true
% 1.37/0.99  --inst_restr_to_given                   false
% 1.37/0.99  --inst_activity_threshold               500
% 1.37/0.99  --inst_out_proof                        true
% 1.37/0.99  
% 1.37/0.99  ------ Resolution Options
% 1.37/0.99  
% 1.37/0.99  --resolution_flag                       false
% 1.37/0.99  --res_lit_sel                           adaptive
% 1.37/0.99  --res_lit_sel_side                      none
% 1.37/0.99  --res_ordering                          kbo
% 1.37/0.99  --res_to_prop_solver                    active
% 1.37/0.99  --res_prop_simpl_new                    false
% 1.37/0.99  --res_prop_simpl_given                  true
% 1.37/0.99  --res_passive_queue_type                priority_queues
% 1.37/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.37/0.99  --res_passive_queues_freq               [15;5]
% 1.37/0.99  --res_forward_subs                      full
% 1.37/0.99  --res_backward_subs                     full
% 1.37/0.99  --res_forward_subs_resolution           true
% 1.37/0.99  --res_backward_subs_resolution          true
% 1.37/0.99  --res_orphan_elimination                true
% 1.37/0.99  --res_time_limit                        2.
% 1.37/0.99  --res_out_proof                         true
% 1.37/0.99  
% 1.37/0.99  ------ Superposition Options
% 1.37/0.99  
% 1.37/0.99  --superposition_flag                    true
% 1.37/0.99  --sup_passive_queue_type                priority_queues
% 1.37/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.37/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.37/0.99  --demod_completeness_check              fast
% 1.37/0.99  --demod_use_ground                      true
% 1.37/0.99  --sup_to_prop_solver                    passive
% 1.37/0.99  --sup_prop_simpl_new                    true
% 1.37/0.99  --sup_prop_simpl_given                  true
% 1.37/0.99  --sup_fun_splitting                     false
% 1.37/0.99  --sup_smt_interval                      50000
% 1.37/0.99  
% 1.37/0.99  ------ Superposition Simplification Setup
% 1.37/0.99  
% 1.37/0.99  --sup_indices_passive                   []
% 1.37/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.37/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.37/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.37/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.37/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.37/0.99  --sup_full_bw                           [BwDemod]
% 1.37/0.99  --sup_immed_triv                        [TrivRules]
% 1.37/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.37/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.37/0.99  --sup_immed_bw_main                     []
% 1.37/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.37/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.37/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.37/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.37/0.99  
% 1.37/0.99  ------ Combination Options
% 1.37/0.99  
% 1.37/0.99  --comb_res_mult                         3
% 1.37/0.99  --comb_sup_mult                         2
% 1.37/0.99  --comb_inst_mult                        10
% 1.37/0.99  
% 1.37/0.99  ------ Debug Options
% 1.37/0.99  
% 1.37/0.99  --dbg_backtrace                         false
% 1.37/0.99  --dbg_dump_prop_clauses                 false
% 1.37/0.99  --dbg_dump_prop_clauses_file            -
% 1.37/0.99  --dbg_out_stat                          false
% 1.37/0.99  
% 1.37/0.99  
% 1.37/0.99  
% 1.37/0.99  
% 1.37/0.99  ------ Proving...
% 1.37/0.99  
% 1.37/0.99  
% 1.37/0.99  % SZS status Theorem for theBenchmark.p
% 1.37/0.99  
% 1.37/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.37/0.99  
% 1.37/0.99  fof(f5,axiom,(
% 1.37/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 1.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.00  
% 1.37/1.00  fof(f23,plain,(
% 1.37/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.37/1.00    inference(ennf_transformation,[],[f5])).
% 1.37/1.00  
% 1.37/1.00  fof(f34,plain,(
% 1.37/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.37/1.00    inference(nnf_transformation,[],[f23])).
% 1.37/1.00  
% 1.37/1.00  fof(f55,plain,(
% 1.37/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.37/1.00    inference(cnf_transformation,[],[f34])).
% 1.37/1.00  
% 1.37/1.00  fof(f8,axiom,(
% 1.37/1.00    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.00  
% 1.37/1.00  fof(f16,plain,(
% 1.37/1.00    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 1.37/1.00    inference(pure_predicate_removal,[],[f8])).
% 1.37/1.00  
% 1.37/1.00  fof(f60,plain,(
% 1.37/1.00    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 1.37/1.00    inference(cnf_transformation,[],[f16])).
% 1.37/1.00  
% 1.37/1.00  fof(f12,conjecture,(
% 1.37/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 1.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.00  
% 1.37/1.00  fof(f13,negated_conjecture,(
% 1.37/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 1.37/1.00    inference(negated_conjecture,[],[f12])).
% 1.37/1.00  
% 1.37/1.00  fof(f27,plain,(
% 1.37/1.00    ? [X0] : (? [X1] : (? [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & ~v1_xboole_0(X0))),
% 1.37/1.00    inference(ennf_transformation,[],[f13])).
% 1.37/1.00  
% 1.37/1.00  fof(f36,plain,(
% 1.37/1.00    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2))) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & ~v1_xboole_0(X0))),
% 1.37/1.00    inference(nnf_transformation,[],[f27])).
% 1.37/1.00  
% 1.37/1.00  fof(f37,plain,(
% 1.37/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & ~v1_xboole_0(X0))),
% 1.37/1.00    inference(flattening,[],[f36])).
% 1.37/1.00  
% 1.37/1.00  fof(f40,plain,(
% 1.37/1.00    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) => ((~r1_tarski(X1,sK4) | ~r3_orders_2(k2_yellow_1(X0),X1,sK4)) & (r1_tarski(X1,sK4) | r3_orders_2(k2_yellow_1(X0),X1,sK4)) & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0))))) )),
% 1.37/1.00    introduced(choice_axiom,[])).
% 1.37/1.00  
% 1.37/1.00  fof(f39,plain,(
% 1.37/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) => (? [X2] : ((~r1_tarski(sK3,X2) | ~r3_orders_2(k2_yellow_1(X0),sK3,X2)) & (r1_tarski(sK3,X2) | r3_orders_2(k2_yellow_1(X0),sK3,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))))) )),
% 1.37/1.00    introduced(choice_axiom,[])).
% 1.37/1.00  
% 1.37/1.00  fof(f38,plain,(
% 1.37/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(sK2),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(sK2),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))) & ~v1_xboole_0(sK2))),
% 1.37/1.00    introduced(choice_axiom,[])).
% 1.37/1.00  
% 1.37/1.00  fof(f41,plain,(
% 1.37/1.00    (((~r1_tarski(sK3,sK4) | ~r3_orders_2(k2_yellow_1(sK2),sK3,sK4)) & (r1_tarski(sK3,sK4) | r3_orders_2(k2_yellow_1(sK2),sK3,sK4)) & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))) & ~v1_xboole_0(sK2)),
% 1.37/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f40,f39,f38])).
% 1.37/1.00  
% 1.37/1.00  fof(f68,plain,(
% 1.37/1.00    r1_tarski(sK3,sK4) | r3_orders_2(k2_yellow_1(sK2),sK3,sK4)),
% 1.37/1.00    inference(cnf_transformation,[],[f41])).
% 1.37/1.00  
% 1.37/1.00  fof(f7,axiom,(
% 1.37/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.00  
% 1.37/1.00  fof(f25,plain,(
% 1.37/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.37/1.00    inference(ennf_transformation,[],[f7])).
% 1.37/1.00  
% 1.37/1.00  fof(f26,plain,(
% 1.37/1.00    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.37/1.00    inference(flattening,[],[f25])).
% 1.37/1.00  
% 1.37/1.00  fof(f35,plain,(
% 1.37/1.00    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.37/1.00    inference(nnf_transformation,[],[f26])).
% 1.37/1.00  
% 1.37/1.00  fof(f58,plain,(
% 1.37/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.37/1.00    inference(cnf_transformation,[],[f35])).
% 1.37/1.00  
% 1.37/1.00  fof(f9,axiom,(
% 1.37/1.00    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.00  
% 1.37/1.00  fof(f14,plain,(
% 1.37/1.00    ! [X0] : (v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.37/1.00    inference(pure_predicate_removal,[],[f9])).
% 1.37/1.00  
% 1.37/1.00  fof(f15,plain,(
% 1.37/1.00    ! [X0] : (v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.37/1.00    inference(pure_predicate_removal,[],[f14])).
% 1.37/1.00  
% 1.37/1.00  fof(f17,plain,(
% 1.37/1.00    ! [X0] : v3_orders_2(k2_yellow_1(X0))),
% 1.37/1.00    inference(pure_predicate_removal,[],[f15])).
% 1.37/1.00  
% 1.37/1.00  fof(f61,plain,(
% 1.37/1.00    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 1.37/1.00    inference(cnf_transformation,[],[f17])).
% 1.37/1.00  
% 1.37/1.00  fof(f6,axiom,(
% 1.37/1.00    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.00  
% 1.37/1.00  fof(f24,plain,(
% 1.37/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.37/1.00    inference(ennf_transformation,[],[f6])).
% 1.37/1.00  
% 1.37/1.00  fof(f57,plain,(
% 1.37/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.37/1.00    inference(cnf_transformation,[],[f24])).
% 1.37/1.00  
% 1.37/1.00  fof(f4,axiom,(
% 1.37/1.00    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 1.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.00  
% 1.37/1.00  fof(f21,plain,(
% 1.37/1.00    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 1.37/1.00    inference(ennf_transformation,[],[f4])).
% 1.37/1.00  
% 1.37/1.00  fof(f22,plain,(
% 1.37/1.00    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 1.37/1.00    inference(flattening,[],[f21])).
% 1.37/1.00  
% 1.37/1.00  fof(f54,plain,(
% 1.37/1.00    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 1.37/1.00    inference(cnf_transformation,[],[f22])).
% 1.37/1.00  
% 1.37/1.00  fof(f11,axiom,(
% 1.37/1.00    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 1.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.00  
% 1.37/1.00  fof(f63,plain,(
% 1.37/1.00    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 1.37/1.00    inference(cnf_transformation,[],[f11])).
% 1.37/1.00  
% 1.37/1.00  fof(f65,plain,(
% 1.37/1.00    ~v1_xboole_0(sK2)),
% 1.37/1.00    inference(cnf_transformation,[],[f41])).
% 1.37/1.00  
% 1.37/1.00  fof(f67,plain,(
% 1.37/1.00    m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))),
% 1.37/1.00    inference(cnf_transformation,[],[f41])).
% 1.37/1.00  
% 1.37/1.00  fof(f1,axiom,(
% 1.37/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.00  
% 1.37/1.00  fof(f18,plain,(
% 1.37/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.37/1.00    inference(ennf_transformation,[],[f1])).
% 1.37/1.00  
% 1.37/1.00  fof(f28,plain,(
% 1.37/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.37/1.00    inference(nnf_transformation,[],[f18])).
% 1.37/1.00  
% 1.37/1.00  fof(f42,plain,(
% 1.37/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.37/1.00    inference(cnf_transformation,[],[f28])).
% 1.37/1.00  
% 1.37/1.00  fof(f66,plain,(
% 1.37/1.00    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))),
% 1.37/1.00    inference(cnf_transformation,[],[f41])).
% 1.37/1.00  
% 1.37/1.00  fof(f2,axiom,(
% 1.37/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 1.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.00  
% 1.37/1.00  fof(f19,plain,(
% 1.37/1.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 1.37/1.00    inference(ennf_transformation,[],[f2])).
% 1.37/1.00  
% 1.37/1.00  fof(f20,plain,(
% 1.37/1.00    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 1.37/1.00    inference(flattening,[],[f19])).
% 1.37/1.00  
% 1.37/1.00  fof(f29,plain,(
% 1.37/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 1.37/1.00    inference(nnf_transformation,[],[f20])).
% 1.37/1.00  
% 1.37/1.00  fof(f30,plain,(
% 1.37/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 1.37/1.00    inference(flattening,[],[f29])).
% 1.37/1.00  
% 1.37/1.00  fof(f31,plain,(
% 1.37/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 1.37/1.00    inference(rectify,[],[f30])).
% 1.37/1.00  
% 1.37/1.00  fof(f32,plain,(
% 1.37/1.00    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)))),
% 1.37/1.00    introduced(choice_axiom,[])).
% 1.37/1.00  
% 1.37/1.00  fof(f33,plain,(
% 1.37/1.00    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK0(X0,X1),sK1(X0,X1)) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r1_tarski(sK0(X0,X1),sK1(X0,X1)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 1.37/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).
% 1.37/1.00  
% 1.37/1.00  fof(f48,plain,(
% 1.37/1.00    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 1.37/1.00    inference(cnf_transformation,[],[f33])).
% 1.37/1.00  
% 1.37/1.00  fof(f10,axiom,(
% 1.37/1.00    ! [X0] : k1_wellord2(X0) = k1_yellow_1(X0)),
% 1.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.00  
% 1.37/1.00  fof(f62,plain,(
% 1.37/1.00    ( ! [X0] : (k1_wellord2(X0) = k1_yellow_1(X0)) )),
% 1.37/1.00    inference(cnf_transformation,[],[f10])).
% 1.37/1.00  
% 1.37/1.00  fof(f64,plain,(
% 1.37/1.00    ( ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)) )),
% 1.37/1.00    inference(cnf_transformation,[],[f11])).
% 1.37/1.00  
% 1.37/1.00  fof(f70,plain,(
% 1.37/1.00    ( ! [X0] : (k1_wellord2(X0) = u1_orders_2(k2_yellow_1(X0))) )),
% 1.37/1.00    inference(definition_unfolding,[],[f62,f64])).
% 1.37/1.00  
% 1.37/1.00  fof(f75,plain,(
% 1.37/1.00    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | u1_orders_2(k2_yellow_1(X0)) != X1 | ~v1_relat_1(X1)) )),
% 1.37/1.00    inference(definition_unfolding,[],[f48,f70])).
% 1.37/1.00  
% 1.37/1.00  fof(f83,plain,(
% 1.37/1.00    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),u1_orders_2(k2_yellow_1(X0))) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(u1_orders_2(k2_yellow_1(X0)))) )),
% 1.37/1.00    inference(equality_resolution,[],[f75])).
% 1.37/1.00  
% 1.37/1.00  fof(f3,axiom,(
% 1.37/1.00    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 1.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.37/1.00  
% 1.37/1.00  fof(f53,plain,(
% 1.37/1.00    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 1.37/1.00    inference(cnf_transformation,[],[f3])).
% 1.37/1.00  
% 1.37/1.00  fof(f78,plain,(
% 1.37/1.00    ( ! [X0] : (v1_relat_1(u1_orders_2(k2_yellow_1(X0)))) )),
% 1.37/1.00    inference(definition_unfolding,[],[f53,f70])).
% 1.37/1.00  
% 1.37/1.00  fof(f56,plain,(
% 1.37/1.00    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.37/1.00    inference(cnf_transformation,[],[f34])).
% 1.37/1.00  
% 1.37/1.00  fof(f69,plain,(
% 1.37/1.00    ~r1_tarski(sK3,sK4) | ~r3_orders_2(k2_yellow_1(sK2),sK3,sK4)),
% 1.37/1.00    inference(cnf_transformation,[],[f41])).
% 1.37/1.00  
% 1.37/1.00  fof(f59,plain,(
% 1.37/1.00    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.37/1.00    inference(cnf_transformation,[],[f35])).
% 1.37/1.00  
% 1.37/1.00  fof(f47,plain,(
% 1.37/1.00    ( ! [X4,X0,X5,X1] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 1.37/1.00    inference(cnf_transformation,[],[f33])).
% 1.37/1.00  
% 1.37/1.00  fof(f76,plain,(
% 1.37/1.00    ( ! [X4,X0,X5,X1] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | u1_orders_2(k2_yellow_1(X0)) != X1 | ~v1_relat_1(X1)) )),
% 1.37/1.00    inference(definition_unfolding,[],[f47,f70])).
% 1.37/1.00  
% 1.37/1.00  fof(f84,plain,(
% 1.37/1.00    ( ! [X4,X0,X5] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),u1_orders_2(k2_yellow_1(X0))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(u1_orders_2(k2_yellow_1(X0)))) )),
% 1.37/1.00    inference(equality_resolution,[],[f76])).
% 1.37/1.00  
% 1.37/1.00  cnf(c_14,plain,
% 1.37/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.37/1.00      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.37/1.00      | ~ l1_orders_2(X0) ),
% 1.37/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_18,plain,
% 1.37/1.00      ( l1_orders_2(k2_yellow_1(X0)) ),
% 1.37/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_435,plain,
% 1.37/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 1.37/1.00      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.37/1.00      | k2_yellow_1(X3) != X0 ),
% 1.37/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_436,plain,
% 1.37/1.00      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) ),
% 1.37/1.00      inference(unflattening,[status(thm)],[c_435]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_22,negated_conjecture,
% 1.37/1.00      ( r3_orders_2(k2_yellow_1(sK2),sK3,sK4) | r1_tarski(sK3,sK4) ),
% 1.37/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_195,plain,
% 1.37/1.00      ( r1_tarski(sK3,sK4) | r3_orders_2(k2_yellow_1(sK2),sK3,sK4) ),
% 1.37/1.00      inference(prop_impl,[status(thm)],[c_22]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_196,plain,
% 1.37/1.00      ( r3_orders_2(k2_yellow_1(sK2),sK3,sK4) | r1_tarski(sK3,sK4) ),
% 1.37/1.00      inference(renaming,[status(thm)],[c_195]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_17,plain,
% 1.37/1.00      ( ~ r3_orders_2(X0,X1,X2)
% 1.37/1.00      | r1_orders_2(X0,X1,X2)
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.37/1.00      | ~ v3_orders_2(X0)
% 1.37/1.00      | ~ l1_orders_2(X0)
% 1.37/1.00      | v2_struct_0(X0) ),
% 1.37/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_19,plain,
% 1.37/1.00      ( v3_orders_2(k2_yellow_1(X0)) ),
% 1.37/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_357,plain,
% 1.37/1.00      ( ~ r3_orders_2(X0,X1,X2)
% 1.37/1.00      | r1_orders_2(X0,X1,X2)
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.37/1.00      | ~ l1_orders_2(X0)
% 1.37/1.00      | v2_struct_0(X0)
% 1.37/1.00      | k2_yellow_1(X3) != X0 ),
% 1.37/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_19]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_358,plain,
% 1.37/1.00      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | r1_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ l1_orders_2(k2_yellow_1(X0))
% 1.37/1.00      | v2_struct_0(k2_yellow_1(X0)) ),
% 1.37/1.00      inference(unflattening,[status(thm)],[c_357]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_362,plain,
% 1.37/1.00      ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | r1_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | v2_struct_0(k2_yellow_1(X0)) ),
% 1.37/1.00      inference(global_propositional_subsumption,
% 1.37/1.00                [status(thm)],
% 1.37/1.00                [c_358,c_18]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_363,plain,
% 1.37/1.00      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | r1_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | v2_struct_0(k2_yellow_1(X0)) ),
% 1.37/1.00      inference(renaming,[status(thm)],[c_362]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_15,plain,
% 1.37/1.00      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.37/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_12,plain,
% 1.37/1.00      ( ~ v2_struct_0(X0)
% 1.37/1.00      | ~ l1_struct_0(X0)
% 1.37/1.00      | v1_xboole_0(u1_struct_0(X0)) ),
% 1.37/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_339,plain,
% 1.37/1.00      ( ~ l1_orders_2(X0)
% 1.37/1.00      | ~ v2_struct_0(X0)
% 1.37/1.00      | v1_xboole_0(u1_struct_0(X0)) ),
% 1.37/1.00      inference(resolution,[status(thm)],[c_15,c_12]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_423,plain,
% 1.37/1.00      ( ~ v2_struct_0(X0)
% 1.37/1.00      | v1_xboole_0(u1_struct_0(X0))
% 1.37/1.00      | k2_yellow_1(X1) != X0 ),
% 1.37/1.00      inference(resolution_lifted,[status(thm)],[c_339,c_18]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_424,plain,
% 1.37/1.00      ( ~ v2_struct_0(k2_yellow_1(X0))
% 1.37/1.00      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 1.37/1.00      inference(unflattening,[status(thm)],[c_423]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_504,plain,
% 1.37/1.00      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | r1_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 1.37/1.00      inference(resolution,[status(thm)],[c_363,c_424]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_658,plain,
% 1.37/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | r1_tarski(sK3,sK4)
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK2)
% 1.37/1.00      | sK4 != X2
% 1.37/1.00      | sK3 != X1 ),
% 1.37/1.00      inference(resolution_lifted,[status(thm)],[c_196,c_504]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_659,plain,
% 1.37/1.00      ( r1_orders_2(k2_yellow_1(X0),sK3,sK4)
% 1.37/1.00      | r1_tarski(sK3,sK4)
% 1.37/1.00      | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK2) ),
% 1.37/1.00      inference(unflattening,[status(thm)],[c_658]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_755,plain,
% 1.37/1.00      ( r1_tarski(sK3,sK4)
% 1.37/1.00      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(k2_yellow_1(X2)))
% 1.37/1.00      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X2)))
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X2)))
% 1.37/1.00      | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X3)))
% 1.37/1.00      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X3)))
% 1.37/1.00      | v1_xboole_0(u1_struct_0(k2_yellow_1(X3)))
% 1.37/1.00      | k2_yellow_1(X3) != k2_yellow_1(X2)
% 1.37/1.00      | k2_yellow_1(X3) != k2_yellow_1(sK2)
% 1.37/1.00      | sK4 != X1
% 1.37/1.00      | sK3 != X0 ),
% 1.37/1.00      inference(resolution_lifted,[status(thm)],[c_436,c_659]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_756,plain,
% 1.37/1.00      ( r1_tarski(sK3,sK4)
% 1.37/1.00      | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X1)))
% 1.37/1.00      | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X1)))
% 1.37/1.00      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | v1_xboole_0(u1_struct_0(k2_yellow_1(X1)))
% 1.37/1.00      | k2_yellow_1(X1) != k2_yellow_1(X0)
% 1.37/1.00      | k2_yellow_1(X1) != k2_yellow_1(sK2) ),
% 1.37/1.00      inference(unflattening,[status(thm)],[c_755]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1821,plain,
% 1.37/1.00      ( k2_yellow_1(X0) != k2_yellow_1(X1)
% 1.37/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK2)
% 1.37/1.00      | r1_tarski(sK3,sK4) = iProver_top
% 1.37/1.00      | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X1))) = iProver_top
% 1.37/1.00      | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X1))) != iProver_top
% 1.37/1.00      | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X1))) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 1.37/1.00      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 1.37/1.00      inference(predicate_to_equality,[status(thm)],[c_756]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_20,plain,
% 1.37/1.00      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 1.37/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1896,plain,
% 1.37/1.00      ( k2_yellow_1(X0) != k2_yellow_1(X1)
% 1.37/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK2)
% 1.37/1.00      | r1_tarski(sK3,sK4) = iProver_top
% 1.37/1.00      | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X1))) = iProver_top
% 1.37/1.00      | m1_subset_1(sK4,X0) != iProver_top
% 1.37/1.00      | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X1))) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,X0) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X1))) != iProver_top
% 1.37/1.00      | v1_xboole_0(X0) = iProver_top ),
% 1.37/1.00      inference(light_normalisation,[status(thm)],[c_1821,c_20]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1897,plain,
% 1.37/1.00      ( k2_yellow_1(X0) != k2_yellow_1(X1)
% 1.37/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK2)
% 1.37/1.00      | r1_tarski(sK3,sK4) = iProver_top
% 1.37/1.00      | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X1))) = iProver_top
% 1.37/1.00      | m1_subset_1(sK4,X0) != iProver_top
% 1.37/1.00      | m1_subset_1(sK4,X1) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,X0) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,X1) != iProver_top
% 1.37/1.00      | v1_xboole_0(X0) = iProver_top ),
% 1.37/1.00      inference(demodulation,[status(thm)],[c_1896,c_20]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_2262,plain,
% 1.37/1.00      ( k2_yellow_1(X0) != k2_yellow_1(sK2)
% 1.37/1.00      | r1_tarski(sK3,sK4) = iProver_top
% 1.37/1.00      | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X0))) = iProver_top
% 1.37/1.00      | m1_subset_1(sK4,X0) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,X0) != iProver_top
% 1.37/1.00      | v1_xboole_0(X0) = iProver_top ),
% 1.37/1.00      inference(equality_resolution,[status(thm)],[c_1897]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_25,negated_conjecture,
% 1.37/1.00      ( ~ v1_xboole_0(sK2) ),
% 1.37/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_26,plain,
% 1.37/1.00      ( v1_xboole_0(sK2) != iProver_top ),
% 1.37/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_23,negated_conjecture,
% 1.37/1.00      ( m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) ),
% 1.37/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1831,plain,
% 1.37/1.00      ( m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) = iProver_top ),
% 1.37/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1845,plain,
% 1.37/1.00      ( m1_subset_1(sK4,sK2) = iProver_top ),
% 1.37/1.00      inference(demodulation,[status(thm)],[c_1831,c_20]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_3,plain,
% 1.37/1.00      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 1.37/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_2162,plain,
% 1.37/1.00      ( r2_hidden(sK4,X0) | ~ m1_subset_1(sK4,X0) | v1_xboole_0(X0) ),
% 1.37/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_2163,plain,
% 1.37/1.00      ( r2_hidden(sK4,X0) = iProver_top
% 1.37/1.00      | m1_subset_1(sK4,X0) != iProver_top
% 1.37/1.00      | v1_xboole_0(X0) = iProver_top ),
% 1.37/1.00      inference(predicate_to_equality,[status(thm)],[c_2162]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_2165,plain,
% 1.37/1.00      ( r2_hidden(sK4,sK2) = iProver_top
% 1.37/1.00      | m1_subset_1(sK4,sK2) != iProver_top
% 1.37/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 1.37/1.00      inference(instantiation,[status(thm)],[c_2163]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_24,negated_conjecture,
% 1.37/1.00      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) ),
% 1.37/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1830,plain,
% 1.37/1.00      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) = iProver_top ),
% 1.37/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1842,plain,
% 1.37/1.00      ( m1_subset_1(sK3,sK2) = iProver_top ),
% 1.37/1.00      inference(demodulation,[status(thm)],[c_1830,c_20]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1832,plain,
% 1.37/1.00      ( r2_hidden(X0,X1) = iProver_top
% 1.37/1.00      | m1_subset_1(X0,X1) != iProver_top
% 1.37/1.00      | v1_xboole_0(X1) = iProver_top ),
% 1.37/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_2194,plain,
% 1.37/1.00      ( r2_hidden(sK3,sK2) = iProver_top
% 1.37/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 1.37/1.00      inference(superposition,[status(thm)],[c_1842,c_1832]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_8,plain,
% 1.37/1.00      ( ~ r1_tarski(X0,X1)
% 1.37/1.00      | ~ r2_hidden(X1,X2)
% 1.37/1.00      | ~ r2_hidden(X0,X2)
% 1.37/1.00      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(k2_yellow_1(X2)))
% 1.37/1.00      | ~ v1_relat_1(u1_orders_2(k2_yellow_1(X2))) ),
% 1.37/1.00      inference(cnf_transformation,[],[f83]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_11,plain,
% 1.37/1.00      ( v1_relat_1(u1_orders_2(k2_yellow_1(X0))) ),
% 1.37/1.00      inference(cnf_transformation,[],[f78]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_610,plain,
% 1.37/1.00      ( ~ r1_tarski(X0,X1)
% 1.37/1.00      | ~ r2_hidden(X1,X2)
% 1.37/1.00      | ~ r2_hidden(X0,X2)
% 1.37/1.00      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(k2_yellow_1(X2)))
% 1.37/1.00      | u1_orders_2(k2_yellow_1(X3)) != u1_orders_2(k2_yellow_1(X2)) ),
% 1.37/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_11]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1823,plain,
% 1.37/1.00      ( u1_orders_2(k2_yellow_1(X0)) != u1_orders_2(k2_yellow_1(X1))
% 1.37/1.00      | r1_tarski(X2,X3) != iProver_top
% 1.37/1.00      | r2_hidden(X3,X1) != iProver_top
% 1.37/1.00      | r2_hidden(X2,X1) != iProver_top
% 1.37/1.00      | r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X1))) = iProver_top ),
% 1.37/1.00      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_2106,plain,
% 1.37/1.00      ( r1_tarski(X0,X1) != iProver_top
% 1.37/1.00      | r2_hidden(X1,X2) != iProver_top
% 1.37/1.00      | r2_hidden(X0,X2) != iProver_top
% 1.37/1.00      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(k2_yellow_1(X2))) = iProver_top ),
% 1.37/1.00      inference(equality_resolution,[status(thm)],[c_1823]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_13,plain,
% 1.37/1.00      ( r1_orders_2(X0,X1,X2)
% 1.37/1.00      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.37/1.00      | ~ l1_orders_2(X0) ),
% 1.37/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_453,plain,
% 1.37/1.00      ( r1_orders_2(X0,X1,X2)
% 1.37/1.00      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.37/1.00      | k2_yellow_1(X3) != X0 ),
% 1.37/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_454,plain,
% 1.37/1.00      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) ),
% 1.37/1.00      inference(unflattening,[status(thm)],[c_453]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_21,negated_conjecture,
% 1.37/1.00      ( ~ r3_orders_2(k2_yellow_1(sK2),sK3,sK4) | ~ r1_tarski(sK3,sK4) ),
% 1.37/1.00      inference(cnf_transformation,[],[f69]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_193,plain,
% 1.37/1.00      ( ~ r1_tarski(sK3,sK4) | ~ r3_orders_2(k2_yellow_1(sK2),sK3,sK4) ),
% 1.37/1.00      inference(prop_impl,[status(thm)],[c_21]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_194,plain,
% 1.37/1.00      ( ~ r3_orders_2(k2_yellow_1(sK2),sK3,sK4) | ~ r1_tarski(sK3,sK4) ),
% 1.37/1.00      inference(renaming,[status(thm)],[c_193]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_16,plain,
% 1.37/1.00      ( r3_orders_2(X0,X1,X2)
% 1.37/1.00      | ~ r1_orders_2(X0,X1,X2)
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.37/1.00      | ~ v3_orders_2(X0)
% 1.37/1.00      | ~ l1_orders_2(X0)
% 1.37/1.00      | v2_struct_0(X0) ),
% 1.37/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_384,plain,
% 1.37/1.00      ( r3_orders_2(X0,X1,X2)
% 1.37/1.00      | ~ r1_orders_2(X0,X1,X2)
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.37/1.00      | ~ l1_orders_2(X0)
% 1.37/1.00      | v2_struct_0(X0)
% 1.37/1.00      | k2_yellow_1(X3) != X0 ),
% 1.37/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_385,plain,
% 1.37/1.00      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ l1_orders_2(k2_yellow_1(X0))
% 1.37/1.00      | v2_struct_0(k2_yellow_1(X0)) ),
% 1.37/1.00      inference(unflattening,[status(thm)],[c_384]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_389,plain,
% 1.37/1.00      ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | r3_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | v2_struct_0(k2_yellow_1(X0)) ),
% 1.37/1.00      inference(global_propositional_subsumption,
% 1.37/1.00                [status(thm)],
% 1.37/1.00                [c_385,c_18]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_390,plain,
% 1.37/1.00      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | v2_struct_0(k2_yellow_1(X0)) ),
% 1.37/1.00      inference(renaming,[status(thm)],[c_389]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_484,plain,
% 1.37/1.00      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ),
% 1.37/1.00      inference(resolution,[status(thm)],[c_390,c_424]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_682,plain,
% 1.37/1.00      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
% 1.37/1.00      | ~ r1_tarski(sK3,sK4)
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK2)
% 1.37/1.00      | sK4 != X2
% 1.37/1.00      | sK3 != X1 ),
% 1.37/1.00      inference(resolution_lifted,[status(thm)],[c_194,c_484]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_683,plain,
% 1.37/1.00      ( ~ r1_orders_2(k2_yellow_1(X0),sK3,sK4)
% 1.37/1.00      | ~ r1_tarski(sK3,sK4)
% 1.37/1.00      | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK2) ),
% 1.37/1.00      inference(unflattening,[status(thm)],[c_682]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_722,plain,
% 1.37/1.00      ( ~ r1_tarski(sK3,sK4)
% 1.37/1.00      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(k2_yellow_1(X2)))
% 1.37/1.00      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X2)))
% 1.37/1.00      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X2)))
% 1.37/1.00      | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X3)))
% 1.37/1.00      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X3)))
% 1.37/1.00      | v1_xboole_0(u1_struct_0(k2_yellow_1(X3)))
% 1.37/1.00      | k2_yellow_1(X3) != k2_yellow_1(X2)
% 1.37/1.00      | k2_yellow_1(X3) != k2_yellow_1(sK2)
% 1.37/1.00      | sK4 != X1
% 1.37/1.00      | sK3 != X0 ),
% 1.37/1.00      inference(resolution_lifted,[status(thm)],[c_454,c_683]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_723,plain,
% 1.37/1.00      ( ~ r1_tarski(sK3,sK4)
% 1.37/1.00      | ~ r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X1)))
% 1.37/1.00      | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X1)))
% 1.37/1.00      | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0)))
% 1.37/1.00      | v1_xboole_0(u1_struct_0(k2_yellow_1(X1)))
% 1.37/1.00      | k2_yellow_1(X1) != k2_yellow_1(X0)
% 1.37/1.00      | k2_yellow_1(X1) != k2_yellow_1(sK2) ),
% 1.37/1.00      inference(unflattening,[status(thm)],[c_722]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1822,plain,
% 1.37/1.00      ( k2_yellow_1(X0) != k2_yellow_1(X1)
% 1.37/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK2)
% 1.37/1.00      | r1_tarski(sK3,sK4) != iProver_top
% 1.37/1.00      | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X1))) != iProver_top
% 1.37/1.00      | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X1))) != iProver_top
% 1.37/1.00      | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X1))) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X0))) != iProver_top
% 1.37/1.00      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) = iProver_top ),
% 1.37/1.00      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1916,plain,
% 1.37/1.00      ( k2_yellow_1(X0) != k2_yellow_1(X1)
% 1.37/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK2)
% 1.37/1.00      | r1_tarski(sK3,sK4) != iProver_top
% 1.37/1.00      | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X1))) != iProver_top
% 1.37/1.00      | m1_subset_1(sK4,X0) != iProver_top
% 1.37/1.00      | m1_subset_1(sK4,u1_struct_0(k2_yellow_1(X1))) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,X0) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,u1_struct_0(k2_yellow_1(X1))) != iProver_top
% 1.37/1.00      | v1_xboole_0(X0) = iProver_top ),
% 1.37/1.00      inference(light_normalisation,[status(thm)],[c_1822,c_20]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1917,plain,
% 1.37/1.00      ( k2_yellow_1(X0) != k2_yellow_1(X1)
% 1.37/1.00      | k2_yellow_1(X0) != k2_yellow_1(sK2)
% 1.37/1.00      | r1_tarski(sK3,sK4) != iProver_top
% 1.37/1.00      | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X1))) != iProver_top
% 1.37/1.00      | m1_subset_1(sK4,X0) != iProver_top
% 1.37/1.00      | m1_subset_1(sK4,X1) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,X0) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,X1) != iProver_top
% 1.37/1.00      | v1_xboole_0(X0) = iProver_top ),
% 1.37/1.00      inference(demodulation,[status(thm)],[c_1916,c_20]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_2274,plain,
% 1.37/1.00      ( k2_yellow_1(X0) != k2_yellow_1(sK2)
% 1.37/1.00      | r1_tarski(sK3,sK4) != iProver_top
% 1.37/1.00      | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X0))) != iProver_top
% 1.37/1.00      | m1_subset_1(sK4,X0) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,X0) != iProver_top
% 1.37/1.00      | v1_xboole_0(X0) = iProver_top ),
% 1.37/1.00      inference(equality_resolution,[status(thm)],[c_1917]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_2604,plain,
% 1.37/1.00      ( r1_tarski(sK3,sK4) != iProver_top
% 1.37/1.00      | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(sK2))) != iProver_top
% 1.37/1.00      | m1_subset_1(sK4,sK2) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,sK2) != iProver_top
% 1.37/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 1.37/1.00      inference(equality_resolution,[status(thm)],[c_2274]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_2657,plain,
% 1.37/1.00      ( r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(sK2))) != iProver_top
% 1.37/1.00      | r1_tarski(sK3,sK4) != iProver_top ),
% 1.37/1.00      inference(global_propositional_subsumption,
% 1.37/1.00                [status(thm)],
% 1.37/1.00                [c_2604,c_26,c_1842,c_1845]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_2658,plain,
% 1.37/1.00      ( r1_tarski(sK3,sK4) != iProver_top
% 1.37/1.00      | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(sK2))) != iProver_top ),
% 1.37/1.00      inference(renaming,[status(thm)],[c_2657]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_2663,plain,
% 1.37/1.00      ( r1_tarski(sK3,sK4) != iProver_top
% 1.37/1.00      | r2_hidden(sK4,sK2) != iProver_top
% 1.37/1.00      | r2_hidden(sK3,sK2) != iProver_top ),
% 1.37/1.00      inference(superposition,[status(thm)],[c_2106,c_2658]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_2666,plain,
% 1.37/1.00      ( k2_yellow_1(X0) != k2_yellow_1(sK2)
% 1.37/1.00      | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(X0))) = iProver_top
% 1.37/1.00      | m1_subset_1(sK4,X0) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,X0) != iProver_top
% 1.37/1.00      | v1_xboole_0(X0) = iProver_top ),
% 1.37/1.00      inference(global_propositional_subsumption,
% 1.37/1.00                [status(thm)],
% 1.37/1.00                [c_2262,c_26,c_1845,c_2165,c_2194,c_2663]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_2677,plain,
% 1.37/1.00      ( r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(sK2))) = iProver_top
% 1.37/1.00      | m1_subset_1(sK4,sK2) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,sK2) != iProver_top
% 1.37/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 1.37/1.00      inference(equality_resolution,[status(thm)],[c_2666]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1535,plain,
% 1.37/1.00      ( X0 != X1 | k2_yellow_1(X0) = k2_yellow_1(X1) ),
% 1.37/1.00      theory(equality) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1546,plain,
% 1.37/1.00      ( k2_yellow_1(sK2) = k2_yellow_1(sK2) | sK2 != sK2 ),
% 1.37/1.00      inference(instantiation,[status(thm)],[c_1535]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1529,plain,( X0 = X0 ),theory(equality) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1554,plain,
% 1.37/1.00      ( sK2 = sK2 ),
% 1.37/1.00      inference(instantiation,[status(thm)],[c_1529]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1938,plain,
% 1.37/1.00      ( k2_yellow_1(sK2) != k2_yellow_1(sK2)
% 1.37/1.00      | r1_tarski(sK3,sK4) = iProver_top
% 1.37/1.00      | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(sK2))) = iProver_top
% 1.37/1.00      | m1_subset_1(sK4,sK2) != iProver_top
% 1.37/1.00      | m1_subset_1(sK3,sK2) != iProver_top
% 1.37/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 1.37/1.00      inference(instantiation,[status(thm)],[c_1897]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_2814,plain,
% 1.37/1.00      ( r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(k2_yellow_1(sK2))) = iProver_top ),
% 1.37/1.00      inference(global_propositional_subsumption,
% 1.37/1.00                [status(thm)],
% 1.37/1.00                [c_2677,c_26,c_1546,c_1554,c_1842,c_1938,c_1845,c_2165,
% 1.37/1.00                 c_2194,c_2663]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_9,plain,
% 1.37/1.00      ( r1_tarski(X0,X1)
% 1.37/1.00      | ~ r2_hidden(X1,X2)
% 1.37/1.00      | ~ r2_hidden(X0,X2)
% 1.37/1.00      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(k2_yellow_1(X2)))
% 1.37/1.00      | ~ v1_relat_1(u1_orders_2(k2_yellow_1(X2))) ),
% 1.37/1.00      inference(cnf_transformation,[],[f84]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_590,plain,
% 1.37/1.00      ( r1_tarski(X0,X1)
% 1.37/1.00      | ~ r2_hidden(X1,X2)
% 1.37/1.00      | ~ r2_hidden(X0,X2)
% 1.37/1.00      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(k2_yellow_1(X2)))
% 1.37/1.00      | u1_orders_2(k2_yellow_1(X3)) != u1_orders_2(k2_yellow_1(X2)) ),
% 1.37/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_11]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_1824,plain,
% 1.37/1.00      ( u1_orders_2(k2_yellow_1(X0)) != u1_orders_2(k2_yellow_1(X1))
% 1.37/1.00      | r1_tarski(X2,X3) = iProver_top
% 1.37/1.00      | r2_hidden(X3,X1) != iProver_top
% 1.37/1.00      | r2_hidden(X2,X1) != iProver_top
% 1.37/1.00      | r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X1))) != iProver_top ),
% 1.37/1.00      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_2489,plain,
% 1.37/1.00      ( r1_tarski(X0,X1) = iProver_top
% 1.37/1.00      | r2_hidden(X1,X2) != iProver_top
% 1.37/1.00      | r2_hidden(X0,X2) != iProver_top
% 1.37/1.00      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(k2_yellow_1(X2))) != iProver_top ),
% 1.37/1.00      inference(equality_resolution,[status(thm)],[c_1824]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(c_2820,plain,
% 1.37/1.00      ( r1_tarski(sK3,sK4) = iProver_top
% 1.37/1.00      | r2_hidden(sK4,sK2) != iProver_top
% 1.37/1.00      | r2_hidden(sK3,sK2) != iProver_top ),
% 1.37/1.00      inference(superposition,[status(thm)],[c_2814,c_2489]) ).
% 1.37/1.00  
% 1.37/1.00  cnf(contradiction,plain,
% 1.37/1.00      ( $false ),
% 1.37/1.00      inference(minisat,
% 1.37/1.00                [status(thm)],
% 1.37/1.00                [c_2820,c_2663,c_2194,c_2165,c_1845,c_26]) ).
% 1.37/1.00  
% 1.37/1.00  
% 1.37/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.37/1.00  
% 1.37/1.00  ------                               Statistics
% 1.37/1.00  
% 1.37/1.00  ------ General
% 1.37/1.00  
% 1.37/1.00  abstr_ref_over_cycles:                  0
% 1.37/1.00  abstr_ref_under_cycles:                 0
% 1.37/1.00  gc_basic_clause_elim:                   0
% 1.37/1.00  forced_gc_time:                         0
% 1.37/1.00  parsing_time:                           0.009
% 1.37/1.00  unif_index_cands_time:                  0.
% 1.37/1.00  unif_index_add_time:                    0.
% 1.37/1.00  orderings_time:                         0.
% 1.37/1.00  out_proof_time:                         0.009
% 1.37/1.00  total_time:                             0.095
% 1.37/1.00  num_of_symbols:                         52
% 1.37/1.00  num_of_terms:                           1687
% 1.37/1.00  
% 1.37/1.00  ------ Preprocessing
% 1.37/1.00  
% 1.37/1.00  num_of_splits:                          0
% 1.37/1.00  num_of_split_atoms:                     0
% 1.37/1.00  num_of_reused_defs:                     0
% 1.37/1.00  num_eq_ax_congr_red:                    7
% 1.37/1.00  num_of_sem_filtered_clauses:            1
% 1.37/1.00  num_of_subtypes:                        0
% 1.37/1.00  monotx_restored_types:                  0
% 1.37/1.00  sat_num_of_epr_types:                   0
% 1.37/1.00  sat_num_of_non_cyclic_types:            0
% 1.37/1.00  sat_guarded_non_collapsed_types:        0
% 1.37/1.00  num_pure_diseq_elim:                    0
% 1.37/1.00  simp_replaced_by:                       0
% 1.37/1.00  res_preprocessed:                       104
% 1.37/1.00  prep_upred:                             0
% 1.37/1.00  prep_unflattend:                        33
% 1.37/1.00  smt_new_axioms:                         0
% 1.37/1.00  pred_elim_cands:                        4
% 1.37/1.00  pred_elim:                              7
% 1.37/1.00  pred_elim_cl:                           9
% 1.37/1.00  pred_elim_cycles:                       9
% 1.37/1.00  merged_defs:                            2
% 1.37/1.00  merged_defs_ncl:                        0
% 1.37/1.00  bin_hyper_res:                          2
% 1.37/1.00  prep_cycles:                            4
% 1.37/1.00  pred_elim_time:                         0.021
% 1.37/1.00  splitting_time:                         0.
% 1.37/1.00  sem_filter_time:                        0.
% 1.37/1.00  monotx_time:                            0.
% 1.37/1.00  subtype_inf_time:                       0.
% 1.37/1.00  
% 1.37/1.00  ------ Problem properties
% 1.37/1.00  
% 1.37/1.00  clauses:                                17
% 1.37/1.00  conjectures:                            3
% 1.37/1.00  epr:                                    5
% 1.37/1.00  horn:                                   11
% 1.37/1.00  ground:                                 3
% 1.37/1.00  unary:                                  5
% 1.37/1.00  binary:                                 2
% 1.37/1.00  lits:                                   55
% 1.37/1.00  lits_eq:                                12
% 1.37/1.00  fd_pure:                                0
% 1.37/1.00  fd_pseudo:                              0
% 1.37/1.00  fd_cond:                                0
% 1.37/1.00  fd_pseudo_cond:                         0
% 1.37/1.00  ac_symbols:                             0
% 1.37/1.00  
% 1.37/1.00  ------ Propositional Solver
% 1.37/1.00  
% 1.37/1.00  prop_solver_calls:                      25
% 1.37/1.00  prop_fast_solver_calls:                 992
% 1.37/1.00  smt_solver_calls:                       0
% 1.37/1.00  smt_fast_solver_calls:                  0
% 1.37/1.00  prop_num_of_clauses:                    670
% 1.37/1.00  prop_preprocess_simplified:             3358
% 1.37/1.00  prop_fo_subsumed:                       14
% 1.37/1.00  prop_solver_time:                       0.
% 1.37/1.00  smt_solver_time:                        0.
% 1.37/1.00  smt_fast_solver_time:                   0.
% 1.37/1.00  prop_fast_solver_time:                  0.
% 1.37/1.00  prop_unsat_core_time:                   0.
% 1.37/1.00  
% 1.37/1.00  ------ QBF
% 1.37/1.00  
% 1.37/1.00  qbf_q_res:                              0
% 1.37/1.00  qbf_num_tautologies:                    0
% 1.37/1.00  qbf_prep_cycles:                        0
% 1.37/1.00  
% 1.37/1.00  ------ BMC1
% 1.37/1.00  
% 1.37/1.00  bmc1_current_bound:                     -1
% 1.37/1.00  bmc1_last_solved_bound:                 -1
% 1.37/1.00  bmc1_unsat_core_size:                   -1
% 1.37/1.00  bmc1_unsat_core_parents_size:           -1
% 1.37/1.00  bmc1_merge_next_fun:                    0
% 1.37/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.37/1.00  
% 1.37/1.00  ------ Instantiation
% 1.37/1.00  
% 1.37/1.00  inst_num_of_clauses:                    170
% 1.37/1.00  inst_num_in_passive:                    25
% 1.37/1.00  inst_num_in_active:                     101
% 1.37/1.00  inst_num_in_unprocessed:                44
% 1.37/1.00  inst_num_of_loops:                      120
% 1.37/1.00  inst_num_of_learning_restarts:          0
% 1.37/1.00  inst_num_moves_active_passive:          16
% 1.37/1.00  inst_lit_activity:                      0
% 1.37/1.00  inst_lit_activity_moves:                0
% 1.37/1.00  inst_num_tautologies:                   0
% 1.37/1.00  inst_num_prop_implied:                  0
% 1.37/1.00  inst_num_existing_simplified:           0
% 1.37/1.00  inst_num_eq_res_simplified:             0
% 1.37/1.00  inst_num_child_elim:                    0
% 1.37/1.00  inst_num_of_dismatching_blockings:      7
% 1.37/1.00  inst_num_of_non_proper_insts:           107
% 1.37/1.00  inst_num_of_duplicates:                 0
% 1.37/1.00  inst_inst_num_from_inst_to_res:         0
% 1.37/1.00  inst_dismatching_checking_time:         0.
% 1.37/1.00  
% 1.37/1.00  ------ Resolution
% 1.37/1.00  
% 1.37/1.00  res_num_of_clauses:                     0
% 1.37/1.00  res_num_in_passive:                     0
% 1.37/1.00  res_num_in_active:                      0
% 1.37/1.00  res_num_of_loops:                       108
% 1.37/1.00  res_forward_subset_subsumed:            7
% 1.37/1.00  res_backward_subset_subsumed:           0
% 1.37/1.00  res_forward_subsumed:                   0
% 1.37/1.00  res_backward_subsumed:                  0
% 1.37/1.00  res_forward_subsumption_resolution:     0
% 1.37/1.00  res_backward_subsumption_resolution:    0
% 1.37/1.00  res_clause_to_clause_subsumption:       308
% 1.37/1.00  res_orphan_elimination:                 0
% 1.37/1.00  res_tautology_del:                      19
% 1.37/1.00  res_num_eq_res_simplified:              0
% 1.37/1.00  res_num_sel_changes:                    0
% 1.37/1.00  res_moves_from_active_to_pass:          0
% 1.37/1.00  
% 1.37/1.00  ------ Superposition
% 1.37/1.00  
% 1.37/1.00  sup_time_total:                         0.
% 1.37/1.00  sup_time_generating:                    0.
% 1.37/1.00  sup_time_sim_full:                      0.
% 1.37/1.00  sup_time_sim_immed:                     0.
% 1.37/1.00  
% 1.37/1.00  sup_num_of_clauses:                     26
% 1.37/1.00  sup_num_in_active:                      22
% 1.37/1.00  sup_num_in_passive:                     4
% 1.37/1.00  sup_num_of_loops:                       22
% 1.37/1.00  sup_fw_superposition:                   7
% 1.37/1.00  sup_bw_superposition:                   8
% 1.37/1.00  sup_immediate_simplified:               5
% 1.37/1.00  sup_given_eliminated:                   0
% 1.37/1.00  comparisons_done:                       0
% 1.37/1.00  comparisons_avoided:                    0
% 1.37/1.00  
% 1.37/1.00  ------ Simplifications
% 1.37/1.00  
% 1.37/1.00  
% 1.37/1.00  sim_fw_subset_subsumed:                 5
% 1.37/1.00  sim_bw_subset_subsumed:                 1
% 1.37/1.00  sim_fw_subsumed:                        0
% 1.37/1.00  sim_bw_subsumed:                        0
% 1.37/1.00  sim_fw_subsumption_res:                 0
% 1.37/1.00  sim_bw_subsumption_res:                 0
% 1.37/1.00  sim_tautology_del:                      4
% 1.37/1.00  sim_eq_tautology_del:                   4
% 1.37/1.00  sim_eq_res_simp:                        0
% 1.37/1.00  sim_fw_demodulated:                     4
% 1.37/1.00  sim_bw_demodulated:                     0
% 1.37/1.00  sim_light_normalised:                   6
% 1.37/1.00  sim_joinable_taut:                      0
% 1.37/1.00  sim_joinable_simp:                      0
% 1.37/1.00  sim_ac_normalised:                      0
% 1.37/1.00  sim_smt_subsumption:                    0
% 1.37/1.00  
%------------------------------------------------------------------------------
