%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2046+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:04 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 495 expanded)
%              Number of clauses        :   68 ( 174 expanded)
%              Number of leaves         :   16 ( 115 expanded)
%              Depth                    :   17
%              Number of atoms          :  385 (1590 expanded)
%              Number of equality atoms :   80 ( 209 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f34])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( l1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
             => ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_waybel_7(X0,X2,X1)
                  | ~ r1_tarski(k1_yellow19(X0,X1),X2) )
                & ( r1_tarski(k1_yellow19(X0,X1),X2)
                  | ~ r2_waybel_7(X0,X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X2,X1)
      | ~ r1_tarski(k1_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_waybel_7(X0,k1_yellow19(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r2_waybel_7(X0,k1_yellow19(X0,X1),X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ r2_waybel_7(X0,k1_yellow19(X0,sK2),sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r2_waybel_7(sK1,k1_yellow19(sK1,X1),X1)
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r2_waybel_7(sK1,k1_yellow19(sK1,sK2),sK2)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f39,f38])).

fof(f61,plain,(
    ~ r2_waybel_7(sK1,k1_yellow19(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0))) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_8,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1018,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | l1_orders_2(g1_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1021,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | l1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1457,plain,
    ( l1_orders_2(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1018,c_1021])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1022,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | l1_orders_2(X0) != iProver_top
    | v1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1744,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),u1_orders_2(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))))) = g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))
    | v1_orders_2(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1457,c_1022])).

cnf(c_1129,plain,
    ( ~ m1_subset_1(sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | l1_orders_2(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1130,plain,
    ( m1_subset_1(sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_orders_2(g1_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1160,plain,
    ( ~ m1_subset_1(sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_orders_2(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1214,plain,
    ( ~ l1_orders_2(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))))
    | ~ v1_orders_2(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))))
    | g1_orders_2(u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),u1_orders_2(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))))) = g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1976,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),u1_orders_2(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))))) = g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1744,c_1129,c_1130,c_1160,c_1214])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1016,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1982,plain,
    ( g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) = X1
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1976,c_1016])).

cnf(c_7,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1215,plain,
    ( m1_subset_1(u1_orders_2(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))))))
    | ~ l1_orders_2(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1983,plain,
    ( g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) = X1
    | m1_subset_1(u1_orders_2(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1976,c_1016])).

cnf(c_2013,plain,
    ( ~ m1_subset_1(u1_orders_2(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))))))
    | g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1983])).

cnf(c_2161,plain,
    ( u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) = X1
    | g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) != g1_orders_2(X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1982,c_1129,c_1130,c_1215,c_2013])).

cnf(c_2162,plain,
    ( g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) = X1 ),
    inference(renaming,[status(thm)],[c_2161])).

cnf(c_2167,plain,
    ( u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) = X0 ),
    inference(equality_resolution,[status(thm)],[c_2162])).

cnf(c_6,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_324,plain,
    ( ~ l1_orders_2(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_6,c_1])).

cnf(c_1013,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_1745,plain,
    ( k2_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) = u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) ),
    inference(superposition,[status(thm)],[c_1457,c_1013])).

cnf(c_2333,plain,
    ( k2_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) = X0 ),
    inference(demodulation,[status(thm)],[c_2167,c_1745])).

cnf(c_5,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_313,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_6,c_5])).

cnf(c_1014,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_2494,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))))) = iProver_top
    | l1_orders_2(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2333,c_1014])).

cnf(c_2495,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
    | l1_orders_2(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2494,c_2167])).

cnf(c_1131,plain,
    ( m1_subset_1(sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | l1_orders_2(g1_orders_2(X0,sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1129])).

cnf(c_1135,plain,
    ( m1_subset_1(sK0(k1_zfmisc_1(k2_zfmisc_1(X0,X0))),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1130])).

cnf(c_2627,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2495,c_1131,c_1135])).

cnf(c_13,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_164,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( r2_waybel_7(X0,X1,X2)
    | ~ r1_tarski(k1_yellow19(X0,X2),X1)
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_16,negated_conjecture,
    ( ~ r2_waybel_7(sK1,k1_yellow19(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_402,plain,
    ( ~ r1_tarski(k1_yellow19(X0,X1),X2)
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k1_yellow19(sK1,sK2) != X2
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_16])).

cnf(c_403,plain,
    ( ~ r1_tarski(k1_yellow19(sK1,sK2),k1_yellow19(sK1,sK2))
    | ~ v13_waybel_0(k1_yellow19(sK1,sK2),k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_405,plain,
    ( ~ r1_tarski(k1_yellow19(sK1,sK2),k1_yellow19(sK1,sK2))
    | ~ v13_waybel_0(k1_yellow19(sK1,sK2),k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_20,c_19,c_18,c_17])).

cnf(c_424,plain,
    ( ~ v13_waybel_0(k1_yellow19(sK1,sK2),k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | k1_yellow19(sK1,sK2) != X1
    | k1_yellow19(sK1,sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_164,c_405])).

cnf(c_425,plain,
    ( ~ v13_waybel_0(k1_yellow19(sK1,sK2),k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(k1_yellow19(sK1,sK2)))
    | ~ m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_1012,plain,
    ( v13_waybel_0(k1_yellow19(sK1,sK2),k3_yellow_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(k1_yellow19(sK1,sK2))) != iProver_top
    | m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_24,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_426,plain,
    ( v13_waybel_0(k1_yellow19(sK1,sK2),k3_yellow_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(k1_yellow19(sK1,sK2))) != iProver_top
    | m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_9,plain,
    ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_478,plain,
    ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_479,plain,
    ( v13_waybel_0(k1_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_483,plain,
    ( v13_waybel_0(k1_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_20,c_19])).

cnf(c_1109,plain,
    ( v13_waybel_0(k1_yellow19(sK1,sK2),k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_1110,plain,
    ( v13_waybel_0(k1_yellow19(sK1,sK2),k3_yellow_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1109])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_yellow19(X1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_yellow19(X1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_18])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k1_yellow19(sK1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k1_yellow19(sK1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_20,c_19])).

cnf(c_1112,plain,
    ( m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_501])).

cnf(c_1113,plain,
    ( m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1112])).

cnf(c_1155,plain,
    ( m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(k1_yellow19(sK1,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1012,c_24,c_426,c_1110,c_1113])).

cnf(c_2636,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2627,c_1155])).


%------------------------------------------------------------------------------
