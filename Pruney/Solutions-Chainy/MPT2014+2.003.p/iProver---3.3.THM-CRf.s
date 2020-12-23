%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:41 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 600 expanded)
%              Number of clauses        :   66 ( 154 expanded)
%              Number of leaves         :   13 ( 184 expanded)
%              Depth                    :   20
%              Number of atoms          :  461 (3077 expanded)
%              Number of equality atoms :  119 ( 230 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,sK4)),u1_struct_0(X1))
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,sK3,X2)),u1_struct_0(sK3))
            & m1_subset_1(X2,u1_struct_0(sK3)) )
        & l1_waybel_0(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK2,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_waybel_0(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_struct_0(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f37,f36,f35])).

fof(f53,plain,(
    l1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f51,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X2))
        & l1_waybel_0(X2,X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ? [X4] :
              ( r1_orders_2(X2,X3,X4)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ? [X5] :
              ( r1_orders_2(X2,X3,X5)
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X3,X2,X0] :
      ( ? [X5] :
          ( r1_orders_2(X2,X3,X5)
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X2)) )
     => ( r1_orders_2(X2,X3,sK1(X0,X2,X3))
        & sK1(X0,X2,X3) = X0
        & m1_subset_1(sK1(X0,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ( r1_orders_2(X2,X3,sK1(X0,X2,X3))
            & sK1(X0,X2,X3) = X0
            & m1_subset_1(sK1(X0,X2,X3),u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK1(X0,X2,X3),u1_struct_0(X2))
      | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & ~ v1_xboole_0(u1_waybel_0(X0,X1))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_waybel_0(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( sK1(X0,X2,X3) = X0
      | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_13,negated_conjecture,
    ( l1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_370,negated_conjecture,
    ( l1_waybel_0(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_716,plain,
    ( l1_waybel_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_371,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_715,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_10,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1)
    | u1_struct_0(k4_waybel_9(X1,X0,X2)) = a_3_0_waybel_9(X1,X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_372,plain,
    ( ~ l1_waybel_0(X0_47,X1_47)
    | ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | v2_struct_0(X1_47)
    | ~ l1_struct_0(X1_47)
    | u1_struct_0(k4_waybel_9(X1_47,X0_47,X0_48)) = a_3_0_waybel_9(X1_47,X0_47,X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_714,plain,
    ( u1_struct_0(k4_waybel_9(X0_47,X1_47,X0_48)) = a_3_0_waybel_9(X0_47,X1_47,X0_48)
    | l1_waybel_0(X1_47,X0_47) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(X1_47)) != iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_struct_0(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_1109,plain,
    ( u1_struct_0(k4_waybel_9(X0_47,sK3,sK4)) = a_3_0_waybel_9(X0_47,sK3,sK4)
    | l1_waybel_0(sK3,X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_struct_0(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_714])).

cnf(c_14,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_19,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1219,plain,
    ( v2_struct_0(X0_47) = iProver_top
    | l1_waybel_0(sK3,X0_47) != iProver_top
    | u1_struct_0(k4_waybel_9(X0_47,sK3,sK4)) = a_3_0_waybel_9(X0_47,sK3,sK4)
    | l1_struct_0(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1109,c_19])).

cnf(c_1220,plain,
    ( u1_struct_0(k4_waybel_9(X0_47,sK3,sK4)) = a_3_0_waybel_9(X0_47,sK3,sK4)
    | l1_waybel_0(sK3,X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_struct_0(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_1219])).

cnf(c_1227,plain,
    ( u1_struct_0(k4_waybel_9(sK2,sK3,sK4)) = a_3_0_waybel_9(sK2,sK3,sK4)
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_1220])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_15,negated_conjecture,
    ( l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_893,plain,
    ( ~ l1_waybel_0(X0_47,sK2)
    | ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | u1_struct_0(k4_waybel_9(sK2,X0_47,X0_48)) = a_3_0_waybel_9(sK2,X0_47,X0_48) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_895,plain,
    ( ~ l1_waybel_0(sK3,sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | u1_struct_0(k4_waybel_9(sK2,sK3,sK4)) = a_3_0_waybel_9(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_893])).

cnf(c_1230,plain,
    ( u1_struct_0(k4_waybel_9(sK2,sK3,sK4)) = a_3_0_waybel_9(sK2,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1227,c_16,c_15,c_14,c_13,c_12,c_895])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_190,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | u1_struct_0(k4_waybel_9(sK2,sK3,sK4)) != X0
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_191,plain,
    ( r2_hidden(sK0(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3)),u1_struct_0(k4_waybel_9(sK2,sK3,sK4))) ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_366,plain,
    ( r2_hidden(sK0(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3)),u1_struct_0(k4_waybel_9(sK2,sK3,sK4))) ),
    inference(subtyping,[status(esa)],[c_191])).

cnf(c_720,plain,
    ( r2_hidden(sK0(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3)),u1_struct_0(k4_waybel_9(sK2,sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_1233,plain,
    ( r2_hidden(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),a_3_0_waybel_9(sK2,sK3,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1230,c_720])).

cnf(c_9,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X3,X0,X2),u1_struct_0(X0))
    | ~ r2_hidden(X3,a_3_0_waybel_9(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_373,plain,
    ( ~ l1_waybel_0(X0_47,X1_47)
    | ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
    | m1_subset_1(sK1(X1_48,X0_47,X0_48),u1_struct_0(X0_47))
    | ~ r2_hidden(X1_48,a_3_0_waybel_9(X1_47,X0_47,X0_48))
    | v2_struct_0(X0_47)
    | v2_struct_0(X1_47)
    | ~ l1_struct_0(X1_47) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_713,plain,
    ( l1_waybel_0(X0_47,X1_47) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
    | m1_subset_1(sK1(X1_48,X0_47,X0_48),u1_struct_0(X0_47)) = iProver_top
    | r2_hidden(X1_48,a_3_0_waybel_9(X1_47,X0_47,X0_48)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | l1_struct_0(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_1557,plain,
    ( l1_waybel_0(sK3,sK2) != iProver_top
    | m1_subset_1(sK1(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),sK3,sK4),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_713])).

cnf(c_17,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_20,plain,
    ( l1_waybel_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_21,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1912,plain,
    ( m1_subset_1(sK1(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),sK3,sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1557,c_17,c_18,c_19,c_20,c_21])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0_48,X1_48)
    | r2_hidden(X0_48,X1_48)
    | v1_xboole_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_708,plain,
    ( m1_subset_1(X0_48,X1_48) != iProver_top
    | r2_hidden(X0_48,X1_48) = iProver_top
    | v1_xboole_0(X1_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_1917,plain,
    ( r2_hidden(sK1(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),sK3,sK4),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_708])).

cnf(c_4,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_376,plain,
    ( ~ l1_waybel_0(X0_47,X1_47)
    | m1_subset_1(u1_waybel_0(X1_47,X0_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
    | ~ l1_struct_0(X1_47) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_710,plain,
    ( l1_waybel_0(X0_47,X1_47) != iProver_top
    | m1_subset_1(u1_waybel_0(X1_47,X0_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) = iProver_top
    | l1_struct_0(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ v1_xboole_0(X1_48)
    | v1_xboole_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_709,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | v1_xboole_0(X1_48) != iProver_top
    | v1_xboole_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_1012,plain,
    ( l1_waybel_0(X0_47,X1_47) != iProver_top
    | l1_struct_0(X1_47) != iProver_top
    | v1_xboole_0(u1_waybel_0(X1_47,X0_47)) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_47)) != iProver_top ),
    inference(superposition,[status(thm)],[c_710,c_709])).

cnf(c_5,plain,
    ( ~ l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_waybel_0(X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_375,plain,
    ( ~ l1_waybel_0(X0_47,X1_47)
    | v2_struct_0(X0_47)
    | v2_struct_0(X1_47)
    | ~ l1_struct_0(X1_47)
    | ~ v1_xboole_0(u1_waybel_0(X1_47,X0_47)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_711,plain,
    ( l1_waybel_0(X0_47,X1_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | l1_struct_0(X1_47) != iProver_top
    | v1_xboole_0(u1_waybel_0(X1_47,X0_47)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_1655,plain,
    ( l1_waybel_0(X0_47,X1_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | l1_struct_0(X1_47) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_47)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1012,c_711])).

cnf(c_1665,plain,
    ( v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_1655])).

cnf(c_2121,plain,
    ( r2_hidden(sK1(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),sK3,sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1917,c_17,c_18,c_19,c_1665])).

cnf(c_8,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X3,a_3_0_waybel_9(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1)
    | sK1(X3,X0,X2) = X3 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_374,plain,
    ( ~ l1_waybel_0(X0_47,X1_47)
    | ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
    | ~ r2_hidden(X1_48,a_3_0_waybel_9(X1_47,X0_47,X0_48))
    | v2_struct_0(X0_47)
    | v2_struct_0(X1_47)
    | ~ l1_struct_0(X1_47)
    | sK1(X1_48,X0_47,X0_48) = X1_48 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_712,plain,
    ( sK1(X0_48,X0_47,X1_48) = X0_48
    | l1_waybel_0(X0_47,X1_47) != iProver_top
    | m1_subset_1(X1_48,u1_struct_0(X0_47)) != iProver_top
    | r2_hidden(X0_48,a_3_0_waybel_9(X1_47,X0_47,X1_48)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(X1_47) = iProver_top
    | l1_struct_0(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_1355,plain,
    ( sK1(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),sK3,sK4) = sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3))
    | l1_waybel_0(sK3,sK2) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_712])).

cnf(c_2022,plain,
    ( sK1(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),sK3,sK4) = sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1355,c_17,c_18,c_19,c_20,c_21])).

cnf(c_2125,plain,
    ( r2_hidden(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2121,c_2022])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_197,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | u1_struct_0(k4_waybel_9(sK2,sK3,sK4)) != X0
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_198,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_365,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_198])).

cnf(c_721,plain,
    ( r2_hidden(sK0(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_1234,plain,
    ( r2_hidden(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1230,c_721])).

cnf(c_2127,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2125,c_1234])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n022.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 17:55:56 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 1.64/0.93  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/0.93  
% 1.64/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.64/0.93  
% 1.64/0.93  ------  iProver source info
% 1.64/0.93  
% 1.64/0.93  git: date: 2020-06-30 10:37:57 +0100
% 1.64/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.64/0.93  git: non_committed_changes: false
% 1.64/0.93  git: last_make_outside_of_git: false
% 1.64/0.93  
% 1.64/0.93  ------ 
% 1.64/0.93  
% 1.64/0.93  ------ Input Options
% 1.64/0.93  
% 1.64/0.93  --out_options                           all
% 1.64/0.93  --tptp_safe_out                         true
% 1.64/0.93  --problem_path                          ""
% 1.64/0.93  --include_path                          ""
% 1.64/0.93  --clausifier                            res/vclausify_rel
% 1.64/0.93  --clausifier_options                    --mode clausify
% 1.64/0.93  --stdin                                 false
% 1.64/0.93  --stats_out                             all
% 1.64/0.93  
% 1.64/0.93  ------ General Options
% 1.64/0.93  
% 1.64/0.93  --fof                                   false
% 1.64/0.93  --time_out_real                         305.
% 1.64/0.93  --time_out_virtual                      -1.
% 1.64/0.93  --symbol_type_check                     false
% 1.64/0.93  --clausify_out                          false
% 1.64/0.93  --sig_cnt_out                           false
% 1.64/0.93  --trig_cnt_out                          false
% 1.64/0.93  --trig_cnt_out_tolerance                1.
% 1.64/0.93  --trig_cnt_out_sk_spl                   false
% 1.64/0.93  --abstr_cl_out                          false
% 1.64/0.93  
% 1.64/0.93  ------ Global Options
% 1.64/0.93  
% 1.64/0.93  --schedule                              default
% 1.64/0.93  --add_important_lit                     false
% 1.64/0.93  --prop_solver_per_cl                    1000
% 1.64/0.93  --min_unsat_core                        false
% 1.64/0.93  --soft_assumptions                      false
% 1.64/0.93  --soft_lemma_size                       3
% 1.64/0.93  --prop_impl_unit_size                   0
% 1.64/0.93  --prop_impl_unit                        []
% 1.64/0.93  --share_sel_clauses                     true
% 1.64/0.93  --reset_solvers                         false
% 1.64/0.93  --bc_imp_inh                            [conj_cone]
% 1.64/0.93  --conj_cone_tolerance                   3.
% 1.64/0.93  --extra_neg_conj                        none
% 1.64/0.93  --large_theory_mode                     true
% 1.64/0.93  --prolific_symb_bound                   200
% 1.64/0.93  --lt_threshold                          2000
% 1.64/0.93  --clause_weak_htbl                      true
% 1.64/0.93  --gc_record_bc_elim                     false
% 1.64/0.93  
% 1.64/0.93  ------ Preprocessing Options
% 1.64/0.93  
% 1.64/0.93  --preprocessing_flag                    true
% 1.64/0.93  --time_out_prep_mult                    0.1
% 1.64/0.93  --splitting_mode                        input
% 1.64/0.93  --splitting_grd                         true
% 1.64/0.93  --splitting_cvd                         false
% 1.64/0.93  --splitting_cvd_svl                     false
% 1.64/0.93  --splitting_nvd                         32
% 1.64/0.93  --sub_typing                            true
% 1.64/0.93  --prep_gs_sim                           true
% 1.64/0.93  --prep_unflatten                        true
% 1.64/0.93  --prep_res_sim                          true
% 1.64/0.93  --prep_upred                            true
% 1.64/0.93  --prep_sem_filter                       exhaustive
% 1.64/0.93  --prep_sem_filter_out                   false
% 1.64/0.93  --pred_elim                             true
% 1.64/0.93  --res_sim_input                         true
% 1.64/0.93  --eq_ax_congr_red                       true
% 1.64/0.93  --pure_diseq_elim                       true
% 1.64/0.93  --brand_transform                       false
% 1.64/0.93  --non_eq_to_eq                          false
% 1.64/0.93  --prep_def_merge                        true
% 1.64/0.93  --prep_def_merge_prop_impl              false
% 1.64/0.93  --prep_def_merge_mbd                    true
% 1.64/0.93  --prep_def_merge_tr_red                 false
% 1.64/0.93  --prep_def_merge_tr_cl                  false
% 1.64/0.93  --smt_preprocessing                     true
% 1.64/0.93  --smt_ac_axioms                         fast
% 1.64/0.93  --preprocessed_out                      false
% 1.64/0.93  --preprocessed_stats                    false
% 1.64/0.93  
% 1.64/0.93  ------ Abstraction refinement Options
% 1.64/0.93  
% 1.64/0.93  --abstr_ref                             []
% 1.64/0.93  --abstr_ref_prep                        false
% 1.64/0.93  --abstr_ref_until_sat                   false
% 1.64/0.93  --abstr_ref_sig_restrict                funpre
% 1.64/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 1.64/0.93  --abstr_ref_under                       []
% 1.64/0.93  
% 1.64/0.93  ------ SAT Options
% 1.64/0.93  
% 1.64/0.93  --sat_mode                              false
% 1.64/0.93  --sat_fm_restart_options                ""
% 1.64/0.93  --sat_gr_def                            false
% 1.64/0.93  --sat_epr_types                         true
% 1.64/0.93  --sat_non_cyclic_types                  false
% 1.64/0.93  --sat_finite_models                     false
% 1.64/0.93  --sat_fm_lemmas                         false
% 1.64/0.93  --sat_fm_prep                           false
% 1.64/0.93  --sat_fm_uc_incr                        true
% 1.64/0.93  --sat_out_model                         small
% 1.64/0.93  --sat_out_clauses                       false
% 1.64/0.93  
% 1.64/0.93  ------ QBF Options
% 1.64/0.93  
% 1.64/0.93  --qbf_mode                              false
% 1.64/0.93  --qbf_elim_univ                         false
% 1.64/0.93  --qbf_dom_inst                          none
% 1.64/0.93  --qbf_dom_pre_inst                      false
% 1.64/0.93  --qbf_sk_in                             false
% 1.64/0.93  --qbf_pred_elim                         true
% 1.64/0.93  --qbf_split                             512
% 1.64/0.93  
% 1.64/0.93  ------ BMC1 Options
% 1.64/0.93  
% 1.64/0.93  --bmc1_incremental                      false
% 1.64/0.93  --bmc1_axioms                           reachable_all
% 1.64/0.93  --bmc1_min_bound                        0
% 1.64/0.93  --bmc1_max_bound                        -1
% 1.64/0.93  --bmc1_max_bound_default                -1
% 1.64/0.93  --bmc1_symbol_reachability              true
% 1.64/0.93  --bmc1_property_lemmas                  false
% 1.64/0.93  --bmc1_k_induction                      false
% 1.64/0.93  --bmc1_non_equiv_states                 false
% 1.64/0.93  --bmc1_deadlock                         false
% 1.64/0.93  --bmc1_ucm                              false
% 1.64/0.93  --bmc1_add_unsat_core                   none
% 1.64/0.93  --bmc1_unsat_core_children              false
% 1.64/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 1.64/0.93  --bmc1_out_stat                         full
% 1.64/0.93  --bmc1_ground_init                      false
% 1.64/0.93  --bmc1_pre_inst_next_state              false
% 1.64/0.93  --bmc1_pre_inst_state                   false
% 1.64/0.93  --bmc1_pre_inst_reach_state             false
% 1.64/0.93  --bmc1_out_unsat_core                   false
% 1.64/0.93  --bmc1_aig_witness_out                  false
% 1.64/0.93  --bmc1_verbose                          false
% 1.64/0.93  --bmc1_dump_clauses_tptp                false
% 1.64/0.93  --bmc1_dump_unsat_core_tptp             false
% 1.64/0.93  --bmc1_dump_file                        -
% 1.64/0.93  --bmc1_ucm_expand_uc_limit              128
% 1.64/0.93  --bmc1_ucm_n_expand_iterations          6
% 1.64/0.93  --bmc1_ucm_extend_mode                  1
% 1.64/0.93  --bmc1_ucm_init_mode                    2
% 1.64/0.93  --bmc1_ucm_cone_mode                    none
% 1.64/0.93  --bmc1_ucm_reduced_relation_type        0
% 1.64/0.93  --bmc1_ucm_relax_model                  4
% 1.64/0.93  --bmc1_ucm_full_tr_after_sat            true
% 1.64/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 1.64/0.93  --bmc1_ucm_layered_model                none
% 1.64/0.93  --bmc1_ucm_max_lemma_size               10
% 1.64/0.93  
% 1.64/0.93  ------ AIG Options
% 1.64/0.93  
% 1.64/0.93  --aig_mode                              false
% 1.64/0.93  
% 1.64/0.93  ------ Instantiation Options
% 1.64/0.93  
% 1.64/0.93  --instantiation_flag                    true
% 1.64/0.93  --inst_sos_flag                         false
% 1.64/0.93  --inst_sos_phase                        true
% 1.64/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.64/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.64/0.93  --inst_lit_sel_side                     num_symb
% 1.64/0.93  --inst_solver_per_active                1400
% 1.64/0.93  --inst_solver_calls_frac                1.
% 1.64/0.93  --inst_passive_queue_type               priority_queues
% 1.64/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.64/0.93  --inst_passive_queues_freq              [25;2]
% 1.64/0.93  --inst_dismatching                      true
% 1.64/0.93  --inst_eager_unprocessed_to_passive     true
% 1.64/0.93  --inst_prop_sim_given                   true
% 1.64/0.93  --inst_prop_sim_new                     false
% 1.64/0.93  --inst_subs_new                         false
% 1.64/0.93  --inst_eq_res_simp                      false
% 1.64/0.93  --inst_subs_given                       false
% 1.64/0.93  --inst_orphan_elimination               true
% 1.64/0.93  --inst_learning_loop_flag               true
% 1.64/0.93  --inst_learning_start                   3000
% 1.64/0.93  --inst_learning_factor                  2
% 1.64/0.93  --inst_start_prop_sim_after_learn       3
% 1.64/0.93  --inst_sel_renew                        solver
% 1.64/0.93  --inst_lit_activity_flag                true
% 1.64/0.93  --inst_restr_to_given                   false
% 1.64/0.93  --inst_activity_threshold               500
% 1.64/0.93  --inst_out_proof                        true
% 1.64/0.93  
% 1.64/0.93  ------ Resolution Options
% 1.64/0.93  
% 1.64/0.93  --resolution_flag                       true
% 1.64/0.93  --res_lit_sel                           adaptive
% 1.64/0.93  --res_lit_sel_side                      none
% 1.64/0.93  --res_ordering                          kbo
% 1.64/0.93  --res_to_prop_solver                    active
% 1.64/0.93  --res_prop_simpl_new                    false
% 1.64/0.93  --res_prop_simpl_given                  true
% 1.64/0.93  --res_passive_queue_type                priority_queues
% 1.64/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.64/0.93  --res_passive_queues_freq               [15;5]
% 1.64/0.93  --res_forward_subs                      full
% 1.64/0.93  --res_backward_subs                     full
% 1.64/0.93  --res_forward_subs_resolution           true
% 1.64/0.93  --res_backward_subs_resolution          true
% 1.64/0.93  --res_orphan_elimination                true
% 1.64/0.93  --res_time_limit                        2.
% 1.64/0.93  --res_out_proof                         true
% 1.64/0.93  
% 1.64/0.93  ------ Superposition Options
% 1.64/0.93  
% 1.64/0.93  --superposition_flag                    true
% 1.64/0.93  --sup_passive_queue_type                priority_queues
% 1.64/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.64/0.93  --sup_passive_queues_freq               [8;1;4]
% 1.64/0.93  --demod_completeness_check              fast
% 1.64/0.93  --demod_use_ground                      true
% 1.64/0.93  --sup_to_prop_solver                    passive
% 1.64/0.93  --sup_prop_simpl_new                    true
% 1.64/0.93  --sup_prop_simpl_given                  true
% 1.64/0.93  --sup_fun_splitting                     false
% 1.64/0.93  --sup_smt_interval                      50000
% 1.64/0.93  
% 1.64/0.93  ------ Superposition Simplification Setup
% 1.64/0.93  
% 1.64/0.93  --sup_indices_passive                   []
% 1.64/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 1.64/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/0.93  --sup_full_bw                           [BwDemod]
% 1.64/0.93  --sup_immed_triv                        [TrivRules]
% 1.64/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.64/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/0.93  --sup_immed_bw_main                     []
% 1.64/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.64/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 1.64/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.64/0.93  
% 1.64/0.93  ------ Combination Options
% 1.64/0.93  
% 1.64/0.93  --comb_res_mult                         3
% 1.64/0.93  --comb_sup_mult                         2
% 1.64/0.93  --comb_inst_mult                        10
% 1.64/0.93  
% 1.64/0.93  ------ Debug Options
% 1.64/0.93  
% 1.64/0.93  --dbg_backtrace                         false
% 1.64/0.93  --dbg_dump_prop_clauses                 false
% 1.64/0.93  --dbg_dump_prop_clauses_file            -
% 1.64/0.93  --dbg_out_stat                          false
% 1.64/0.93  ------ Parsing...
% 1.64/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.64/0.93  
% 1.64/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.64/0.93  
% 1.64/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.64/0.93  
% 1.64/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.64/0.93  ------ Proving...
% 1.64/0.93  ------ Problem Properties 
% 1.64/0.93  
% 1.64/0.93  
% 1.64/0.93  clauses                                 15
% 1.64/0.93  conjectures                             5
% 1.64/0.93  EPR                                     5
% 1.64/0.93  Horn                                    9
% 1.64/0.93  unary                                   7
% 1.64/0.93  binary                                  0
% 1.64/0.93  lits                                    51
% 1.64/0.93  lits eq                                 2
% 1.64/0.93  fd_pure                                 0
% 1.64/0.93  fd_pseudo                               0
% 1.64/0.93  fd_cond                                 0
% 1.64/0.93  fd_pseudo_cond                          0
% 1.64/0.93  AC symbols                              0
% 1.64/0.93  
% 1.64/0.93  ------ Schedule dynamic 5 is on 
% 1.64/0.93  
% 1.64/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.64/0.93  
% 1.64/0.93  
% 1.64/0.93  ------ 
% 1.64/0.93  Current options:
% 1.64/0.93  ------ 
% 1.64/0.93  
% 1.64/0.93  ------ Input Options
% 1.64/0.93  
% 1.64/0.93  --out_options                           all
% 1.64/0.93  --tptp_safe_out                         true
% 1.64/0.93  --problem_path                          ""
% 1.64/0.93  --include_path                          ""
% 1.64/0.93  --clausifier                            res/vclausify_rel
% 1.64/0.93  --clausifier_options                    --mode clausify
% 1.64/0.93  --stdin                                 false
% 1.64/0.93  --stats_out                             all
% 1.64/0.93  
% 1.64/0.93  ------ General Options
% 1.64/0.93  
% 1.64/0.93  --fof                                   false
% 1.64/0.93  --time_out_real                         305.
% 1.64/0.93  --time_out_virtual                      -1.
% 1.64/0.93  --symbol_type_check                     false
% 1.64/0.93  --clausify_out                          false
% 1.64/0.93  --sig_cnt_out                           false
% 1.64/0.93  --trig_cnt_out                          false
% 1.64/0.93  --trig_cnt_out_tolerance                1.
% 1.64/0.93  --trig_cnt_out_sk_spl                   false
% 1.64/0.93  --abstr_cl_out                          false
% 1.64/0.93  
% 1.64/0.93  ------ Global Options
% 1.64/0.93  
% 1.64/0.93  --schedule                              default
% 1.64/0.93  --add_important_lit                     false
% 1.64/0.93  --prop_solver_per_cl                    1000
% 1.64/0.93  --min_unsat_core                        false
% 1.64/0.93  --soft_assumptions                      false
% 1.64/0.93  --soft_lemma_size                       3
% 1.64/0.93  --prop_impl_unit_size                   0
% 1.64/0.93  --prop_impl_unit                        []
% 1.64/0.93  --share_sel_clauses                     true
% 1.64/0.93  --reset_solvers                         false
% 1.64/0.93  --bc_imp_inh                            [conj_cone]
% 1.64/0.93  --conj_cone_tolerance                   3.
% 1.64/0.93  --extra_neg_conj                        none
% 1.64/0.93  --large_theory_mode                     true
% 1.64/0.93  --prolific_symb_bound                   200
% 1.64/0.93  --lt_threshold                          2000
% 1.64/0.93  --clause_weak_htbl                      true
% 1.64/0.93  --gc_record_bc_elim                     false
% 1.64/0.93  
% 1.64/0.93  ------ Preprocessing Options
% 1.64/0.93  
% 1.64/0.93  --preprocessing_flag                    true
% 1.64/0.93  --time_out_prep_mult                    0.1
% 1.64/0.93  --splitting_mode                        input
% 1.64/0.93  --splitting_grd                         true
% 1.64/0.93  --splitting_cvd                         false
% 1.64/0.93  --splitting_cvd_svl                     false
% 1.64/0.93  --splitting_nvd                         32
% 1.64/0.93  --sub_typing                            true
% 1.64/0.93  --prep_gs_sim                           true
% 1.64/0.93  --prep_unflatten                        true
% 1.64/0.93  --prep_res_sim                          true
% 1.64/0.93  --prep_upred                            true
% 1.64/0.93  --prep_sem_filter                       exhaustive
% 1.64/0.93  --prep_sem_filter_out                   false
% 1.64/0.93  --pred_elim                             true
% 1.64/0.93  --res_sim_input                         true
% 1.64/0.93  --eq_ax_congr_red                       true
% 1.64/0.93  --pure_diseq_elim                       true
% 1.64/0.93  --brand_transform                       false
% 1.64/0.93  --non_eq_to_eq                          false
% 1.64/0.93  --prep_def_merge                        true
% 1.64/0.93  --prep_def_merge_prop_impl              false
% 1.64/0.93  --prep_def_merge_mbd                    true
% 1.64/0.93  --prep_def_merge_tr_red                 false
% 1.64/0.93  --prep_def_merge_tr_cl                  false
% 1.64/0.93  --smt_preprocessing                     true
% 1.64/0.93  --smt_ac_axioms                         fast
% 1.64/0.93  --preprocessed_out                      false
% 1.64/0.93  --preprocessed_stats                    false
% 1.64/0.93  
% 1.64/0.93  ------ Abstraction refinement Options
% 1.64/0.93  
% 1.64/0.93  --abstr_ref                             []
% 1.64/0.93  --abstr_ref_prep                        false
% 1.64/0.93  --abstr_ref_until_sat                   false
% 1.64/0.93  --abstr_ref_sig_restrict                funpre
% 1.64/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 1.64/0.93  --abstr_ref_under                       []
% 1.64/0.93  
% 1.64/0.93  ------ SAT Options
% 1.64/0.93  
% 1.64/0.93  --sat_mode                              false
% 1.64/0.93  --sat_fm_restart_options                ""
% 1.64/0.93  --sat_gr_def                            false
% 1.64/0.93  --sat_epr_types                         true
% 1.64/0.93  --sat_non_cyclic_types                  false
% 1.64/0.93  --sat_finite_models                     false
% 1.64/0.93  --sat_fm_lemmas                         false
% 1.64/0.93  --sat_fm_prep                           false
% 1.64/0.93  --sat_fm_uc_incr                        true
% 1.64/0.93  --sat_out_model                         small
% 1.64/0.93  --sat_out_clauses                       false
% 1.64/0.93  
% 1.64/0.93  ------ QBF Options
% 1.64/0.93  
% 1.64/0.93  --qbf_mode                              false
% 1.64/0.93  --qbf_elim_univ                         false
% 1.64/0.93  --qbf_dom_inst                          none
% 1.64/0.93  --qbf_dom_pre_inst                      false
% 1.64/0.93  --qbf_sk_in                             false
% 1.64/0.93  --qbf_pred_elim                         true
% 1.64/0.93  --qbf_split                             512
% 1.64/0.93  
% 1.64/0.93  ------ BMC1 Options
% 1.64/0.93  
% 1.64/0.93  --bmc1_incremental                      false
% 1.64/0.93  --bmc1_axioms                           reachable_all
% 1.64/0.93  --bmc1_min_bound                        0
% 1.64/0.93  --bmc1_max_bound                        -1
% 1.64/0.93  --bmc1_max_bound_default                -1
% 1.64/0.93  --bmc1_symbol_reachability              true
% 1.64/0.93  --bmc1_property_lemmas                  false
% 1.64/0.93  --bmc1_k_induction                      false
% 1.64/0.93  --bmc1_non_equiv_states                 false
% 1.64/0.93  --bmc1_deadlock                         false
% 1.64/0.93  --bmc1_ucm                              false
% 1.64/0.93  --bmc1_add_unsat_core                   none
% 1.64/0.93  --bmc1_unsat_core_children              false
% 1.64/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 1.64/0.93  --bmc1_out_stat                         full
% 1.64/0.93  --bmc1_ground_init                      false
% 1.64/0.93  --bmc1_pre_inst_next_state              false
% 1.64/0.93  --bmc1_pre_inst_state                   false
% 1.64/0.93  --bmc1_pre_inst_reach_state             false
% 1.64/0.93  --bmc1_out_unsat_core                   false
% 1.64/0.93  --bmc1_aig_witness_out                  false
% 1.64/0.93  --bmc1_verbose                          false
% 1.64/0.93  --bmc1_dump_clauses_tptp                false
% 1.64/0.93  --bmc1_dump_unsat_core_tptp             false
% 1.64/0.93  --bmc1_dump_file                        -
% 1.64/0.93  --bmc1_ucm_expand_uc_limit              128
% 1.64/0.93  --bmc1_ucm_n_expand_iterations          6
% 1.64/0.93  --bmc1_ucm_extend_mode                  1
% 1.64/0.93  --bmc1_ucm_init_mode                    2
% 1.64/0.93  --bmc1_ucm_cone_mode                    none
% 1.64/0.93  --bmc1_ucm_reduced_relation_type        0
% 1.64/0.93  --bmc1_ucm_relax_model                  4
% 1.64/0.93  --bmc1_ucm_full_tr_after_sat            true
% 1.64/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 1.64/0.93  --bmc1_ucm_layered_model                none
% 1.64/0.93  --bmc1_ucm_max_lemma_size               10
% 1.64/0.93  
% 1.64/0.93  ------ AIG Options
% 1.64/0.93  
% 1.64/0.93  --aig_mode                              false
% 1.64/0.93  
% 1.64/0.93  ------ Instantiation Options
% 1.64/0.93  
% 1.64/0.93  --instantiation_flag                    true
% 1.64/0.93  --inst_sos_flag                         false
% 1.64/0.93  --inst_sos_phase                        true
% 1.64/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.64/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.64/0.93  --inst_lit_sel_side                     none
% 1.64/0.93  --inst_solver_per_active                1400
% 1.64/0.93  --inst_solver_calls_frac                1.
% 1.64/0.93  --inst_passive_queue_type               priority_queues
% 1.64/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.64/0.93  --inst_passive_queues_freq              [25;2]
% 1.64/0.93  --inst_dismatching                      true
% 1.64/0.93  --inst_eager_unprocessed_to_passive     true
% 1.64/0.93  --inst_prop_sim_given                   true
% 1.64/0.93  --inst_prop_sim_new                     false
% 1.64/0.93  --inst_subs_new                         false
% 1.64/0.93  --inst_eq_res_simp                      false
% 1.64/0.93  --inst_subs_given                       false
% 1.64/0.93  --inst_orphan_elimination               true
% 1.64/0.93  --inst_learning_loop_flag               true
% 1.64/0.93  --inst_learning_start                   3000
% 1.64/0.93  --inst_learning_factor                  2
% 1.64/0.93  --inst_start_prop_sim_after_learn       3
% 1.64/0.93  --inst_sel_renew                        solver
% 1.64/0.93  --inst_lit_activity_flag                true
% 1.64/0.93  --inst_restr_to_given                   false
% 1.64/0.93  --inst_activity_threshold               500
% 1.64/0.93  --inst_out_proof                        true
% 1.64/0.93  
% 1.64/0.93  ------ Resolution Options
% 1.64/0.93  
% 1.64/0.93  --resolution_flag                       false
% 1.64/0.93  --res_lit_sel                           adaptive
% 1.64/0.93  --res_lit_sel_side                      none
% 1.64/0.93  --res_ordering                          kbo
% 1.64/0.93  --res_to_prop_solver                    active
% 1.64/0.93  --res_prop_simpl_new                    false
% 1.64/0.93  --res_prop_simpl_given                  true
% 1.64/0.93  --res_passive_queue_type                priority_queues
% 1.64/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.64/0.93  --res_passive_queues_freq               [15;5]
% 1.64/0.93  --res_forward_subs                      full
% 1.64/0.93  --res_backward_subs                     full
% 1.64/0.93  --res_forward_subs_resolution           true
% 1.64/0.93  --res_backward_subs_resolution          true
% 1.64/0.93  --res_orphan_elimination                true
% 1.64/0.93  --res_time_limit                        2.
% 1.64/0.93  --res_out_proof                         true
% 1.64/0.93  
% 1.64/0.93  ------ Superposition Options
% 1.64/0.93  
% 1.64/0.93  --superposition_flag                    true
% 1.64/0.93  --sup_passive_queue_type                priority_queues
% 1.64/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.64/0.93  --sup_passive_queues_freq               [8;1;4]
% 1.64/0.93  --demod_completeness_check              fast
% 1.64/0.93  --demod_use_ground                      true
% 1.64/0.93  --sup_to_prop_solver                    passive
% 1.64/0.93  --sup_prop_simpl_new                    true
% 1.64/0.93  --sup_prop_simpl_given                  true
% 1.64/0.93  --sup_fun_splitting                     false
% 1.64/0.93  --sup_smt_interval                      50000
% 1.64/0.93  
% 1.64/0.93  ------ Superposition Simplification Setup
% 1.64/0.93  
% 1.64/0.93  --sup_indices_passive                   []
% 1.64/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.64/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 1.64/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/0.93  --sup_full_bw                           [BwDemod]
% 1.64/0.93  --sup_immed_triv                        [TrivRules]
% 1.64/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.64/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/0.93  --sup_immed_bw_main                     []
% 1.64/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.64/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 1.64/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.64/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.64/0.93  
% 1.64/0.93  ------ Combination Options
% 1.64/0.93  
% 1.64/0.93  --comb_res_mult                         3
% 1.64/0.93  --comb_sup_mult                         2
% 1.64/0.93  --comb_inst_mult                        10
% 1.64/0.93  
% 1.64/0.93  ------ Debug Options
% 1.64/0.93  
% 1.64/0.93  --dbg_backtrace                         false
% 1.64/0.93  --dbg_dump_prop_clauses                 false
% 1.64/0.93  --dbg_dump_prop_clauses_file            -
% 1.64/0.93  --dbg_out_stat                          false
% 1.64/0.93  
% 1.64/0.93  
% 1.64/0.93  
% 1.64/0.93  
% 1.64/0.93  ------ Proving...
% 1.64/0.93  
% 1.64/0.93  
% 1.64/0.93  % SZS status Theorem for theBenchmark.p
% 1.64/0.93  
% 1.64/0.93   Resolution empty clause
% 1.64/0.93  
% 1.64/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 1.64/0.93  
% 1.64/0.93  fof(f8,conjecture,(
% 1.64/0.93    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 1.64/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f9,negated_conjecture,(
% 1.64/0.93    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 1.64/0.93    inference(negated_conjecture,[],[f8])).
% 1.64/0.93  
% 1.64/0.93  fof(f27,plain,(
% 1.64/0.93    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.64/0.93    inference(ennf_transformation,[],[f9])).
% 1.64/0.93  
% 1.64/0.93  fof(f28,plain,(
% 1.64/0.93    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.64/0.93    inference(flattening,[],[f27])).
% 1.64/0.93  
% 1.64/0.93  fof(f37,plain,(
% 1.64/0.93    ( ! [X0,X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) => (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,sK4)),u1_struct_0(X1)) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 1.64/0.93    introduced(choice_axiom,[])).
% 1.64/0.93  
% 1.64/0.93  fof(f36,plain,(
% 1.64/0.93    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,sK3,X2)),u1_struct_0(sK3)) & m1_subset_1(X2,u1_struct_0(sK3))) & l1_waybel_0(sK3,X0) & ~v2_struct_0(sK3))) )),
% 1.64/0.93    introduced(choice_axiom,[])).
% 1.64/0.93  
% 1.64/0.93  fof(f35,plain,(
% 1.64/0.93    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK2,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK2) & ~v2_struct_0(X1)) & l1_struct_0(sK2) & ~v2_struct_0(sK2))),
% 1.64/0.93    introduced(choice_axiom,[])).
% 1.64/0.93  
% 1.64/0.93  fof(f38,plain,(
% 1.64/0.93    ((~r1_tarski(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_waybel_0(sK3,sK2) & ~v2_struct_0(sK3)) & l1_struct_0(sK2) & ~v2_struct_0(sK2)),
% 1.64/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f37,f36,f35])).
% 1.64/0.93  
% 1.64/0.93  fof(f53,plain,(
% 1.64/0.93    l1_waybel_0(sK3,sK2)),
% 1.64/0.93    inference(cnf_transformation,[],[f38])).
% 1.64/0.93  
% 1.64/0.93  fof(f54,plain,(
% 1.64/0.93    m1_subset_1(sK4,u1_struct_0(sK3))),
% 1.64/0.93    inference(cnf_transformation,[],[f38])).
% 1.64/0.93  
% 1.64/0.93  fof(f7,axiom,(
% 1.64/0.93    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2))))),
% 1.64/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f25,plain,(
% 1.64/0.93    ! [X0] : (! [X1] : (! [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.64/0.93    inference(ennf_transformation,[],[f7])).
% 1.64/0.93  
% 1.64/0.93  fof(f26,plain,(
% 1.64/0.93    ! [X0] : (! [X1] : (! [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.64/0.93    inference(flattening,[],[f25])).
% 1.64/0.93  
% 1.64/0.93  fof(f49,plain,(
% 1.64/0.93    ( ! [X2,X0,X1] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f26])).
% 1.64/0.93  
% 1.64/0.93  fof(f52,plain,(
% 1.64/0.93    ~v2_struct_0(sK3)),
% 1.64/0.93    inference(cnf_transformation,[],[f38])).
% 1.64/0.93  
% 1.64/0.93  fof(f50,plain,(
% 1.64/0.93    ~v2_struct_0(sK2)),
% 1.64/0.93    inference(cnf_transformation,[],[f38])).
% 1.64/0.93  
% 1.64/0.93  fof(f51,plain,(
% 1.64/0.93    l1_struct_0(sK2)),
% 1.64/0.93    inference(cnf_transformation,[],[f38])).
% 1.64/0.93  
% 1.64/0.93  fof(f1,axiom,(
% 1.64/0.93    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.64/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f10,plain,(
% 1.64/0.93    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.64/0.93    inference(unused_predicate_definition_removal,[],[f1])).
% 1.64/0.93  
% 1.64/0.93  fof(f15,plain,(
% 1.64/0.93    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.64/0.93    inference(ennf_transformation,[],[f10])).
% 1.64/0.93  
% 1.64/0.93  fof(f29,plain,(
% 1.64/0.93    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.64/0.93    introduced(choice_axiom,[])).
% 1.64/0.93  
% 1.64/0.93  fof(f30,plain,(
% 1.64/0.93    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.64/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f29])).
% 1.64/0.93  
% 1.64/0.93  fof(f39,plain,(
% 1.64/0.93    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f30])).
% 1.64/0.93  
% 1.64/0.93  fof(f55,plain,(
% 1.64/0.93    ~r1_tarski(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3))),
% 1.64/0.93    inference(cnf_transformation,[],[f38])).
% 1.64/0.93  
% 1.64/0.93  fof(f6,axiom,(
% 1.64/0.93    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,u1_struct_0(X2)) & l1_waybel_0(X2,X1) & ~v2_struct_0(X2) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))))),
% 1.64/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f23,plain,(
% 1.64/0.93    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))) | (~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)))),
% 1.64/0.93    inference(ennf_transformation,[],[f6])).
% 1.64/0.93  
% 1.64/0.93  fof(f24,plain,(
% 1.64/0.93    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 1.64/0.93    inference(flattening,[],[f23])).
% 1.64/0.93  
% 1.64/0.93  fof(f31,plain,(
% 1.64/0.93    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ! [X4] : (~r1_orders_2(X2,X3,X4) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & (? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2))) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 1.64/0.93    inference(nnf_transformation,[],[f24])).
% 1.64/0.93  
% 1.64/0.93  fof(f32,plain,(
% 1.64/0.93    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ! [X4] : (~r1_orders_2(X2,X3,X4) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & (? [X5] : (r1_orders_2(X2,X3,X5) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X2))) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 1.64/0.93    inference(rectify,[],[f31])).
% 1.64/0.93  
% 1.64/0.93  fof(f33,plain,(
% 1.64/0.93    ! [X3,X2,X0] : (? [X5] : (r1_orders_2(X2,X3,X5) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X2))) => (r1_orders_2(X2,X3,sK1(X0,X2,X3)) & sK1(X0,X2,X3) = X0 & m1_subset_1(sK1(X0,X2,X3),u1_struct_0(X2))))),
% 1.64/0.93    introduced(choice_axiom,[])).
% 1.64/0.93  
% 1.64/0.93  fof(f34,plain,(
% 1.64/0.93    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ! [X4] : (~r1_orders_2(X2,X3,X4) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & ((r1_orders_2(X2,X3,sK1(X0,X2,X3)) & sK1(X0,X2,X3) = X0 & m1_subset_1(sK1(X0,X2,X3),u1_struct_0(X2))) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 1.64/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 1.64/0.93  
% 1.64/0.93  fof(f45,plain,(
% 1.64/0.93    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK1(X0,X2,X3),u1_struct_0(X2)) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f34])).
% 1.64/0.93  
% 1.64/0.93  fof(f2,axiom,(
% 1.64/0.93    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.64/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f16,plain,(
% 1.64/0.93    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.64/0.93    inference(ennf_transformation,[],[f2])).
% 1.64/0.93  
% 1.64/0.93  fof(f17,plain,(
% 1.64/0.93    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.64/0.93    inference(flattening,[],[f16])).
% 1.64/0.93  
% 1.64/0.93  fof(f41,plain,(
% 1.64/0.93    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f17])).
% 1.64/0.93  
% 1.64/0.93  fof(f4,axiom,(
% 1.64/0.93    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 1.64/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f11,plain,(
% 1.64/0.93    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 1.64/0.93    inference(pure_predicate_removal,[],[f4])).
% 1.64/0.93  
% 1.64/0.93  fof(f14,plain,(
% 1.64/0.93    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))))),
% 1.64/0.93    inference(pure_predicate_removal,[],[f11])).
% 1.64/0.93  
% 1.64/0.93  fof(f19,plain,(
% 1.64/0.93    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 1.64/0.93    inference(ennf_transformation,[],[f14])).
% 1.64/0.93  
% 1.64/0.93  fof(f20,plain,(
% 1.64/0.93    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 1.64/0.93    inference(flattening,[],[f19])).
% 1.64/0.93  
% 1.64/0.93  fof(f43,plain,(
% 1.64/0.93    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f20])).
% 1.64/0.93  
% 1.64/0.93  fof(f3,axiom,(
% 1.64/0.93    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.64/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f18,plain,(
% 1.64/0.93    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.64/0.93    inference(ennf_transformation,[],[f3])).
% 1.64/0.93  
% 1.64/0.93  fof(f42,plain,(
% 1.64/0.93    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f18])).
% 1.64/0.93  
% 1.64/0.93  fof(f5,axiom,(
% 1.64/0.93    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & ~v1_xboole_0(u1_waybel_0(X0,X1)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 1.64/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.64/0.93  
% 1.64/0.93  fof(f12,plain,(
% 1.64/0.93    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (~v1_xboole_0(u1_waybel_0(X0,X1)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 1.64/0.93    inference(pure_predicate_removal,[],[f5])).
% 1.64/0.93  
% 1.64/0.93  fof(f13,plain,(
% 1.64/0.93    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_waybel_0(X0,X1)))),
% 1.64/0.93    inference(pure_predicate_removal,[],[f12])).
% 1.64/0.93  
% 1.64/0.93  fof(f21,plain,(
% 1.64/0.93    ! [X0,X1] : (~v1_xboole_0(u1_waybel_0(X0,X1)) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.64/0.93    inference(ennf_transformation,[],[f13])).
% 1.64/0.93  
% 1.64/0.93  fof(f22,plain,(
% 1.64/0.93    ! [X0,X1] : (~v1_xboole_0(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.64/0.93    inference(flattening,[],[f21])).
% 1.64/0.93  
% 1.64/0.93  fof(f44,plain,(
% 1.64/0.93    ( ! [X0,X1] : (~v1_xboole_0(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f22])).
% 1.64/0.93  
% 1.64/0.93  fof(f46,plain,(
% 1.64/0.93    ( ! [X2,X0,X3,X1] : (sK1(X0,X2,X3) = X0 | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f34])).
% 1.64/0.93  
% 1.64/0.93  fof(f40,plain,(
% 1.64/0.93    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 1.64/0.93    inference(cnf_transformation,[],[f30])).
% 1.64/0.93  
% 1.64/0.93  cnf(c_13,negated_conjecture,
% 1.64/0.93      ( l1_waybel_0(sK3,sK2) ),
% 1.64/0.93      inference(cnf_transformation,[],[f53]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_370,negated_conjecture,
% 1.64/0.93      ( l1_waybel_0(sK3,sK2) ),
% 1.64/0.93      inference(subtyping,[status(esa)],[c_13]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_716,plain,
% 1.64/0.93      ( l1_waybel_0(sK3,sK2) = iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_370]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_12,negated_conjecture,
% 1.64/0.93      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.64/0.93      inference(cnf_transformation,[],[f54]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_371,negated_conjecture,
% 1.64/0.93      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.64/0.93      inference(subtyping,[status(esa)],[c_12]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_715,plain,
% 1.64/0.93      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_10,plain,
% 1.64/0.93      ( ~ l1_waybel_0(X0,X1)
% 1.64/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.64/0.93      | v2_struct_0(X1)
% 1.64/0.93      | v2_struct_0(X0)
% 1.64/0.93      | ~ l1_struct_0(X1)
% 1.64/0.93      | u1_struct_0(k4_waybel_9(X1,X0,X2)) = a_3_0_waybel_9(X1,X0,X2) ),
% 1.64/0.93      inference(cnf_transformation,[],[f49]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_372,plain,
% 1.64/0.93      ( ~ l1_waybel_0(X0_47,X1_47)
% 1.64/0.93      | ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
% 1.64/0.93      | v2_struct_0(X0_47)
% 1.64/0.93      | v2_struct_0(X1_47)
% 1.64/0.93      | ~ l1_struct_0(X1_47)
% 1.64/0.93      | u1_struct_0(k4_waybel_9(X1_47,X0_47,X0_48)) = a_3_0_waybel_9(X1_47,X0_47,X0_48) ),
% 1.64/0.93      inference(subtyping,[status(esa)],[c_10]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_714,plain,
% 1.64/0.93      ( u1_struct_0(k4_waybel_9(X0_47,X1_47,X0_48)) = a_3_0_waybel_9(X0_47,X1_47,X0_48)
% 1.64/0.93      | l1_waybel_0(X1_47,X0_47) != iProver_top
% 1.64/0.93      | m1_subset_1(X0_48,u1_struct_0(X1_47)) != iProver_top
% 1.64/0.93      | v2_struct_0(X1_47) = iProver_top
% 1.64/0.93      | v2_struct_0(X0_47) = iProver_top
% 1.64/0.93      | l1_struct_0(X0_47) != iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1109,plain,
% 1.64/0.93      ( u1_struct_0(k4_waybel_9(X0_47,sK3,sK4)) = a_3_0_waybel_9(X0_47,sK3,sK4)
% 1.64/0.93      | l1_waybel_0(sK3,X0_47) != iProver_top
% 1.64/0.93      | v2_struct_0(X0_47) = iProver_top
% 1.64/0.93      | v2_struct_0(sK3) = iProver_top
% 1.64/0.93      | l1_struct_0(X0_47) != iProver_top ),
% 1.64/0.93      inference(superposition,[status(thm)],[c_715,c_714]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_14,negated_conjecture,
% 1.64/0.93      ( ~ v2_struct_0(sK3) ),
% 1.64/0.93      inference(cnf_transformation,[],[f52]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_19,plain,
% 1.64/0.93      ( v2_struct_0(sK3) != iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1219,plain,
% 1.64/0.93      ( v2_struct_0(X0_47) = iProver_top
% 1.64/0.93      | l1_waybel_0(sK3,X0_47) != iProver_top
% 1.64/0.93      | u1_struct_0(k4_waybel_9(X0_47,sK3,sK4)) = a_3_0_waybel_9(X0_47,sK3,sK4)
% 1.64/0.93      | l1_struct_0(X0_47) != iProver_top ),
% 1.64/0.93      inference(global_propositional_subsumption,[status(thm)],[c_1109,c_19]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1220,plain,
% 1.64/0.93      ( u1_struct_0(k4_waybel_9(X0_47,sK3,sK4)) = a_3_0_waybel_9(X0_47,sK3,sK4)
% 1.64/0.93      | l1_waybel_0(sK3,X0_47) != iProver_top
% 1.64/0.93      | v2_struct_0(X0_47) = iProver_top
% 1.64/0.93      | l1_struct_0(X0_47) != iProver_top ),
% 1.64/0.93      inference(renaming,[status(thm)],[c_1219]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1227,plain,
% 1.64/0.93      ( u1_struct_0(k4_waybel_9(sK2,sK3,sK4)) = a_3_0_waybel_9(sK2,sK3,sK4)
% 1.64/0.93      | v2_struct_0(sK2) = iProver_top
% 1.64/0.93      | l1_struct_0(sK2) != iProver_top ),
% 1.64/0.93      inference(superposition,[status(thm)],[c_716,c_1220]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_16,negated_conjecture,
% 1.64/0.93      ( ~ v2_struct_0(sK2) ),
% 1.64/0.93      inference(cnf_transformation,[],[f50]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_15,negated_conjecture,
% 1.64/0.93      ( l1_struct_0(sK2) ),
% 1.64/0.93      inference(cnf_transformation,[],[f51]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_893,plain,
% 1.64/0.93      ( ~ l1_waybel_0(X0_47,sK2)
% 1.64/0.93      | ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
% 1.64/0.93      | v2_struct_0(X0_47)
% 1.64/0.93      | v2_struct_0(sK2)
% 1.64/0.93      | ~ l1_struct_0(sK2)
% 1.64/0.93      | u1_struct_0(k4_waybel_9(sK2,X0_47,X0_48)) = a_3_0_waybel_9(sK2,X0_47,X0_48) ),
% 1.64/0.93      inference(instantiation,[status(thm)],[c_372]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_895,plain,
% 1.64/0.93      ( ~ l1_waybel_0(sK3,sK2)
% 1.64/0.93      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.64/0.93      | v2_struct_0(sK3)
% 1.64/0.93      | v2_struct_0(sK2)
% 1.64/0.93      | ~ l1_struct_0(sK2)
% 1.64/0.93      | u1_struct_0(k4_waybel_9(sK2,sK3,sK4)) = a_3_0_waybel_9(sK2,sK3,sK4) ),
% 1.64/0.93      inference(instantiation,[status(thm)],[c_893]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1230,plain,
% 1.64/0.93      ( u1_struct_0(k4_waybel_9(sK2,sK3,sK4)) = a_3_0_waybel_9(sK2,sK3,sK4) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_1227,c_16,c_15,c_14,c_13,c_12,c_895]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1,plain,
% 1.64/0.93      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 1.64/0.93      inference(cnf_transformation,[],[f39]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_11,negated_conjecture,
% 1.64/0.93      ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3)) ),
% 1.64/0.93      inference(cnf_transformation,[],[f55]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_190,plain,
% 1.64/0.93      ( r2_hidden(sK0(X0,X1),X0)
% 1.64/0.93      | u1_struct_0(k4_waybel_9(sK2,sK3,sK4)) != X0
% 1.64/0.93      | u1_struct_0(sK3) != X1 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_1,c_11]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_191,plain,
% 1.64/0.93      ( r2_hidden(sK0(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3)),u1_struct_0(k4_waybel_9(sK2,sK3,sK4))) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_190]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_366,plain,
% 1.64/0.93      ( r2_hidden(sK0(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3)),u1_struct_0(k4_waybel_9(sK2,sK3,sK4))) ),
% 1.64/0.93      inference(subtyping,[status(esa)],[c_191]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_720,plain,
% 1.64/0.93      ( r2_hidden(sK0(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3)),u1_struct_0(k4_waybel_9(sK2,sK3,sK4))) = iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1233,plain,
% 1.64/0.93      ( r2_hidden(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),a_3_0_waybel_9(sK2,sK3,sK4)) = iProver_top ),
% 1.64/0.93      inference(demodulation,[status(thm)],[c_1230,c_720]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_9,plain,
% 1.64/0.93      ( ~ l1_waybel_0(X0,X1)
% 1.64/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.64/0.93      | m1_subset_1(sK1(X3,X0,X2),u1_struct_0(X0))
% 1.64/0.93      | ~ r2_hidden(X3,a_3_0_waybel_9(X1,X0,X2))
% 1.64/0.93      | v2_struct_0(X1)
% 1.64/0.93      | v2_struct_0(X0)
% 1.64/0.93      | ~ l1_struct_0(X1) ),
% 1.64/0.93      inference(cnf_transformation,[],[f45]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_373,plain,
% 1.64/0.93      ( ~ l1_waybel_0(X0_47,X1_47)
% 1.64/0.93      | ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
% 1.64/0.93      | m1_subset_1(sK1(X1_48,X0_47,X0_48),u1_struct_0(X0_47))
% 1.64/0.93      | ~ r2_hidden(X1_48,a_3_0_waybel_9(X1_47,X0_47,X0_48))
% 1.64/0.93      | v2_struct_0(X0_47)
% 1.64/0.93      | v2_struct_0(X1_47)
% 1.64/0.93      | ~ l1_struct_0(X1_47) ),
% 1.64/0.93      inference(subtyping,[status(esa)],[c_9]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_713,plain,
% 1.64/0.93      ( l1_waybel_0(X0_47,X1_47) != iProver_top
% 1.64/0.93      | m1_subset_1(X0_48,u1_struct_0(X0_47)) != iProver_top
% 1.64/0.93      | m1_subset_1(sK1(X1_48,X0_47,X0_48),u1_struct_0(X0_47)) = iProver_top
% 1.64/0.93      | r2_hidden(X1_48,a_3_0_waybel_9(X1_47,X0_47,X0_48)) != iProver_top
% 1.64/0.93      | v2_struct_0(X0_47) = iProver_top
% 1.64/0.93      | v2_struct_0(X1_47) = iProver_top
% 1.64/0.93      | l1_struct_0(X1_47) != iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1557,plain,
% 1.64/0.93      ( l1_waybel_0(sK3,sK2) != iProver_top
% 1.64/0.93      | m1_subset_1(sK1(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),sK3,sK4),u1_struct_0(sK3)) = iProver_top
% 1.64/0.93      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 1.64/0.93      | v2_struct_0(sK3) = iProver_top
% 1.64/0.93      | v2_struct_0(sK2) = iProver_top
% 1.64/0.93      | l1_struct_0(sK2) != iProver_top ),
% 1.64/0.93      inference(superposition,[status(thm)],[c_1233,c_713]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_17,plain,
% 1.64/0.93      ( v2_struct_0(sK2) != iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_18,plain,
% 1.64/0.93      ( l1_struct_0(sK2) = iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_20,plain,
% 1.64/0.93      ( l1_waybel_0(sK3,sK2) = iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_21,plain,
% 1.64/0.93      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1912,plain,
% 1.64/0.93      ( m1_subset_1(sK1(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),sK3,sK4),u1_struct_0(sK3)) = iProver_top ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_1557,c_17,c_18,c_19,c_20,c_21]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_2,plain,
% 1.64/0.93      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.64/0.93      inference(cnf_transformation,[],[f41]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_378,plain,
% 1.64/0.93      ( ~ m1_subset_1(X0_48,X1_48)
% 1.64/0.93      | r2_hidden(X0_48,X1_48)
% 1.64/0.93      | v1_xboole_0(X1_48) ),
% 1.64/0.93      inference(subtyping,[status(esa)],[c_2]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_708,plain,
% 1.64/0.93      ( m1_subset_1(X0_48,X1_48) != iProver_top
% 1.64/0.93      | r2_hidden(X0_48,X1_48) = iProver_top
% 1.64/0.93      | v1_xboole_0(X1_48) = iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1917,plain,
% 1.64/0.93      ( r2_hidden(sK1(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),sK3,sK4),u1_struct_0(sK3)) = iProver_top
% 1.64/0.93      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.64/0.93      inference(superposition,[status(thm)],[c_1912,c_708]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_4,plain,
% 1.64/0.93      ( ~ l1_waybel_0(X0,X1)
% 1.64/0.93      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.64/0.93      | ~ l1_struct_0(X1) ),
% 1.64/0.93      inference(cnf_transformation,[],[f43]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_376,plain,
% 1.64/0.93      ( ~ l1_waybel_0(X0_47,X1_47)
% 1.64/0.93      | m1_subset_1(u1_waybel_0(X1_47,X0_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47))))
% 1.64/0.93      | ~ l1_struct_0(X1_47) ),
% 1.64/0.93      inference(subtyping,[status(esa)],[c_4]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_710,plain,
% 1.64/0.93      ( l1_waybel_0(X0_47,X1_47) != iProver_top
% 1.64/0.93      | m1_subset_1(u1_waybel_0(X1_47,X0_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_47),u1_struct_0(X1_47)))) = iProver_top
% 1.64/0.93      | l1_struct_0(X1_47) != iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_376]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_3,plain,
% 1.64/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.64/0.93      | ~ v1_xboole_0(X1)
% 1.64/0.93      | v1_xboole_0(X0) ),
% 1.64/0.93      inference(cnf_transformation,[],[f42]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_377,plain,
% 1.64/0.93      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 1.64/0.93      | ~ v1_xboole_0(X1_48)
% 1.64/0.93      | v1_xboole_0(X0_48) ),
% 1.64/0.93      inference(subtyping,[status(esa)],[c_3]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_709,plain,
% 1.64/0.93      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 1.64/0.93      | v1_xboole_0(X1_48) != iProver_top
% 1.64/0.93      | v1_xboole_0(X0_48) = iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1012,plain,
% 1.64/0.93      ( l1_waybel_0(X0_47,X1_47) != iProver_top
% 1.64/0.93      | l1_struct_0(X1_47) != iProver_top
% 1.64/0.93      | v1_xboole_0(u1_waybel_0(X1_47,X0_47)) = iProver_top
% 1.64/0.93      | v1_xboole_0(u1_struct_0(X0_47)) != iProver_top ),
% 1.64/0.93      inference(superposition,[status(thm)],[c_710,c_709]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_5,plain,
% 1.64/0.93      ( ~ l1_waybel_0(X0,X1)
% 1.64/0.93      | v2_struct_0(X1)
% 1.64/0.93      | v2_struct_0(X0)
% 1.64/0.93      | ~ l1_struct_0(X1)
% 1.64/0.93      | ~ v1_xboole_0(u1_waybel_0(X1,X0)) ),
% 1.64/0.93      inference(cnf_transformation,[],[f44]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_375,plain,
% 1.64/0.93      ( ~ l1_waybel_0(X0_47,X1_47)
% 1.64/0.93      | v2_struct_0(X0_47)
% 1.64/0.93      | v2_struct_0(X1_47)
% 1.64/0.93      | ~ l1_struct_0(X1_47)
% 1.64/0.93      | ~ v1_xboole_0(u1_waybel_0(X1_47,X0_47)) ),
% 1.64/0.93      inference(subtyping,[status(esa)],[c_5]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_711,plain,
% 1.64/0.93      ( l1_waybel_0(X0_47,X1_47) != iProver_top
% 1.64/0.93      | v2_struct_0(X0_47) = iProver_top
% 1.64/0.93      | v2_struct_0(X1_47) = iProver_top
% 1.64/0.93      | l1_struct_0(X1_47) != iProver_top
% 1.64/0.93      | v1_xboole_0(u1_waybel_0(X1_47,X0_47)) != iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1655,plain,
% 1.64/0.93      ( l1_waybel_0(X0_47,X1_47) != iProver_top
% 1.64/0.93      | v2_struct_0(X0_47) = iProver_top
% 1.64/0.93      | v2_struct_0(X1_47) = iProver_top
% 1.64/0.93      | l1_struct_0(X1_47) != iProver_top
% 1.64/0.93      | v1_xboole_0(u1_struct_0(X0_47)) != iProver_top ),
% 1.64/0.93      inference(superposition,[status(thm)],[c_1012,c_711]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1665,plain,
% 1.64/0.93      ( v2_struct_0(sK3) = iProver_top
% 1.64/0.93      | v2_struct_0(sK2) = iProver_top
% 1.64/0.93      | l1_struct_0(sK2) != iProver_top
% 1.64/0.93      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 1.64/0.93      inference(superposition,[status(thm)],[c_716,c_1655]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_2121,plain,
% 1.64/0.93      ( r2_hidden(sK1(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),sK3,sK4),u1_struct_0(sK3)) = iProver_top ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_1917,c_17,c_18,c_19,c_1665]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_8,plain,
% 1.64/0.93      ( ~ l1_waybel_0(X0,X1)
% 1.64/0.93      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.64/0.93      | ~ r2_hidden(X3,a_3_0_waybel_9(X1,X0,X2))
% 1.64/0.93      | v2_struct_0(X1)
% 1.64/0.93      | v2_struct_0(X0)
% 1.64/0.93      | ~ l1_struct_0(X1)
% 1.64/0.93      | sK1(X3,X0,X2) = X3 ),
% 1.64/0.93      inference(cnf_transformation,[],[f46]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_374,plain,
% 1.64/0.93      ( ~ l1_waybel_0(X0_47,X1_47)
% 1.64/0.93      | ~ m1_subset_1(X0_48,u1_struct_0(X0_47))
% 1.64/0.93      | ~ r2_hidden(X1_48,a_3_0_waybel_9(X1_47,X0_47,X0_48))
% 1.64/0.93      | v2_struct_0(X0_47)
% 1.64/0.93      | v2_struct_0(X1_47)
% 1.64/0.93      | ~ l1_struct_0(X1_47)
% 1.64/0.93      | sK1(X1_48,X0_47,X0_48) = X1_48 ),
% 1.64/0.93      inference(subtyping,[status(esa)],[c_8]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_712,plain,
% 1.64/0.93      ( sK1(X0_48,X0_47,X1_48) = X0_48
% 1.64/0.93      | l1_waybel_0(X0_47,X1_47) != iProver_top
% 1.64/0.93      | m1_subset_1(X1_48,u1_struct_0(X0_47)) != iProver_top
% 1.64/0.93      | r2_hidden(X0_48,a_3_0_waybel_9(X1_47,X0_47,X1_48)) != iProver_top
% 1.64/0.93      | v2_struct_0(X0_47) = iProver_top
% 1.64/0.93      | v2_struct_0(X1_47) = iProver_top
% 1.64/0.93      | l1_struct_0(X1_47) != iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1355,plain,
% 1.64/0.93      ( sK1(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),sK3,sK4) = sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3))
% 1.64/0.93      | l1_waybel_0(sK3,sK2) != iProver_top
% 1.64/0.93      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 1.64/0.93      | v2_struct_0(sK3) = iProver_top
% 1.64/0.93      | v2_struct_0(sK2) = iProver_top
% 1.64/0.93      | l1_struct_0(sK2) != iProver_top ),
% 1.64/0.93      inference(superposition,[status(thm)],[c_1233,c_712]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_2022,plain,
% 1.64/0.93      ( sK1(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),sK3,sK4) = sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)) ),
% 1.64/0.93      inference(global_propositional_subsumption,
% 1.64/0.93                [status(thm)],
% 1.64/0.93                [c_1355,c_17,c_18,c_19,c_20,c_21]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_2125,plain,
% 1.64/0.93      ( r2_hidden(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top ),
% 1.64/0.93      inference(light_normalisation,[status(thm)],[c_2121,c_2022]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_0,plain,
% 1.64/0.93      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 1.64/0.93      inference(cnf_transformation,[],[f40]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_197,plain,
% 1.64/0.93      ( ~ r2_hidden(sK0(X0,X1),X1)
% 1.64/0.93      | u1_struct_0(k4_waybel_9(sK2,sK3,sK4)) != X0
% 1.64/0.93      | u1_struct_0(sK3) != X1 ),
% 1.64/0.93      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_198,plain,
% 1.64/0.93      ( ~ r2_hidden(sK0(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3)),u1_struct_0(sK3)) ),
% 1.64/0.93      inference(unflattening,[status(thm)],[c_197]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_365,plain,
% 1.64/0.93      ( ~ r2_hidden(sK0(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3)),u1_struct_0(sK3)) ),
% 1.64/0.93      inference(subtyping,[status(esa)],[c_198]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_721,plain,
% 1.64/0.93      ( r2_hidden(sK0(u1_struct_0(k4_waybel_9(sK2,sK3,sK4)),u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top ),
% 1.64/0.93      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_1234,plain,
% 1.64/0.93      ( r2_hidden(sK0(a_3_0_waybel_9(sK2,sK3,sK4),u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top ),
% 1.64/0.93      inference(demodulation,[status(thm)],[c_1230,c_721]) ).
% 1.64/0.93  
% 1.64/0.93  cnf(c_2127,plain,
% 1.64/0.93      ( $false ),
% 1.64/0.93      inference(forward_subsumption_resolution,[status(thm)],[c_2125,c_1234]) ).
% 1.64/0.93  
% 1.64/0.93  
% 1.64/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 1.64/0.93  
% 1.64/0.93  ------                               Statistics
% 1.64/0.93  
% 1.64/0.93  ------ General
% 1.64/0.93  
% 1.64/0.93  abstr_ref_over_cycles:                  0
% 1.64/0.93  abstr_ref_under_cycles:                 0
% 1.64/0.93  gc_basic_clause_elim:                   0
% 1.64/0.93  forced_gc_time:                         0
% 1.64/0.93  parsing_time:                           0.008
% 1.64/0.93  unif_index_cands_time:                  0.
% 1.64/0.93  unif_index_add_time:                    0.
% 1.64/0.93  orderings_time:                         0.
% 1.64/0.93  out_proof_time:                         0.009
% 1.64/0.93  total_time:                             0.104
% 1.64/0.93  num_of_symbols:                         53
% 1.64/0.93  num_of_terms:                           1756
% 1.64/0.93  
% 1.64/0.93  ------ Preprocessing
% 1.64/0.93  
% 1.64/0.93  num_of_splits:                          0
% 1.64/0.93  num_of_split_atoms:                     0
% 1.64/0.93  num_of_reused_defs:                     0
% 1.64/0.93  num_eq_ax_congr_red:                    28
% 1.64/0.93  num_of_sem_filtered_clauses:            1
% 1.64/0.93  num_of_subtypes:                        3
% 1.64/0.93  monotx_restored_types:                  1
% 1.64/0.93  sat_num_of_epr_types:                   0
% 1.64/0.93  sat_num_of_non_cyclic_types:            0
% 1.64/0.93  sat_guarded_non_collapsed_types:        0
% 1.64/0.93  num_pure_diseq_elim:                    0
% 1.64/0.93  simp_replaced_by:                       0
% 1.64/0.93  res_preprocessed:                       93
% 1.64/0.93  prep_upred:                             0
% 1.64/0.93  prep_unflattend:                        7
% 1.64/0.93  smt_new_axioms:                         0
% 1.64/0.93  pred_elim_cands:                        6
% 1.64/0.93  pred_elim:                              2
% 1.64/0.93  pred_elim_cl:                           2
% 1.64/0.93  pred_elim_cycles:                       4
% 1.64/0.93  merged_defs:                            0
% 1.64/0.93  merged_defs_ncl:                        0
% 1.64/0.93  bin_hyper_res:                          0
% 1.64/0.93  prep_cycles:                            4
% 1.64/0.93  pred_elim_time:                         0.002
% 1.64/0.93  splitting_time:                         0.
% 1.64/0.93  sem_filter_time:                        0.
% 1.64/0.93  monotx_time:                            0.001
% 1.64/0.93  subtype_inf_time:                       0.001
% 1.64/0.93  
% 1.64/0.93  ------ Problem properties
% 1.64/0.93  
% 1.64/0.93  clauses:                                15
% 1.64/0.93  conjectures:                            5
% 1.64/0.93  epr:                                    5
% 1.64/0.93  horn:                                   9
% 1.64/0.93  ground:                                 7
% 1.64/0.93  unary:                                  7
% 1.64/0.93  binary:                                 0
% 1.64/0.93  lits:                                   51
% 1.64/0.93  lits_eq:                                2
% 1.64/0.93  fd_pure:                                0
% 1.64/0.93  fd_pseudo:                              0
% 1.64/0.93  fd_cond:                                0
% 1.64/0.93  fd_pseudo_cond:                         0
% 1.64/0.93  ac_symbols:                             0
% 1.64/0.93  
% 1.64/0.93  ------ Propositional Solver
% 1.64/0.93  
% 1.64/0.93  prop_solver_calls:                      27
% 1.64/0.93  prop_fast_solver_calls:                 741
% 1.64/0.93  smt_solver_calls:                       0
% 1.64/0.93  smt_fast_solver_calls:                  0
% 1.64/0.93  prop_num_of_clauses:                    573
% 1.64/0.93  prop_preprocess_simplified:             2762
% 1.64/0.93  prop_fo_subsumed:                       17
% 1.64/0.93  prop_solver_time:                       0.
% 1.64/0.93  smt_solver_time:                        0.
% 1.64/0.93  smt_fast_solver_time:                   0.
% 1.64/0.93  prop_fast_solver_time:                  0.
% 1.64/0.93  prop_unsat_core_time:                   0.
% 1.64/0.93  
% 1.64/0.93  ------ QBF
% 1.64/0.93  
% 1.64/0.93  qbf_q_res:                              0
% 1.64/0.93  qbf_num_tautologies:                    0
% 1.64/0.93  qbf_prep_cycles:                        0
% 1.64/0.93  
% 1.64/0.93  ------ BMC1
% 1.64/0.93  
% 1.64/0.93  bmc1_current_bound:                     -1
% 1.64/0.93  bmc1_last_solved_bound:                 -1
% 1.64/0.93  bmc1_unsat_core_size:                   -1
% 1.64/0.93  bmc1_unsat_core_parents_size:           -1
% 1.64/0.93  bmc1_merge_next_fun:                    0
% 1.64/0.93  bmc1_unsat_core_clauses_time:           0.
% 1.64/0.93  
% 1.64/0.93  ------ Instantiation
% 1.64/0.93  
% 1.64/0.93  inst_num_of_clauses:                    210
% 1.64/0.93  inst_num_in_passive:                    3
% 1.64/0.93  inst_num_in_active:                     164
% 1.64/0.93  inst_num_in_unprocessed:                43
% 1.64/0.93  inst_num_of_loops:                      170
% 1.64/0.93  inst_num_of_learning_restarts:          0
% 1.64/0.93  inst_num_moves_active_passive:          1
% 1.64/0.93  inst_lit_activity:                      0
% 1.64/0.93  inst_lit_activity_moves:                0
% 1.64/0.93  inst_num_tautologies:                   0
% 1.64/0.93  inst_num_prop_implied:                  0
% 1.64/0.93  inst_num_existing_simplified:           0
% 1.64/0.93  inst_num_eq_res_simplified:             0
% 1.64/0.93  inst_num_child_elim:                    0
% 1.64/0.93  inst_num_of_dismatching_blockings:      63
% 1.64/0.93  inst_num_of_non_proper_insts:           249
% 1.64/0.93  inst_num_of_duplicates:                 0
% 1.64/0.93  inst_inst_num_from_inst_to_res:         0
% 1.64/0.93  inst_dismatching_checking_time:         0.
% 1.64/0.93  
% 1.64/0.93  ------ Resolution
% 1.64/0.93  
% 1.64/0.93  res_num_of_clauses:                     0
% 1.64/0.93  res_num_in_passive:                     0
% 1.64/0.93  res_num_in_active:                      0
% 1.64/0.93  res_num_of_loops:                       97
% 1.64/0.93  res_forward_subset_subsumed:            50
% 1.64/0.93  res_backward_subset_subsumed:           2
% 1.64/0.93  res_forward_subsumed:                   0
% 1.64/0.93  res_backward_subsumed:                  0
% 1.64/0.93  res_forward_subsumption_resolution:     1
% 1.64/0.93  res_backward_subsumption_resolution:    0
% 1.64/0.93  res_clause_to_clause_subsumption:       41
% 1.64/0.93  res_orphan_elimination:                 0
% 1.64/0.93  res_tautology_del:                      38
% 1.64/0.93  res_num_eq_res_simplified:              0
% 1.64/0.93  res_num_sel_changes:                    0
% 1.64/0.93  res_moves_from_active_to_pass:          0
% 1.64/0.93  
% 1.64/0.93  ------ Superposition
% 1.64/0.93  
% 1.64/0.93  sup_time_total:                         0.
% 1.64/0.93  sup_time_generating:                    0.
% 1.64/0.93  sup_time_sim_full:                      0.
% 1.64/0.93  sup_time_sim_immed:                     0.
% 1.64/0.93  
% 1.64/0.93  sup_num_of_clauses:                     37
% 1.64/0.93  sup_num_in_active:                      30
% 1.64/0.93  sup_num_in_passive:                     7
% 1.64/0.93  sup_num_of_loops:                       33
% 1.64/0.93  sup_fw_superposition:                   10
% 1.64/0.93  sup_bw_superposition:                   16
% 1.64/0.93  sup_immediate_simplified:               3
% 1.64/0.93  sup_given_eliminated:                   0
% 1.64/0.93  comparisons_done:                       0
% 1.64/0.93  comparisons_avoided:                    0
% 1.64/0.93  
% 1.64/0.93  ------ Simplifications
% 1.64/0.93  
% 1.64/0.93  
% 1.64/0.93  sim_fw_subset_subsumed:                 0
% 1.64/0.93  sim_bw_subset_subsumed:                 0
% 1.64/0.93  sim_fw_subsumed:                        2
% 1.64/0.93  sim_bw_subsumed:                        0
% 1.64/0.93  sim_fw_subsumption_res:                 1
% 1.64/0.93  sim_bw_subsumption_res:                 0
% 1.64/0.93  sim_tautology_del:                      0
% 1.64/0.93  sim_eq_tautology_del:                   0
% 1.64/0.93  sim_eq_res_simp:                        0
% 1.64/0.93  sim_fw_demodulated:                     0
% 1.64/0.93  sim_bw_demodulated:                     3
% 1.64/0.93  sim_light_normalised:                   4
% 1.64/0.93  sim_joinable_taut:                      0
% 1.64/0.93  sim_joinable_simp:                      0
% 1.64/0.93  sim_ac_normalised:                      0
% 1.64/0.93  sim_smt_subsumption:                    0
% 1.64/0.93  
%------------------------------------------------------------------------------
