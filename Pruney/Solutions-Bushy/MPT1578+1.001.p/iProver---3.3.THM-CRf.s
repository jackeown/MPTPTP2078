%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1578+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:56 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  163 (1079 expanded)
%              Number of clauses        :  113 ( 486 expanded)
%              Number of leaves         :   15 ( 206 expanded)
%              Depth                    :   26
%              Number of atoms          :  412 (2908 expanded)
%              Number of equality atoms :  193 ( 819 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( m1_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0)
            & v4_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( m1_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0)
              & v4_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0)
            | ~ v4_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0)
            | ~ v4_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(X0),sK1)),X0)
          | ~ v4_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(X0),sK1)),X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0)
              | ~ v4_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(sK0),X1)),sK0)
            | ~ v4_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(sK0),X1)),sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
      | ~ v4_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f32,f31])).

fof(f52,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
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

fof(f15,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_yellow_0(X1,X0)
      | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_yellow_0(X1,X0)
              | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
            & ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
              | ~ v4_yellow_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v4_yellow_0(X1,X0)
      | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,
    ( ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
    | ~ v4_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => k1_toler_1(X0,X1) = k2_wellord1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_toler_1(X0,X1) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_toler_1(X0,X1) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_10,plain,
    ( m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2012,plain,
    ( m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2003,plain,
    ( l1_orders_2(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2011,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | l1_orders_2(g1_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2014,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | l1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3189,plain,
    ( l1_orders_2(X0) != iProver_top
    | l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2011,c_2014])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2017,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | l1_orders_2(X0) != iProver_top
    | v1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3709,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
    | l1_orders_2(X0) != iProver_top
    | v1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3189,c_2017])).

cnf(c_2247,plain,
    ( ~ l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
    | ~ v1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
    | g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2248,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
    | l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) != iProver_top
    | v1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2247])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | v1_orders_2(g1_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2013,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_orders_2(g1_orders_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3190,plain,
    ( l1_orders_2(X0) != iProver_top
    | v1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2011,c_2013])).

cnf(c_5108,plain,
    ( l1_orders_2(X0) != iProver_top
    | g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3709,c_2248,c_3189,c_3190])).

cnf(c_5109,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5108])).

cnf(c_5116,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) ),
    inference(superposition,[status(thm)],[c_2003,c_5109])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2009,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5365,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5116,c_2009])).

cnf(c_5415,plain,
    ( u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = u1_struct_0(sK0)
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5365])).

cnf(c_41,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2144,plain,
    ( ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2146,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(instantiation,[status(thm)],[c_2144])).

cnf(c_2149,plain,
    ( ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | v1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2151,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | v1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(instantiation,[status(thm)],[c_2149])).

cnf(c_2249,plain,
    ( ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ v1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) ),
    inference(instantiation,[status(thm)],[c_2247])).

cnf(c_2622,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | X1 = u1_struct_0(sK0)
    | g1_orders_2(X1,X2) != g1_orders_2(u1_struct_0(sK0),X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2853,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | X0 = u1_struct_0(sK0)
    | g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) ),
    inference(instantiation,[status(thm)],[c_2622])).

cnf(c_3919,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2853])).

cnf(c_6060,plain,
    ( u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5415,c_20,c_41,c_2146,c_2151,c_2249,c_3919])).

cnf(c_6094,plain,
    ( m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top
    | l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6060,c_2011])).

cnf(c_21,plain,
    ( l1_orders_2(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_40,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_42,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_2145,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) != iProver_top
    | l1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2144])).

cnf(c_2147,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top
    | l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2145])).

cnf(c_6444,plain,
    ( m1_subset_1(u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6094,c_21,c_42,c_2147])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2010,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5367,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5116,c_2010])).

cnf(c_5846,plain,
    ( u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = u1_orders_2(sK0)
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5367])).

cnf(c_2486,plain,
    ( ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = u1_orders_2(X0)
    | g1_orders_2(X3,X2) != g1_orders_2(X1,u1_orders_2(X0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3115,plain,
    ( ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | X1 = u1_orders_2(X0)
    | g1_orders_2(X2,X1) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(instantiation,[status(thm)],[c_2486])).

cnf(c_4680,plain,
    ( ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))),u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
    | u1_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) = u1_orders_2(X0) ),
    inference(instantiation,[status(thm)],[c_3115])).

cnf(c_4682,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = u1_orders_2(sK0) ),
    inference(instantiation,[status(thm)],[c_4680])).

cnf(c_6230,plain,
    ( u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) = u1_orders_2(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5846,c_20,c_41,c_2146,c_2151,c_2249,c_4682])).

cnf(c_6448,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6444,c_6230])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2016,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6451,plain,
    ( v1_relat_1(u1_orders_2(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6448,c_2016])).

cnf(c_3082,plain,
    ( v1_relat_1(X0) != iProver_top
    | l1_orders_2(g1_orders_2(X1,k1_toler_1(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2012,c_2014])).

cnf(c_3612,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_toler_1(X1,X0))),u1_orders_2(g1_orders_2(X0,k1_toler_1(X1,X0)))) = g1_orders_2(X0,k1_toler_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_orders_2(g1_orders_2(X0,k1_toler_1(X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3082,c_2017])).

cnf(c_2566,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_orders_2(g1_orders_2(X1,k1_toler_1(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2012,c_2013])).

cnf(c_5083,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_toler_1(X1,X0))),u1_orders_2(g1_orders_2(X0,k1_toler_1(X1,X0)))) = g1_orders_2(X0,k1_toler_1(X1,X0))
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3612,c_2566])).

cnf(c_6555,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))),u1_orders_2(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0)))) = g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0)) ),
    inference(superposition,[status(thm)],[c_6451,c_5083])).

cnf(c_7313,plain,
    ( g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0)) != g1_orders_2(X1,X2)
    | u1_orders_2(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) = X2
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6555,c_2010])).

cnf(c_7585,plain,
    ( u1_orders_2(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) = k1_toler_1(u1_orders_2(sK0),X0)
    | m1_subset_1(k1_toler_1(u1_orders_2(sK0),X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_7313])).

cnf(c_9238,plain,
    ( u1_orders_2(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) = k1_toler_1(u1_orders_2(sK0),X0)
    | v1_relat_1(u1_orders_2(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2012,c_7585])).

cnf(c_2122,plain,
    ( ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | v1_relat_1(u1_orders_2(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2123,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) != iProver_top
    | v1_relat_1(u1_orders_2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2122])).

cnf(c_2125,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top
    | v1_relat_1(u1_orders_2(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2123])).

cnf(c_9864,plain,
    ( u1_orders_2(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) = k1_toler_1(u1_orders_2(sK0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9238,c_21,c_42,c_2125])).

cnf(c_7309,plain,
    ( g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0)) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) = X1
    | m1_subset_1(u1_orders_2(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))),u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6555,c_2009])).

cnf(c_7909,plain,
    ( u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) = X0
    | m1_subset_1(u1_orders_2(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))),u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0)))))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_7309])).

cnf(c_7308,plain,
    ( g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0)) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) = X1
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6555,c_2009])).

cnf(c_7562,plain,
    ( u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) = X0
    | m1_subset_1(k1_toler_1(u1_orders_2(sK0),X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_7308])).

cnf(c_9061,plain,
    ( u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) = X0
    | v1_relat_1(u1_orders_2(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2012,c_7562])).

cnf(c_9255,plain,
    ( u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7909,c_21,c_42,c_2125,c_9061])).

cnf(c_2,plain,
    ( ~ r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5,plain,
    ( v4_yellow_0(X0,X1)
    | ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)) != u1_orders_2(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,negated_conjecture,
    ( ~ v4_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
    | ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_352,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
    | ~ l1_orders_2(X1)
    | k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)) != u1_orders_2(X0)
    | g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_353,plain,
    ( ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
    | ~ l1_orders_2(sK0)
    | k1_toler_1(u1_orders_2(sK0),u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))) != u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_355,plain,
    ( ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
    | k1_toler_1(u1_orders_2(sK0),u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))) != u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_353,c_20])).

cnf(c_371,plain,
    ( ~ r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X1)
    | k1_toler_1(u1_orders_2(sK0),u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))) != u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_355])).

cnf(c_372,plain,
    ( ~ r1_tarski(u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_orders_2(sK0))
    | ~ r1_tarski(u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_struct_0(sK0))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | ~ l1_orders_2(sK0)
    | k1_toler_1(u1_orders_2(sK0),u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))) != u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_374,plain,
    ( ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | ~ r1_tarski(u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_struct_0(sK0))
    | ~ r1_tarski(u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_orders_2(sK0))
    | k1_toler_1(u1_orders_2(sK0),u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))) != u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_372,c_20])).

cnf(c_375,plain,
    ( ~ r1_tarski(u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_orders_2(sK0))
    | ~ r1_tarski(u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_struct_0(sK0))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | k1_toler_1(u1_orders_2(sK0),u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))) != u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))) ),
    inference(renaming,[status(thm)],[c_374])).

cnf(c_2002,plain,
    ( k1_toler_1(u1_orders_2(sK0),u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))) != u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | r1_tarski(u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_orders_2(sK0)) != iProver_top
    | r1_tarski(u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_struct_0(sK0)) != iProver_top
    | l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_9259,plain,
    ( u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))) != k1_toler_1(u1_orders_2(sK0),sK1)
    | r1_tarski(u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_orders_2(sK0)) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top
    | l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9255,c_2002])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2132,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2133,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2132])).

cnf(c_2233,plain,
    ( m1_subset_1(k1_toler_1(u1_orders_2(X0),X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_relat_1(u1_orders_2(X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2436,plain,
    ( m1_subset_1(k1_toler_1(u1_orders_2(X0),sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_relat_1(u1_orders_2(X0)) ),
    inference(instantiation,[status(thm)],[c_2233])).

cnf(c_2438,plain,
    ( m1_subset_1(k1_toler_1(u1_orders_2(X0),sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | v1_relat_1(u1_orders_2(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2436])).

cnf(c_2440,plain,
    ( m1_subset_1(k1_toler_1(u1_orders_2(sK0),sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | v1_relat_1(u1_orders_2(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2438])).

cnf(c_2409,plain,
    ( ~ m1_subset_1(k1_toler_1(u1_orders_2(X0),X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | l1_orders_2(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3015,plain,
    ( ~ m1_subset_1(k1_toler_1(u1_orders_2(sK0),sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))) ),
    inference(instantiation,[status(thm)],[c_2409])).

cnf(c_3016,plain,
    ( m1_subset_1(k1_toler_1(u1_orders_2(sK0),sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3015])).

cnf(c_9614,plain,
    ( u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))) != k1_toler_1(u1_orders_2(sK0),sK1)
    | r1_tarski(u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_orders_2(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9259,c_21,c_22,c_42,c_2125,c_2133,c_2440,c_3016])).

cnf(c_9868,plain,
    ( k1_toler_1(u1_orders_2(sK0),sK1) != k1_toler_1(u1_orders_2(sK0),sK1)
    | r1_tarski(k1_toler_1(u1_orders_2(sK0),sK1),u1_orders_2(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9864,c_9614])).

cnf(c_9878,plain,
    ( r1_tarski(k1_toler_1(u1_orders_2(sK0),sK1),u1_orders_2(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9868])).

cnf(c_3188,plain,
    ( v1_relat_1(u1_orders_2(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2011,c_2016])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2015,plain,
    ( k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3593,plain,
    ( k3_xboole_0(u1_orders_2(X0),k2_zfmisc_1(X1,X1)) = k2_wellord1(u1_orders_2(X0),X1)
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3188,c_2015])).

cnf(c_4249,plain,
    ( k3_xboole_0(u1_orders_2(sK0),k2_zfmisc_1(X0,X0)) = k2_wellord1(u1_orders_2(sK0),X0) ),
    inference(superposition,[status(thm)],[c_2003,c_3593])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(X0,X1) = k1_toler_1(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2008,plain,
    ( k2_wellord1(X0,X1) = k1_toler_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3594,plain,
    ( k2_wellord1(u1_orders_2(X0),X1) = k1_toler_1(u1_orders_2(X0),X1)
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3188,c_2008])).

cnf(c_3934,plain,
    ( k2_wellord1(u1_orders_2(sK0),X0) = k1_toler_1(u1_orders_2(sK0),X0) ),
    inference(superposition,[status(thm)],[c_2003,c_3594])).

cnf(c_4264,plain,
    ( k3_xboole_0(u1_orders_2(sK0),k2_zfmisc_1(X0,X0)) = k1_toler_1(u1_orders_2(sK0),X0) ),
    inference(light_normalisation,[status(thm)],[c_4249,c_3934])).

cnf(c_15,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2007,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4547,plain,
    ( r1_tarski(k1_toler_1(u1_orders_2(sK0),X0),u1_orders_2(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4264,c_2007])).

cnf(c_9919,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9878,c_4547])).


%------------------------------------------------------------------------------
