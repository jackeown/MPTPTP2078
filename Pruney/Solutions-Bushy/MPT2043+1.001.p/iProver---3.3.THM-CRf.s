%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2043+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:04 EST 2020

% Result     : Theorem 0.70s
% Output     : CNFRefutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 161 expanded)
%              Number of clauses        :   43 (  49 expanded)
%              Number of leaves         :   13 (  42 expanded)
%              Depth                    :   24
%              Number of atoms          :  381 ( 832 expanded)
%              Number of equality atoms :   52 (  52 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
              & v13_waybel_0(X1,k3_yellow_1(X0))
              & v2_waybel_0(X1,k3_yellow_1(X0))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ~ ( v1_xboole_0(X2)
                  & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f29,plain,(
    ! [X1] :
      ( ? [X2] :
          ( v1_xboole_0(X2)
          & r2_hidden(X2,X1) )
     => ( v1_xboole_0(sK2)
        & r2_hidden(sK2,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( v1_xboole_0(X2)
            & r2_hidden(X2,sK1) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(sK1,k3_yellow_1(X0))
        & v2_waybel_0(sK1,k3_yellow_1(X0))
        & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(X0)))
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
          & v13_waybel_0(X1,k3_yellow_1(sK0))
          & v2_waybel_0(X1,k3_yellow_1(sK0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( v1_xboole_0(sK2)
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    & v13_waybel_0(sK1,k3_yellow_1(sK0))
    & v2_waybel_0(sK1,k3_yellow_1(sK0))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f29,f28,f27])).

fof(f51,plain,(
    v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f39,plain,(
    ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_subset_1(X1,u1_struct_0(X0))
              | r2_hidden(k3_yellow_0(X0),X1) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k3_yellow_0(X0),X1)
      | ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f37,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v25_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_yellow_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v25_waybel_0(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v25_waybel_0(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v25_waybel_0(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_lattice3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v25_waybel_0(X0)
          & v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_lattice3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v25_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f17,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X0] :
      ( v25_waybel_0(X0)
      | ~ v3_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_lattice3(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] : v3_lattice3(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f42,plain,(
    ! [X0] : v3_lattice3(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] : k3_yellow_0(k3_yellow_1(X0)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k3_yellow_0(k3_yellow_1(X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

cnf(c_21,negated_conjecture,
    ( v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,negated_conjecture,
    ( v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_9,plain,
    ( v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ r2_hidden(k3_yellow_0(X1),X0)
    | v1_xboole_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_273,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ r2_hidden(k3_yellow_0(X1),X0)
    | v1_xboole_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | k3_yellow_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_274,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ r2_hidden(k3_yellow_0(k3_yellow_1(X1)),X0)
    | v1_xboole_0(X0)
    | ~ v4_orders_2(k3_yellow_1(X1))
    | ~ v5_orders_2(k3_yellow_1(X1))
    | ~ v1_yellow_0(k3_yellow_1(X1))
    | ~ l1_orders_2(k3_yellow_1(X1))
    | v2_struct_0(k3_yellow_1(X1)) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_10,plain,
    ( ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_6,plain,
    ( l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3,plain,
    ( v1_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v25_waybel_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v25_waybel_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,plain,
    ( v3_lattice3(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_239,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | v25_waybel_0(X0)
    | k3_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_240,plain,
    ( ~ l1_orders_2(k3_yellow_1(X0))
    | v2_struct_0(k3_yellow_1(X0))
    | ~ v3_orders_2(k3_yellow_1(X0))
    | v25_waybel_0(k3_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_244,plain,
    ( v25_waybel_0(k3_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_240,c_10,c_9,c_6])).

cnf(c_256,plain,
    ( v1_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | k3_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_244])).

cnf(c_257,plain,
    ( v1_yellow_0(k3_yellow_1(X0))
    | ~ l1_orders_2(k3_yellow_1(X0))
    | v2_struct_0(k3_yellow_1(X0))
    | ~ v3_orders_2(k3_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_261,plain,
    ( v1_yellow_0(k3_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_257,c_10,c_9,c_6])).

cnf(c_7,plain,
    ( v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8,plain,
    ( v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_300,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ r2_hidden(k3_yellow_0(k3_yellow_1(X1)),X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_274,c_10,c_6,c_261,c_7,c_8,c_14])).

cnf(c_386,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ r2_hidden(k3_yellow_0(k3_yellow_1(X1)),X0)
    | k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))) != k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_300])).

cnf(c_387,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(X0))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(X0)))
    | ~ r2_hidden(k3_yellow_0(k3_yellow_1(X0)),sK1)
    | k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))) != k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_563,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(X0))
    | ~ r2_hidden(k3_yellow_0(k3_yellow_1(X0)),sK1)
    | k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))) != k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))
    | u1_struct_0(k3_yellow_1(X0)) != u1_struct_0(k3_yellow_1(sK0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_387])).

cnf(c_593,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(X0))
    | k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))) != k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))
    | u1_struct_0(k3_yellow_1(X0)) != u1_struct_0(k3_yellow_1(sK0))
    | k3_yellow_0(k3_yellow_1(X0)) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_563])).

cnf(c_625,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))) != k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))
    | u1_struct_0(k3_yellow_1(X0)) != u1_struct_0(k3_yellow_1(sK0))
    | k3_yellow_0(k3_yellow_1(X0)) != sK2
    | k3_yellow_1(X0) != k3_yellow_1(sK0)
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_593])).

cnf(c_655,plain,
    ( k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))) != k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))
    | u1_struct_0(k3_yellow_1(X0)) != u1_struct_0(k3_yellow_1(sK0))
    | k3_yellow_0(k3_yellow_1(X0)) != sK2
    | k3_yellow_1(X0) != k3_yellow_1(sK0)
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_625])).

cnf(c_677,plain,
    ( k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))) != k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))
    | u1_struct_0(k3_yellow_1(X0)) != u1_struct_0(k3_yellow_1(sK0))
    | k3_yellow_0(k3_yellow_1(X0)) != sK2
    | k3_yellow_1(X0) != k3_yellow_1(sK0) ),
    inference(equality_resolution_simp,[status(thm)],[c_655])).

cnf(c_685,plain,
    ( k3_yellow_0(k3_yellow_1(X0_53)) != sK2
    | k3_yellow_1(X0_53) != k3_yellow_1(sK0)
    | u1_struct_0(k3_yellow_1(X0_53)) != u1_struct_0(k3_yellow_1(sK0))
    | k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0_53))) != k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))) ),
    inference(subtyping,[status(esa)],[c_677])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,negated_conjecture,
    ( v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_419,plain,
    ( sK2 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_420,plain,
    ( k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_688,plain,
    ( k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_420])).

cnf(c_12,plain,
    ( k3_yellow_0(k3_yellow_1(X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_689,plain,
    ( k3_yellow_0(k3_yellow_1(X0_53)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_722,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k3_yellow_1(X0_53) != k3_yellow_1(sK0)
    | u1_struct_0(k3_yellow_1(X0_53)) != u1_struct_0(k3_yellow_1(sK0))
    | k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0_53))) != k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))) ),
    inference(light_normalisation,[status(thm)],[c_685,c_688,c_689])).

cnf(c_723,plain,
    ( k3_yellow_1(X0_53) != k3_yellow_1(sK0)
    | u1_struct_0(k3_yellow_1(X0_53)) != u1_struct_0(k3_yellow_1(sK0))
    | k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0_53))) != k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_722])).

cnf(c_748,plain,
    ( k3_yellow_1(sK0) != k3_yellow_1(sK0)
    | u1_struct_0(k3_yellow_1(sK0)) != u1_struct_0(k3_yellow_1(sK0)) ),
    inference(equality_resolution,[status(thm)],[c_723])).

cnf(c_772,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_748])).


%------------------------------------------------------------------------------
