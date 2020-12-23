%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1989+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:00 EST 2020

% Result     : Theorem 0.99s
% Output     : CNFRefutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 630 expanded)
%              Number of clauses        :   75 ( 141 expanded)
%              Number of leaves         :   16 ( 177 expanded)
%              Depth                    :   21
%              Number of atoms          :  687 (4655 expanded)
%              Number of equality atoms :   64 (  88 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v4_waybel_7(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v5_waybel_6(X1,X0)
             => v4_waybel_7(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v4_waybel_7(sK2,X0)
        & v5_waybel_6(sK2,X0)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v4_waybel_7(X1,X0)
            & v5_waybel_6(X1,X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v4_waybel_7(X1,sK1)
          & v5_waybel_6(X1,sK1)
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v2_lattice3(sK1)
      & v1_lattice3(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ v4_waybel_7(sK2,sK1)
    & v5_waybel_6(sK2,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v2_lattice3(sK1)
    & v1_lattice3(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f34,f33])).

fof(f56,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v12_waybel_0(k5_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ? [X2] :
                  ( k1_yellow_0(X0,X2) = X1
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X2,X0)
                  & v12_waybel_0(X2,X0)
                  & v1_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ? [X3] :
                  ( k1_yellow_0(X0,X3) = X1
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X3,X0)
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_yellow_0(X0,X3) = X1
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_7(X3,X0)
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( k1_yellow_0(X0,sK0(X0,X1)) = X1
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_7(sK0(X0,X1),X0)
        & v12_waybel_0(sK0(X0,X1),X0)
        & v1_waybel_0(sK0(X0,X1),X0)
        & ~ v1_xboole_0(sK0(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ( k1_yellow_0(X0,sK0(X0,X1)) = X1
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(sK0(X0,X1),X0)
                & v12_waybel_0(sK0(X0,X1),X0)
                & v1_waybel_0(sK0(X0,X1),X0)
                & ~ v1_xboole_0(sK0(X0,X1)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v4_waybel_7(X1,X0)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X2,X0] :
      ( v4_waybel_7(k1_yellow_0(X0,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v1_waybel_7(k5_waybel_0(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    v5_waybel_6(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ~ v4_waybel_7(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1407,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_1856,plain,
    ( X0_49 != X1_49
    | X0_49 = k1_yellow_0(sK1,k5_waybel_0(sK1,sK2))
    | k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)) != X1_49 ),
    inference(instantiation,[status(thm)],[c_1407])).

cnf(c_1857,plain,
    ( k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)) != sK2
    | sK2 = k1_yellow_0(sK1,k5_waybel_0(sK1,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1856])).

cnf(c_1409,plain,
    ( ~ v4_waybel_7(X0_49,X0_50)
    | v4_waybel_7(X1_49,X0_50)
    | X1_49 != X0_49 ),
    theory(equality)).

cnf(c_1791,plain,
    ( v4_waybel_7(X0_49,sK1)
    | ~ v4_waybel_7(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),sK1)
    | X0_49 != k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1409])).

cnf(c_1793,plain,
    ( ~ v4_waybel_7(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),sK1)
    | v4_waybel_7(sK2,sK1)
    | sK2 != k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1791])).

cnf(c_8,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_18,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_804,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_805,plain,
    ( m1_subset_1(k1_yellow_0(sK1,X0),u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_804])).

cnf(c_10,plain,
    ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_299,plain,
    ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_10,c_0])).

cnf(c_1,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ v1_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_yellow_0(X1,X0),u1_struct_0(X1))
    | v4_waybel_7(k1_yellow_0(X1,X0),X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_14,plain,
    ( ~ v5_waybel_6(X0,X1)
    | v1_waybel_7(k5_waybel_0(X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_16,negated_conjecture,
    ( v5_waybel_6(sK2,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_266,plain,
    ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_16])).

cnf(c_267,plain,
    ( v1_waybel_7(k5_waybel_0(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1) ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_23,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_19,negated_conjecture,
    ( v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_269,plain,
    ( v1_waybel_7(k5_waybel_0(sK1,sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_267,c_23,c_22,c_21,c_20,c_19,c_18,c_17])).

cnf(c_466,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_yellow_0(X1,X0),u1_struct_0(X1))
    | v4_waybel_7(k1_yellow_0(X1,X0),X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k5_waybel_0(sK1,sK2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_269])).

cnf(c_467,plain,
    ( ~ v1_waybel_0(k5_waybel_0(sK1,sK2),sK1)
    | ~ v12_waybel_0(k5_waybel_0(sK1,sK2),sK1)
    | ~ m1_subset_1(k5_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),u1_struct_0(sK1))
    | v4_waybel_7(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | v1_xboole_0(k5_waybel_0(sK1,sK2))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_469,plain,
    ( ~ v1_waybel_0(k5_waybel_0(sK1,sK2),sK1)
    | ~ v12_waybel_0(k5_waybel_0(sK1,sK2),sK1)
    | ~ m1_subset_1(k5_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),u1_struct_0(sK1))
    | v4_waybel_7(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),sK1)
    | v1_xboole_0(k5_waybel_0(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_467,c_23,c_22,c_21,c_20,c_19,c_18])).

cnf(c_545,plain,
    ( ~ v1_waybel_0(k5_waybel_0(sK1,sK2),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k5_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),u1_struct_0(sK1))
    | v4_waybel_7(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),sK1)
    | ~ v4_orders_2(X1)
    | v1_xboole_0(k5_waybel_0(sK1,sK2))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k5_waybel_0(X1,X0) != k5_waybel_0(sK1,sK2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_299,c_469])).

cnf(c_546,plain,
    ( ~ v1_waybel_0(k5_waybel_0(sK1,sK2),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k5_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),u1_struct_0(sK1))
    | v4_waybel_7(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),sK1)
    | ~ v4_orders_2(sK1)
    | v1_xboole_0(k5_waybel_0(sK1,sK2))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | k5_waybel_0(sK1,X0) != k5_waybel_0(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_550,plain,
    ( v4_waybel_7(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),sK1)
    | ~ m1_subset_1(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(k5_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v1_waybel_0(k5_waybel_0(sK1,sK2),sK1)
    | v1_xboole_0(k5_waybel_0(sK1,sK2))
    | k5_waybel_0(sK1,X0) != k5_waybel_0(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_546,c_22,c_19,c_18])).

cnf(c_551,plain,
    ( ~ v1_waybel_0(k5_waybel_0(sK1,sK2),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k5_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),u1_struct_0(sK1))
    | v4_waybel_7(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),sK1)
    | v1_xboole_0(k5_waybel_0(sK1,sK2))
    | k5_waybel_0(sK1,X0) != k5_waybel_0(sK1,sK2) ),
    inference(renaming,[status(thm)],[c_550])).

cnf(c_815,plain,
    ( ~ v1_waybel_0(k5_waybel_0(sK1,sK2),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k5_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_waybel_7(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),sK1)
    | v1_xboole_0(k5_waybel_0(sK1,sK2))
    | k5_waybel_0(sK1,X0) != k5_waybel_0(sK1,sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_805,c_551])).

cnf(c_1387,plain,
    ( ~ v1_waybel_0(k5_waybel_0(sK1,sK2),sK1)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK1))
    | ~ m1_subset_1(k5_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_waybel_7(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),sK1)
    | v1_xboole_0(k5_waybel_0(sK1,sK2))
    | k5_waybel_0(sK1,X0_49) != k5_waybel_0(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_815])).

cnf(c_1403,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK1))
    | k5_waybel_0(sK1,X0_49) != k5_waybel_0(sK1,sK2)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1387])).

cnf(c_1448,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ sP1_iProver_split
    | k5_waybel_0(sK1,sK2) != k5_waybel_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1403])).

cnf(c_1404,plain,
    ( ~ v1_waybel_0(k5_waybel_0(sK1,sK2),sK1)
    | ~ m1_subset_1(k5_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_waybel_7(k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)),sK1)
    | v1_xboole_0(k5_waybel_0(sK1,sK2))
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1387])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_783,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_368,c_19])).

cnf(c_784,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k5_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_783])).

cnf(c_788,plain,
    ( m1_subset_1(k5_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_784,c_18])).

cnf(c_789,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k5_waybel_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_788])).

cnf(c_1390,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK1))
    | m1_subset_1(k5_waybel_0(sK1,X0_49),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_789])).

cnf(c_1439,plain,
    ( m1_subset_1(k5_waybel_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1390])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_759,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_347,c_23])).

cnf(c_760,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v1_xboole_0(k5_waybel_0(sK1,X0))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1) ),
    inference(unflattening,[status(thm)],[c_759])).

cnf(c_764,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v1_xboole_0(k5_waybel_0(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_760,c_19,c_18])).

cnf(c_1391,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK1))
    | ~ v1_xboole_0(k5_waybel_0(sK1,X0_49)) ),
    inference(subtyping,[status(esa)],[c_764])).

cnf(c_1436,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v1_xboole_0(k5_waybel_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1391])).

cnf(c_11,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_279,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_11,c_0])).

cnf(c_741,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_279,c_23])).

cnf(c_742,plain,
    ( v1_waybel_0(k5_waybel_0(sK1,X0),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1) ),
    inference(unflattening,[status(thm)],[c_741])).

cnf(c_746,plain,
    ( v1_waybel_0(k5_waybel_0(sK1,X0),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_742,c_19,c_18])).

cnf(c_1392,plain,
    ( v1_waybel_0(k5_waybel_0(sK1,X0_49),sK1)
    | ~ m1_subset_1(X0_49,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_746])).

cnf(c_1433,plain,
    ( v1_waybel_0(k5_waybel_0(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1392])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_319,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X2)
    | X1 != X2
    | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_720,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_320,c_21])).

cnf(c_721,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | k1_yellow_0(sK1,k5_waybel_0(sK1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_720])).

cnf(c_725,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k1_yellow_0(sK1,k5_waybel_0(sK1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_721,c_23,c_22,c_19,c_18])).

cnf(c_1393,plain,
    ( ~ m1_subset_1(X0_49,u1_struct_0(sK1))
    | k1_yellow_0(sK1,k5_waybel_0(sK1,X0_49)) = X0_49 ),
    inference(subtyping,[status(esa)],[c_725])).

cnf(c_1430,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k1_yellow_0(sK1,k5_waybel_0(sK1,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1393])).

cnf(c_1406,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_1421,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_1413,plain,
    ( X0_49 != X1_49
    | k5_waybel_0(X0_50,X0_49) = k5_waybel_0(X0_50,X1_49) ),
    theory(equality)).

cnf(c_1419,plain,
    ( k5_waybel_0(sK1,sK2) = k5_waybel_0(sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1413])).

cnf(c_15,negated_conjecture,
    ( ~ v4_waybel_7(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1857,c_1793,c_1448,c_1404,c_1439,c_1436,c_1433,c_1430,c_1421,c_1419,c_15,c_17])).


%------------------------------------------------------------------------------
