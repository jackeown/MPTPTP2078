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
% DateTime   : Thu Dec  3 12:28:39 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 465 expanded)
%              Number of clauses        :   76 ( 124 expanded)
%              Number of leaves         :   15 ( 118 expanded)
%              Depth                    :   19
%              Number of atoms          :  562 (2186 expanded)
%              Number of equality atoms :   62 (  73 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] :
          ( v7_waybel_0(X1)
          & v6_waybel_0(X1,X0)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] :
          ( v6_waybel_0(X1,X0)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] :
          ( v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] :
          ( v4_orders_2(X1)
          & v3_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] :
          ( v3_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] :
          ( ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) )
     => ( ~ v2_struct_0(sK2(X0))
        & l1_waybel_0(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ~ v2_struct_0(sK2(X0))
        & l1_waybel_0(sK2(X0),X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f39])).

fof(f58,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f34])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK1(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3))
        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3))
                      & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK1(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_waybel_0(X0,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0),u1_waybel_0(X0,sK4)))
        & l1_waybel_0(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK3,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),u1_waybel_0(sK3,X1)))
          & l1_waybel_0(X1,sK3)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
    & l1_waybel_0(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f33,f42,f41])).

fof(f63,plain,(
    l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f61,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ~ r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                 => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_13,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k4_yellow_6(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_15,plain,
    ( l1_waybel_0(sK2(X0),X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_929,plain,
    ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X0)
    | X2 != X0
    | sK2(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_930,plain,
    ( m1_subset_1(k4_yellow_6(X0,sK2(X0)),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_929])).

cnf(c_3207,plain,
    ( m1_subset_1(k4_yellow_6(X0_54,sK2(X0_54)),u1_struct_0(X0_54))
    | v2_struct_0(X0_54)
    | ~ l1_struct_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_930])).

cnf(c_3637,plain,
    ( m1_subset_1(k4_yellow_6(X0_54,sK2(X0_54)),u1_struct_0(X0_54)) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_struct_0(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3207])).

cnf(c_5,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_17,negated_conjecture,
    ( l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_806,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_807,plain,
    ( r1_waybel_0(sK3,sK4,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK3,sK4,X0,X1),u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_806])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_19,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_811,plain,
    ( m1_subset_1(sK0(sK3,sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_waybel_0(sK3,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_807,c_20,c_19,c_18])).

cnf(c_812,plain,
    ( r1_waybel_0(sK3,sK4,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK3,sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_811])).

cnf(c_3212,plain,
    ( r1_waybel_0(sK3,sK4,X0_56)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK3,sK4,X0_56,X0_52),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_812])).

cnf(c_3632,plain,
    ( r1_waybel_0(sK3,sK4,X0_56) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK0(sK3,sK4,X0_56,X0_52),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3212])).

cnf(c_8,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1)
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2) = k2_waybel_0(X1,X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1063,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),X0) = k2_waybel_0(X2,X1,X0)
    | sK4 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_1064,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0) = k2_waybel_0(sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_1063])).

cnf(c_1068,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0) = k2_waybel_0(sK3,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1064,c_20,c_19,c_18])).

cnf(c_3200,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0_52) = k2_waybel_0(sK3,sK4,X0_52) ),
    inference(subtyping,[status(esa)],[c_1068])).

cnf(c_3644,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0_52) = k2_waybel_0(sK3,sK4,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3200])).

cnf(c_4287,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),sK0(sK3,sK4,X0_56,X0_52)) = k2_waybel_0(sK3,sK4,sK0(sK3,sK4,X0_56,X0_52))
    | r1_waybel_0(sK3,sK4,X0_56) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3632,c_3644])).

cnf(c_4544,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),sK0(sK3,sK4,X0_56,k4_yellow_6(sK4,sK2(sK4)))) = k2_waybel_0(sK3,sK4,sK0(sK3,sK4,X0_56,k4_yellow_6(sK4,sK2(sK4))))
    | r1_waybel_0(sK3,sK4,X0_56) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3637,c_4287])).

cnf(c_22,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_23,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_orders_2(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_242,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | l1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_9,c_2])).

cnf(c_1030,plain,
    ( ~ l1_struct_0(X0)
    | l1_struct_0(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_242,c_17])).

cnf(c_1031,plain,
    ( l1_struct_0(sK4)
    | ~ l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1030])).

cnf(c_1032,plain,
    ( l1_struct_0(sK4) = iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1031])).

cnf(c_5015,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),sK0(sK3,sK4,X0_56,k4_yellow_6(sK4,sK2(sK4)))) = k2_waybel_0(sK3,sK4,sK0(sK3,sK4,X0_56,k4_yellow_6(sK4,sK2(sK4))))
    | r1_waybel_0(sK3,sK4,X0_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4544,c_22,c_23,c_1032])).

cnf(c_16,negated_conjecture,
    ( ~ r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3220,negated_conjecture,
    ( ~ r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3624,plain,
    ( r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3220])).

cnf(c_5023,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),sK0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),k4_yellow_6(sK4,sK2(sK4)))) = k2_waybel_0(sK3,sK4,sK0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),k4_yellow_6(sK4,sK2(sK4)))) ),
    inference(superposition,[status(thm)],[c_5015,c_3624])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1865,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_1866,plain,
    ( ~ l1_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_1865])).

cnf(c_1868,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1866,c_19,c_1031])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(k3_funct_2(X1,X2,X0,X3),k2_relset_1(X1,X2,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_11,plain,
    ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_258,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
    | r2_hidden(k3_funct_2(X3,X5,X4,X2),k2_relset_1(X3,X5,X4))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X5)
    | ~ v1_funct_1(X4)
    | u1_waybel_0(X1,X0) != X4
    | u1_struct_0(X1) != X5
    | u1_struct_0(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_259,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ v1_funct_1(u1_waybel_0(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_12,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | v1_funct_1(u1_waybel_0(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_10,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_263,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X1)
    | r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_259,c_12,c_10])).

cnf(c_264,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_263])).

cnf(c_1009,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),X0),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1)))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X2))
    | sK4 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_264,c_17])).

cnf(c_1010,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
    | ~ l1_struct_0(sK3)
    | v1_xboole_0(u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1009])).

cnf(c_67,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1014,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1010,c_20,c_19,c_67])).

cnf(c_1015,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1014])).

cnf(c_2104,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1868,c_1015])).

cnf(c_3197,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0_52),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) ),
    inference(subtyping,[status(esa)],[c_2104])).

cnf(c_3647,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0_52),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3197])).

cnf(c_5051,plain,
    ( m1_subset_1(sK0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),k4_yellow_6(sK4,sK2(sK4))),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k2_waybel_0(sK3,sK4,sK0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),k4_yellow_6(sK4,sK2(sK4)))),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5023,c_3647])).

cnf(c_3848,plain,
    ( r1_waybel_0(sK3,sK4,X0_56)
    | m1_subset_1(sK0(sK3,sK4,X0_56,k4_yellow_6(sK4,sK2(sK4))),u1_struct_0(sK4))
    | ~ m1_subset_1(k4_yellow_6(sK4,sK2(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3212])).

cnf(c_3991,plain,
    ( r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
    | m1_subset_1(sK0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),k4_yellow_6(sK4,sK2(sK4))),u1_struct_0(sK4))
    | ~ m1_subset_1(k4_yellow_6(sK4,sK2(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3848])).

cnf(c_3992,plain,
    ( r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) = iProver_top
    | m1_subset_1(sK0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),k4_yellow_6(sK4,sK2(sK4))),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k4_yellow_6(sK4,sK2(sK4)),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3991])).

cnf(c_3,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_827,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_17])).

cnf(c_828,plain,
    ( r1_waybel_0(sK3,sK4,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK0(sK3,sK4,X0,X1)),X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_827])).

cnf(c_832,plain,
    ( ~ r2_hidden(k2_waybel_0(sK3,sK4,sK0(sK3,sK4,X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_waybel_0(sK3,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_828,c_20,c_19,c_18])).

cnf(c_833,plain,
    ( r1_waybel_0(sK3,sK4,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK0(sK3,sK4,X0,X1)),X0) ),
    inference(renaming,[status(thm)],[c_832])).

cnf(c_3211,plain,
    ( r1_waybel_0(sK3,sK4,X0_56)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK0(sK3,sK4,X0_56,X0_52)),X0_56) ),
    inference(subtyping,[status(esa)],[c_833])).

cnf(c_3846,plain,
    ( r1_waybel_0(sK3,sK4,X0_56)
    | ~ m1_subset_1(k4_yellow_6(sK4,sK2(sK4)),u1_struct_0(sK4))
    | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK0(sK3,sK4,X0_56,k4_yellow_6(sK4,sK2(sK4)))),X0_56) ),
    inference(instantiation,[status(thm)],[c_3211])).

cnf(c_3952,plain,
    ( r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
    | ~ m1_subset_1(k4_yellow_6(sK4,sK2(sK4)),u1_struct_0(sK4))
    | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),k4_yellow_6(sK4,sK2(sK4)))),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_3846])).

cnf(c_3953,plain,
    ( r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) = iProver_top
    | m1_subset_1(k4_yellow_6(sK4,sK2(sK4)),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k2_waybel_0(sK3,sK4,sK0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),k4_yellow_6(sK4,sK2(sK4)))),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3952])).

cnf(c_1773,plain,
    ( m1_subset_1(k4_yellow_6(X0,sK2(X0)),u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_930,c_18])).

cnf(c_1774,plain,
    ( m1_subset_1(k4_yellow_6(sK4,sK2(sK4)),u1_struct_0(sK4))
    | ~ l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1773])).

cnf(c_1775,plain,
    ( m1_subset_1(k4_yellow_6(sK4,sK2(sK4)),u1_struct_0(sK4)) = iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1774])).

cnf(c_25,plain,
    ( r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5051,c_3992,c_3953,c_1775,c_1032,c_25,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:09:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.16/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.02  
% 2.16/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.16/1.02  
% 2.16/1.02  ------  iProver source info
% 2.16/1.02  
% 2.16/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.16/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.16/1.02  git: non_committed_changes: false
% 2.16/1.02  git: last_make_outside_of_git: false
% 2.16/1.02  
% 2.16/1.02  ------ 
% 2.16/1.02  
% 2.16/1.02  ------ Input Options
% 2.16/1.02  
% 2.16/1.02  --out_options                           all
% 2.16/1.02  --tptp_safe_out                         true
% 2.16/1.02  --problem_path                          ""
% 2.16/1.02  --include_path                          ""
% 2.16/1.02  --clausifier                            res/vclausify_rel
% 2.16/1.02  --clausifier_options                    --mode clausify
% 2.16/1.02  --stdin                                 false
% 2.16/1.02  --stats_out                             all
% 2.16/1.02  
% 2.16/1.02  ------ General Options
% 2.16/1.02  
% 2.16/1.02  --fof                                   false
% 2.16/1.02  --time_out_real                         305.
% 2.16/1.02  --time_out_virtual                      -1.
% 2.16/1.02  --symbol_type_check                     false
% 2.16/1.02  --clausify_out                          false
% 2.16/1.02  --sig_cnt_out                           false
% 2.16/1.02  --trig_cnt_out                          false
% 2.16/1.02  --trig_cnt_out_tolerance                1.
% 2.16/1.02  --trig_cnt_out_sk_spl                   false
% 2.16/1.02  --abstr_cl_out                          false
% 2.16/1.02  
% 2.16/1.02  ------ Global Options
% 2.16/1.02  
% 2.16/1.02  --schedule                              default
% 2.16/1.02  --add_important_lit                     false
% 2.16/1.02  --prop_solver_per_cl                    1000
% 2.16/1.02  --min_unsat_core                        false
% 2.16/1.02  --soft_assumptions                      false
% 2.16/1.02  --soft_lemma_size                       3
% 2.16/1.02  --prop_impl_unit_size                   0
% 2.16/1.02  --prop_impl_unit                        []
% 2.16/1.02  --share_sel_clauses                     true
% 2.16/1.02  --reset_solvers                         false
% 2.16/1.02  --bc_imp_inh                            [conj_cone]
% 2.16/1.02  --conj_cone_tolerance                   3.
% 2.16/1.02  --extra_neg_conj                        none
% 2.16/1.02  --large_theory_mode                     true
% 2.16/1.02  --prolific_symb_bound                   200
% 2.16/1.02  --lt_threshold                          2000
% 2.16/1.02  --clause_weak_htbl                      true
% 2.16/1.02  --gc_record_bc_elim                     false
% 2.16/1.02  
% 2.16/1.02  ------ Preprocessing Options
% 2.16/1.02  
% 2.16/1.02  --preprocessing_flag                    true
% 2.16/1.02  --time_out_prep_mult                    0.1
% 2.16/1.02  --splitting_mode                        input
% 2.16/1.02  --splitting_grd                         true
% 2.16/1.02  --splitting_cvd                         false
% 2.16/1.02  --splitting_cvd_svl                     false
% 2.16/1.02  --splitting_nvd                         32
% 2.16/1.02  --sub_typing                            true
% 2.16/1.02  --prep_gs_sim                           true
% 2.16/1.02  --prep_unflatten                        true
% 2.16/1.02  --prep_res_sim                          true
% 2.16/1.02  --prep_upred                            true
% 2.16/1.02  --prep_sem_filter                       exhaustive
% 2.16/1.02  --prep_sem_filter_out                   false
% 2.16/1.02  --pred_elim                             true
% 2.16/1.02  --res_sim_input                         true
% 2.16/1.02  --eq_ax_congr_red                       true
% 2.16/1.02  --pure_diseq_elim                       true
% 2.16/1.02  --brand_transform                       false
% 2.16/1.02  --non_eq_to_eq                          false
% 2.16/1.02  --prep_def_merge                        true
% 2.16/1.02  --prep_def_merge_prop_impl              false
% 2.16/1.02  --prep_def_merge_mbd                    true
% 2.16/1.02  --prep_def_merge_tr_red                 false
% 2.16/1.02  --prep_def_merge_tr_cl                  false
% 2.16/1.02  --smt_preprocessing                     true
% 2.16/1.02  --smt_ac_axioms                         fast
% 2.16/1.02  --preprocessed_out                      false
% 2.16/1.02  --preprocessed_stats                    false
% 2.16/1.02  
% 2.16/1.02  ------ Abstraction refinement Options
% 2.16/1.02  
% 2.16/1.02  --abstr_ref                             []
% 2.16/1.02  --abstr_ref_prep                        false
% 2.16/1.02  --abstr_ref_until_sat                   false
% 2.16/1.02  --abstr_ref_sig_restrict                funpre
% 2.16/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.02  --abstr_ref_under                       []
% 2.16/1.02  
% 2.16/1.02  ------ SAT Options
% 2.16/1.02  
% 2.16/1.02  --sat_mode                              false
% 2.16/1.02  --sat_fm_restart_options                ""
% 2.16/1.02  --sat_gr_def                            false
% 2.16/1.02  --sat_epr_types                         true
% 2.16/1.02  --sat_non_cyclic_types                  false
% 2.16/1.02  --sat_finite_models                     false
% 2.16/1.02  --sat_fm_lemmas                         false
% 2.16/1.02  --sat_fm_prep                           false
% 2.16/1.02  --sat_fm_uc_incr                        true
% 2.16/1.02  --sat_out_model                         small
% 2.16/1.02  --sat_out_clauses                       false
% 2.16/1.02  
% 2.16/1.02  ------ QBF Options
% 2.16/1.02  
% 2.16/1.02  --qbf_mode                              false
% 2.16/1.02  --qbf_elim_univ                         false
% 2.16/1.02  --qbf_dom_inst                          none
% 2.16/1.02  --qbf_dom_pre_inst                      false
% 2.16/1.02  --qbf_sk_in                             false
% 2.16/1.02  --qbf_pred_elim                         true
% 2.16/1.02  --qbf_split                             512
% 2.16/1.02  
% 2.16/1.02  ------ BMC1 Options
% 2.16/1.02  
% 2.16/1.02  --bmc1_incremental                      false
% 2.16/1.02  --bmc1_axioms                           reachable_all
% 2.16/1.02  --bmc1_min_bound                        0
% 2.16/1.02  --bmc1_max_bound                        -1
% 2.16/1.02  --bmc1_max_bound_default                -1
% 2.16/1.02  --bmc1_symbol_reachability              true
% 2.16/1.02  --bmc1_property_lemmas                  false
% 2.16/1.02  --bmc1_k_induction                      false
% 2.16/1.02  --bmc1_non_equiv_states                 false
% 2.16/1.02  --bmc1_deadlock                         false
% 2.16/1.02  --bmc1_ucm                              false
% 2.16/1.02  --bmc1_add_unsat_core                   none
% 2.16/1.02  --bmc1_unsat_core_children              false
% 2.16/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.02  --bmc1_out_stat                         full
% 2.16/1.02  --bmc1_ground_init                      false
% 2.16/1.02  --bmc1_pre_inst_next_state              false
% 2.16/1.02  --bmc1_pre_inst_state                   false
% 2.16/1.02  --bmc1_pre_inst_reach_state             false
% 2.16/1.02  --bmc1_out_unsat_core                   false
% 2.16/1.02  --bmc1_aig_witness_out                  false
% 2.16/1.02  --bmc1_verbose                          false
% 2.16/1.02  --bmc1_dump_clauses_tptp                false
% 2.16/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.02  --bmc1_dump_file                        -
% 2.16/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.02  --bmc1_ucm_extend_mode                  1
% 2.16/1.02  --bmc1_ucm_init_mode                    2
% 2.16/1.02  --bmc1_ucm_cone_mode                    none
% 2.16/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.02  --bmc1_ucm_relax_model                  4
% 2.16/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.02  --bmc1_ucm_layered_model                none
% 2.16/1.02  --bmc1_ucm_max_lemma_size               10
% 2.16/1.02  
% 2.16/1.02  ------ AIG Options
% 2.16/1.02  
% 2.16/1.02  --aig_mode                              false
% 2.16/1.02  
% 2.16/1.02  ------ Instantiation Options
% 2.16/1.02  
% 2.16/1.02  --instantiation_flag                    true
% 2.16/1.02  --inst_sos_flag                         false
% 2.16/1.02  --inst_sos_phase                        true
% 2.16/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.02  --inst_lit_sel_side                     num_symb
% 2.16/1.02  --inst_solver_per_active                1400
% 2.16/1.02  --inst_solver_calls_frac                1.
% 2.16/1.02  --inst_passive_queue_type               priority_queues
% 2.16/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.02  --inst_passive_queues_freq              [25;2]
% 2.16/1.02  --inst_dismatching                      true
% 2.16/1.02  --inst_eager_unprocessed_to_passive     true
% 2.16/1.02  --inst_prop_sim_given                   true
% 2.16/1.02  --inst_prop_sim_new                     false
% 2.16/1.02  --inst_subs_new                         false
% 2.16/1.02  --inst_eq_res_simp                      false
% 2.16/1.02  --inst_subs_given                       false
% 2.16/1.02  --inst_orphan_elimination               true
% 2.16/1.02  --inst_learning_loop_flag               true
% 2.16/1.02  --inst_learning_start                   3000
% 2.16/1.02  --inst_learning_factor                  2
% 2.16/1.02  --inst_start_prop_sim_after_learn       3
% 2.16/1.02  --inst_sel_renew                        solver
% 2.16/1.02  --inst_lit_activity_flag                true
% 2.16/1.02  --inst_restr_to_given                   false
% 2.16/1.02  --inst_activity_threshold               500
% 2.16/1.02  --inst_out_proof                        true
% 2.16/1.02  
% 2.16/1.02  ------ Resolution Options
% 2.16/1.02  
% 2.16/1.02  --resolution_flag                       true
% 2.16/1.02  --res_lit_sel                           adaptive
% 2.16/1.02  --res_lit_sel_side                      none
% 2.16/1.02  --res_ordering                          kbo
% 2.16/1.02  --res_to_prop_solver                    active
% 2.16/1.02  --res_prop_simpl_new                    false
% 2.16/1.02  --res_prop_simpl_given                  true
% 2.16/1.02  --res_passive_queue_type                priority_queues
% 2.16/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.02  --res_passive_queues_freq               [15;5]
% 2.16/1.02  --res_forward_subs                      full
% 2.16/1.02  --res_backward_subs                     full
% 2.16/1.02  --res_forward_subs_resolution           true
% 2.16/1.02  --res_backward_subs_resolution          true
% 2.16/1.02  --res_orphan_elimination                true
% 2.16/1.02  --res_time_limit                        2.
% 2.16/1.02  --res_out_proof                         true
% 2.16/1.02  
% 2.16/1.02  ------ Superposition Options
% 2.16/1.02  
% 2.16/1.02  --superposition_flag                    true
% 2.16/1.02  --sup_passive_queue_type                priority_queues
% 2.16/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.02  --demod_completeness_check              fast
% 2.16/1.02  --demod_use_ground                      true
% 2.16/1.02  --sup_to_prop_solver                    passive
% 2.16/1.02  --sup_prop_simpl_new                    true
% 2.16/1.02  --sup_prop_simpl_given                  true
% 2.16/1.02  --sup_fun_splitting                     false
% 2.16/1.02  --sup_smt_interval                      50000
% 2.16/1.02  
% 2.16/1.02  ------ Superposition Simplification Setup
% 2.16/1.02  
% 2.16/1.02  --sup_indices_passive                   []
% 2.16/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.02  --sup_full_bw                           [BwDemod]
% 2.16/1.02  --sup_immed_triv                        [TrivRules]
% 2.16/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.02  --sup_immed_bw_main                     []
% 2.16/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.02  
% 2.16/1.02  ------ Combination Options
% 2.16/1.02  
% 2.16/1.02  --comb_res_mult                         3
% 2.16/1.02  --comb_sup_mult                         2
% 2.16/1.02  --comb_inst_mult                        10
% 2.16/1.02  
% 2.16/1.02  ------ Debug Options
% 2.16/1.02  
% 2.16/1.02  --dbg_backtrace                         false
% 2.16/1.02  --dbg_dump_prop_clauses                 false
% 2.16/1.02  --dbg_dump_prop_clauses_file            -
% 2.16/1.02  --dbg_out_stat                          false
% 2.16/1.02  ------ Parsing...
% 2.16/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.16/1.02  
% 2.16/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 2.16/1.02  
% 2.16/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.16/1.02  
% 2.16/1.02  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.16/1.02  ------ Proving...
% 2.16/1.02  ------ Problem Properties 
% 2.16/1.02  
% 2.16/1.02  
% 2.16/1.02  clauses                                 26
% 2.16/1.02  conjectures                             4
% 2.16/1.02  EPR                                     4
% 2.16/1.02  Horn                                    16
% 2.16/1.02  unary                                   7
% 2.16/1.02  binary                                  6
% 2.16/1.02  lits                                    71
% 2.16/1.02  lits eq                                 2
% 2.16/1.02  fd_pure                                 0
% 2.16/1.02  fd_pseudo                               0
% 2.16/1.02  fd_cond                                 0
% 2.16/1.02  fd_pseudo_cond                          0
% 2.16/1.02  AC symbols                              0
% 2.16/1.02  
% 2.16/1.02  ------ Schedule dynamic 5 is on 
% 2.16/1.02  
% 2.16/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.16/1.02  
% 2.16/1.02  
% 2.16/1.02  ------ 
% 2.16/1.02  Current options:
% 2.16/1.02  ------ 
% 2.16/1.02  
% 2.16/1.02  ------ Input Options
% 2.16/1.02  
% 2.16/1.02  --out_options                           all
% 2.16/1.02  --tptp_safe_out                         true
% 2.16/1.02  --problem_path                          ""
% 2.16/1.02  --include_path                          ""
% 2.16/1.02  --clausifier                            res/vclausify_rel
% 2.16/1.02  --clausifier_options                    --mode clausify
% 2.16/1.02  --stdin                                 false
% 2.16/1.02  --stats_out                             all
% 2.16/1.02  
% 2.16/1.02  ------ General Options
% 2.16/1.02  
% 2.16/1.02  --fof                                   false
% 2.16/1.02  --time_out_real                         305.
% 2.16/1.02  --time_out_virtual                      -1.
% 2.16/1.02  --symbol_type_check                     false
% 2.16/1.02  --clausify_out                          false
% 2.16/1.02  --sig_cnt_out                           false
% 2.16/1.02  --trig_cnt_out                          false
% 2.16/1.02  --trig_cnt_out_tolerance                1.
% 2.16/1.02  --trig_cnt_out_sk_spl                   false
% 2.16/1.02  --abstr_cl_out                          false
% 2.16/1.02  
% 2.16/1.02  ------ Global Options
% 2.16/1.02  
% 2.16/1.02  --schedule                              default
% 2.16/1.02  --add_important_lit                     false
% 2.16/1.02  --prop_solver_per_cl                    1000
% 2.16/1.02  --min_unsat_core                        false
% 2.16/1.02  --soft_assumptions                      false
% 2.16/1.02  --soft_lemma_size                       3
% 2.16/1.02  --prop_impl_unit_size                   0
% 2.16/1.02  --prop_impl_unit                        []
% 2.16/1.02  --share_sel_clauses                     true
% 2.16/1.02  --reset_solvers                         false
% 2.16/1.02  --bc_imp_inh                            [conj_cone]
% 2.16/1.02  --conj_cone_tolerance                   3.
% 2.16/1.02  --extra_neg_conj                        none
% 2.16/1.02  --large_theory_mode                     true
% 2.16/1.02  --prolific_symb_bound                   200
% 2.16/1.02  --lt_threshold                          2000
% 2.16/1.02  --clause_weak_htbl                      true
% 2.16/1.02  --gc_record_bc_elim                     false
% 2.16/1.02  
% 2.16/1.02  ------ Preprocessing Options
% 2.16/1.02  
% 2.16/1.02  --preprocessing_flag                    true
% 2.16/1.02  --time_out_prep_mult                    0.1
% 2.16/1.02  --splitting_mode                        input
% 2.16/1.02  --splitting_grd                         true
% 2.16/1.02  --splitting_cvd                         false
% 2.16/1.02  --splitting_cvd_svl                     false
% 2.16/1.02  --splitting_nvd                         32
% 2.16/1.02  --sub_typing                            true
% 2.16/1.02  --prep_gs_sim                           true
% 2.16/1.02  --prep_unflatten                        true
% 2.16/1.02  --prep_res_sim                          true
% 2.16/1.02  --prep_upred                            true
% 2.16/1.02  --prep_sem_filter                       exhaustive
% 2.16/1.02  --prep_sem_filter_out                   false
% 2.16/1.02  --pred_elim                             true
% 2.16/1.02  --res_sim_input                         true
% 2.16/1.02  --eq_ax_congr_red                       true
% 2.16/1.02  --pure_diseq_elim                       true
% 2.16/1.02  --brand_transform                       false
% 2.16/1.02  --non_eq_to_eq                          false
% 2.16/1.02  --prep_def_merge                        true
% 2.16/1.02  --prep_def_merge_prop_impl              false
% 2.16/1.02  --prep_def_merge_mbd                    true
% 2.16/1.02  --prep_def_merge_tr_red                 false
% 2.16/1.02  --prep_def_merge_tr_cl                  false
% 2.16/1.02  --smt_preprocessing                     true
% 2.16/1.02  --smt_ac_axioms                         fast
% 2.16/1.02  --preprocessed_out                      false
% 2.16/1.02  --preprocessed_stats                    false
% 2.16/1.02  
% 2.16/1.02  ------ Abstraction refinement Options
% 2.16/1.02  
% 2.16/1.02  --abstr_ref                             []
% 2.16/1.02  --abstr_ref_prep                        false
% 2.16/1.02  --abstr_ref_until_sat                   false
% 2.16/1.02  --abstr_ref_sig_restrict                funpre
% 2.16/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.02  --abstr_ref_under                       []
% 2.16/1.02  
% 2.16/1.02  ------ SAT Options
% 2.16/1.02  
% 2.16/1.02  --sat_mode                              false
% 2.16/1.02  --sat_fm_restart_options                ""
% 2.16/1.02  --sat_gr_def                            false
% 2.16/1.02  --sat_epr_types                         true
% 2.16/1.02  --sat_non_cyclic_types                  false
% 2.16/1.02  --sat_finite_models                     false
% 2.16/1.02  --sat_fm_lemmas                         false
% 2.16/1.02  --sat_fm_prep                           false
% 2.16/1.02  --sat_fm_uc_incr                        true
% 2.16/1.02  --sat_out_model                         small
% 2.16/1.02  --sat_out_clauses                       false
% 2.16/1.02  
% 2.16/1.02  ------ QBF Options
% 2.16/1.02  
% 2.16/1.02  --qbf_mode                              false
% 2.16/1.02  --qbf_elim_univ                         false
% 2.16/1.02  --qbf_dom_inst                          none
% 2.16/1.02  --qbf_dom_pre_inst                      false
% 2.16/1.02  --qbf_sk_in                             false
% 2.16/1.02  --qbf_pred_elim                         true
% 2.16/1.02  --qbf_split                             512
% 2.16/1.02  
% 2.16/1.02  ------ BMC1 Options
% 2.16/1.02  
% 2.16/1.02  --bmc1_incremental                      false
% 2.16/1.02  --bmc1_axioms                           reachable_all
% 2.16/1.02  --bmc1_min_bound                        0
% 2.16/1.02  --bmc1_max_bound                        -1
% 2.16/1.02  --bmc1_max_bound_default                -1
% 2.16/1.02  --bmc1_symbol_reachability              true
% 2.16/1.02  --bmc1_property_lemmas                  false
% 2.16/1.02  --bmc1_k_induction                      false
% 2.16/1.02  --bmc1_non_equiv_states                 false
% 2.16/1.02  --bmc1_deadlock                         false
% 2.16/1.02  --bmc1_ucm                              false
% 2.16/1.02  --bmc1_add_unsat_core                   none
% 2.16/1.02  --bmc1_unsat_core_children              false
% 2.16/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.02  --bmc1_out_stat                         full
% 2.16/1.02  --bmc1_ground_init                      false
% 2.16/1.02  --bmc1_pre_inst_next_state              false
% 2.16/1.02  --bmc1_pre_inst_state                   false
% 2.16/1.02  --bmc1_pre_inst_reach_state             false
% 2.16/1.02  --bmc1_out_unsat_core                   false
% 2.16/1.02  --bmc1_aig_witness_out                  false
% 2.16/1.02  --bmc1_verbose                          false
% 2.16/1.02  --bmc1_dump_clauses_tptp                false
% 2.16/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.02  --bmc1_dump_file                        -
% 2.16/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.02  --bmc1_ucm_extend_mode                  1
% 2.16/1.02  --bmc1_ucm_init_mode                    2
% 2.16/1.02  --bmc1_ucm_cone_mode                    none
% 2.16/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.02  --bmc1_ucm_relax_model                  4
% 2.16/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.02  --bmc1_ucm_layered_model                none
% 2.16/1.02  --bmc1_ucm_max_lemma_size               10
% 2.16/1.02  
% 2.16/1.02  ------ AIG Options
% 2.16/1.02  
% 2.16/1.02  --aig_mode                              false
% 2.16/1.02  
% 2.16/1.02  ------ Instantiation Options
% 2.16/1.02  
% 2.16/1.02  --instantiation_flag                    true
% 2.16/1.02  --inst_sos_flag                         false
% 2.16/1.02  --inst_sos_phase                        true
% 2.16/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.02  --inst_lit_sel_side                     none
% 2.16/1.02  --inst_solver_per_active                1400
% 2.16/1.02  --inst_solver_calls_frac                1.
% 2.16/1.02  --inst_passive_queue_type               priority_queues
% 2.16/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.02  --inst_passive_queues_freq              [25;2]
% 2.16/1.02  --inst_dismatching                      true
% 2.16/1.02  --inst_eager_unprocessed_to_passive     true
% 2.16/1.02  --inst_prop_sim_given                   true
% 2.16/1.02  --inst_prop_sim_new                     false
% 2.16/1.02  --inst_subs_new                         false
% 2.16/1.02  --inst_eq_res_simp                      false
% 2.16/1.02  --inst_subs_given                       false
% 2.16/1.02  --inst_orphan_elimination               true
% 2.16/1.02  --inst_learning_loop_flag               true
% 2.16/1.02  --inst_learning_start                   3000
% 2.16/1.02  --inst_learning_factor                  2
% 2.16/1.02  --inst_start_prop_sim_after_learn       3
% 2.16/1.02  --inst_sel_renew                        solver
% 2.16/1.02  --inst_lit_activity_flag                true
% 2.16/1.02  --inst_restr_to_given                   false
% 2.16/1.02  --inst_activity_threshold               500
% 2.16/1.02  --inst_out_proof                        true
% 2.16/1.02  
% 2.16/1.02  ------ Resolution Options
% 2.16/1.02  
% 2.16/1.02  --resolution_flag                       false
% 2.16/1.02  --res_lit_sel                           adaptive
% 2.16/1.02  --res_lit_sel_side                      none
% 2.16/1.02  --res_ordering                          kbo
% 2.16/1.02  --res_to_prop_solver                    active
% 2.16/1.02  --res_prop_simpl_new                    false
% 2.16/1.02  --res_prop_simpl_given                  true
% 2.16/1.02  --res_passive_queue_type                priority_queues
% 2.16/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.02  --res_passive_queues_freq               [15;5]
% 2.16/1.02  --res_forward_subs                      full
% 2.16/1.02  --res_backward_subs                     full
% 2.16/1.02  --res_forward_subs_resolution           true
% 2.16/1.02  --res_backward_subs_resolution          true
% 2.16/1.02  --res_orphan_elimination                true
% 2.16/1.02  --res_time_limit                        2.
% 2.16/1.02  --res_out_proof                         true
% 2.16/1.02  
% 2.16/1.02  ------ Superposition Options
% 2.16/1.02  
% 2.16/1.02  --superposition_flag                    true
% 2.16/1.02  --sup_passive_queue_type                priority_queues
% 2.16/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.02  --demod_completeness_check              fast
% 2.16/1.02  --demod_use_ground                      true
% 2.16/1.02  --sup_to_prop_solver                    passive
% 2.16/1.02  --sup_prop_simpl_new                    true
% 2.16/1.02  --sup_prop_simpl_given                  true
% 2.16/1.02  --sup_fun_splitting                     false
% 2.16/1.02  --sup_smt_interval                      50000
% 2.16/1.02  
% 2.16/1.02  ------ Superposition Simplification Setup
% 2.16/1.02  
% 2.16/1.02  --sup_indices_passive                   []
% 2.16/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.02  --sup_full_bw                           [BwDemod]
% 2.16/1.02  --sup_immed_triv                        [TrivRules]
% 2.16/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.02  --sup_immed_bw_main                     []
% 2.16/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.02  
% 2.16/1.02  ------ Combination Options
% 2.16/1.02  
% 2.16/1.02  --comb_res_mult                         3
% 2.16/1.02  --comb_sup_mult                         2
% 2.16/1.02  --comb_inst_mult                        10
% 2.16/1.02  
% 2.16/1.02  ------ Debug Options
% 2.16/1.02  
% 2.16/1.02  --dbg_backtrace                         false
% 2.16/1.02  --dbg_dump_prop_clauses                 false
% 2.16/1.02  --dbg_dump_prop_clauses_file            -
% 2.16/1.02  --dbg_out_stat                          false
% 2.16/1.02  
% 2.16/1.02  
% 2.16/1.02  
% 2.16/1.02  
% 2.16/1.02  ------ Proving...
% 2.16/1.02  
% 2.16/1.02  
% 2.16/1.02  % SZS status Theorem for theBenchmark.p
% 2.16/1.02  
% 2.16/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.16/1.02  
% 2.16/1.02  fof(f8,axiom,(
% 2.16/1.02    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)))),
% 2.16/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.02  
% 2.16/1.02  fof(f29,plain,(
% 2.16/1.02    ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.16/1.02    inference(ennf_transformation,[],[f8])).
% 2.16/1.02  
% 2.16/1.02  fof(f30,plain,(
% 2.16/1.02    ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.16/1.02    inference(flattening,[],[f29])).
% 2.16/1.02  
% 2.16/1.02  fof(f57,plain,(
% 2.16/1.02    ( ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f30])).
% 2.16/1.02  
% 2.16/1.02  fof(f9,axiom,(
% 2.16/1.02    ! [X0] : (l1_struct_0(X0) => ? [X1] : (v7_waybel_0(X1) & v6_waybel_0(X1,X0) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 2.16/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.02  
% 2.16/1.02  fof(f12,plain,(
% 2.16/1.02    ! [X0] : (l1_struct_0(X0) => ? [X1] : (v6_waybel_0(X1,X0) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 2.16/1.02    inference(pure_predicate_removal,[],[f9])).
% 2.16/1.02  
% 2.16/1.02  fof(f13,plain,(
% 2.16/1.02    ! [X0] : (l1_struct_0(X0) => ? [X1] : (v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 2.16/1.02    inference(pure_predicate_removal,[],[f12])).
% 2.16/1.02  
% 2.16/1.02  fof(f14,plain,(
% 2.16/1.02    ! [X0] : (l1_struct_0(X0) => ? [X1] : (v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 2.16/1.02    inference(pure_predicate_removal,[],[f13])).
% 2.16/1.02  
% 2.16/1.02  fof(f15,plain,(
% 2.16/1.02    ! [X0] : (l1_struct_0(X0) => ? [X1] : (v3_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 2.16/1.02    inference(pure_predicate_removal,[],[f14])).
% 2.16/1.02  
% 2.16/1.02  fof(f16,plain,(
% 2.16/1.02    ! [X0] : (l1_struct_0(X0) => ? [X1] : (~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 2.16/1.02    inference(pure_predicate_removal,[],[f15])).
% 2.16/1.02  
% 2.16/1.02  fof(f31,plain,(
% 2.16/1.02    ! [X0] : (? [X1] : (~v2_struct_0(X1) & l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 2.16/1.02    inference(ennf_transformation,[],[f16])).
% 2.16/1.02  
% 2.16/1.02  fof(f39,plain,(
% 2.16/1.02    ! [X0] : (? [X1] : (~v2_struct_0(X1) & l1_waybel_0(X1,X0)) => (~v2_struct_0(sK2(X0)) & l1_waybel_0(sK2(X0),X0)))),
% 2.16/1.02    introduced(choice_axiom,[])).
% 2.16/1.02  
% 2.16/1.02  fof(f40,plain,(
% 2.16/1.02    ! [X0] : ((~v2_struct_0(sK2(X0)) & l1_waybel_0(sK2(X0),X0)) | ~l1_struct_0(X0))),
% 2.16/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f39])).
% 2.16/1.02  
% 2.16/1.02  fof(f58,plain,(
% 2.16/1.02    ( ! [X0] : (l1_waybel_0(sK2(X0),X0) | ~l1_struct_0(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f40])).
% 2.16/1.02  
% 2.16/1.02  fof(f4,axiom,(
% 2.16/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 2.16/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.02  
% 2.16/1.02  fof(f22,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.16/1.02    inference(ennf_transformation,[],[f4])).
% 2.16/1.02  
% 2.16/1.02  fof(f23,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.16/1.02    inference(flattening,[],[f22])).
% 2.16/1.02  
% 2.16/1.02  fof(f34,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.16/1.02    inference(nnf_transformation,[],[f23])).
% 2.16/1.02  
% 2.16/1.02  fof(f35,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.16/1.02    inference(rectify,[],[f34])).
% 2.16/1.02  
% 2.16/1.02  fof(f37,plain,(
% 2.16/1.02    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK1(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))))),
% 2.16/1.02    introduced(choice_axiom,[])).
% 2.16/1.02  
% 2.16/1.02  fof(f36,plain,(
% 2.16/1.02    ! [X3,X2,X1,X0] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))))),
% 2.16/1.02    introduced(choice_axiom,[])).
% 2.16/1.02  
% 2.16/1.02  fof(f38,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : ((~r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK1(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.16/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 2.16/1.02  
% 2.16/1.02  fof(f49,plain,(
% 2.16/1.02    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f38])).
% 2.16/1.02  
% 2.16/1.02  fof(f10,conjecture,(
% 2.16/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 2.16/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.02  
% 2.16/1.02  fof(f11,negated_conjecture,(
% 2.16/1.02    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 2.16/1.02    inference(negated_conjecture,[],[f10])).
% 2.16/1.02  
% 2.16/1.02  fof(f32,plain,(
% 2.16/1.02    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 2.16/1.02    inference(ennf_transformation,[],[f11])).
% 2.16/1.02  
% 2.16/1.02  fof(f33,plain,(
% 2.16/1.02    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 2.16/1.02    inference(flattening,[],[f32])).
% 2.16/1.02  
% 2.16/1.02  fof(f42,plain,(
% 2.16/1.02    ( ! [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (~r1_waybel_0(X0,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0),u1_waybel_0(X0,sK4))) & l1_waybel_0(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.16/1.02    introduced(choice_axiom,[])).
% 2.16/1.02  
% 2.16/1.02  fof(f41,plain,(
% 2.16/1.02    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK3,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),u1_waybel_0(sK3,X1))) & l1_waybel_0(X1,sK3) & ~v2_struct_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 2.16/1.02    introduced(choice_axiom,[])).
% 2.16/1.02  
% 2.16/1.02  fof(f43,plain,(
% 2.16/1.02    (~r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) & l1_waybel_0(sK4,sK3) & ~v2_struct_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 2.16/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f33,f42,f41])).
% 2.16/1.02  
% 2.16/1.02  fof(f63,plain,(
% 2.16/1.02    l1_waybel_0(sK4,sK3)),
% 2.16/1.02    inference(cnf_transformation,[],[f43])).
% 2.16/1.02  
% 2.16/1.02  fof(f60,plain,(
% 2.16/1.02    ~v2_struct_0(sK3)),
% 2.16/1.02    inference(cnf_transformation,[],[f43])).
% 2.16/1.02  
% 2.16/1.02  fof(f61,plain,(
% 2.16/1.02    l1_struct_0(sK3)),
% 2.16/1.02    inference(cnf_transformation,[],[f43])).
% 2.16/1.02  
% 2.16/1.02  fof(f62,plain,(
% 2.16/1.02    ~v2_struct_0(sK4)),
% 2.16/1.02    inference(cnf_transformation,[],[f43])).
% 2.16/1.02  
% 2.16/1.02  fof(f5,axiom,(
% 2.16/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2))))),
% 2.16/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.02  
% 2.16/1.02  fof(f24,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (! [X2] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.16/1.02    inference(ennf_transformation,[],[f5])).
% 2.16/1.02  
% 2.16/1.02  fof(f25,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (! [X2] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.16/1.02    inference(flattening,[],[f24])).
% 2.16/1.02  
% 2.16/1.02  fof(f52,plain,(
% 2.16/1.02    ( ! [X2,X0,X1] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f25])).
% 2.16/1.02  
% 2.16/1.02  fof(f6,axiom,(
% 2.16/1.02    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 2.16/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.02  
% 2.16/1.02  fof(f26,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 2.16/1.02    inference(ennf_transformation,[],[f6])).
% 2.16/1.02  
% 2.16/1.02  fof(f53,plain,(
% 2.16/1.02    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f26])).
% 2.16/1.02  
% 2.16/1.02  fof(f3,axiom,(
% 2.16/1.02    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.16/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.02  
% 2.16/1.02  fof(f21,plain,(
% 2.16/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.16/1.02    inference(ennf_transformation,[],[f3])).
% 2.16/1.02  
% 2.16/1.02  fof(f46,plain,(
% 2.16/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f21])).
% 2.16/1.02  
% 2.16/1.02  fof(f64,plain,(
% 2.16/1.02    ~r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))),
% 2.16/1.02    inference(cnf_transformation,[],[f43])).
% 2.16/1.02  
% 2.16/1.02  fof(f2,axiom,(
% 2.16/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.16/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.02  
% 2.16/1.02  fof(f19,plain,(
% 2.16/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.16/1.02    inference(ennf_transformation,[],[f2])).
% 2.16/1.02  
% 2.16/1.02  fof(f20,plain,(
% 2.16/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.16/1.02    inference(flattening,[],[f19])).
% 2.16/1.02  
% 2.16/1.02  fof(f45,plain,(
% 2.16/1.02    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f20])).
% 2.16/1.02  
% 2.16/1.02  fof(f1,axiom,(
% 2.16/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 2.16/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.02  
% 2.16/1.02  fof(f17,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.16/1.02    inference(ennf_transformation,[],[f1])).
% 2.16/1.02  
% 2.16/1.02  fof(f18,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.16/1.02    inference(flattening,[],[f17])).
% 2.16/1.02  
% 2.16/1.02  fof(f44,plain,(
% 2.16/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f18])).
% 2.16/1.02  
% 2.16/1.02  fof(f7,axiom,(
% 2.16/1.02    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 2.16/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/1.02  
% 2.16/1.02  fof(f27,plain,(
% 2.16/1.02    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 2.16/1.02    inference(ennf_transformation,[],[f7])).
% 2.16/1.02  
% 2.16/1.02  fof(f28,plain,(
% 2.16/1.02    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 2.16/1.02    inference(flattening,[],[f27])).
% 2.16/1.02  
% 2.16/1.02  fof(f55,plain,(
% 2.16/1.02    ( ! [X0,X1] : (v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f28])).
% 2.16/1.02  
% 2.16/1.02  fof(f54,plain,(
% 2.16/1.02    ( ! [X0,X1] : (v1_funct_1(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f28])).
% 2.16/1.02  
% 2.16/1.02  fof(f56,plain,(
% 2.16/1.02    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f28])).
% 2.16/1.02  
% 2.16/1.02  fof(f51,plain,(
% 2.16/1.02    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,X2) | ~r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f38])).
% 2.16/1.02  
% 2.16/1.02  cnf(c_13,plain,
% 2.16/1.02      ( ~ l1_waybel_0(X0,X1)
% 2.16/1.02      | m1_subset_1(k4_yellow_6(X1,X0),u1_struct_0(X1))
% 2.16/1.02      | v2_struct_0(X1)
% 2.16/1.02      | ~ l1_struct_0(X1) ),
% 2.16/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_15,plain,
% 2.16/1.02      ( l1_waybel_0(sK2(X0),X0) | ~ l1_struct_0(X0) ),
% 2.16/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_929,plain,
% 2.16/1.02      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
% 2.16/1.02      | v2_struct_0(X0)
% 2.16/1.02      | ~ l1_struct_0(X2)
% 2.16/1.02      | ~ l1_struct_0(X0)
% 2.16/1.02      | X2 != X0
% 2.16/1.02      | sK2(X2) != X1 ),
% 2.16/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_15]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_930,plain,
% 2.16/1.02      ( m1_subset_1(k4_yellow_6(X0,sK2(X0)),u1_struct_0(X0))
% 2.16/1.02      | v2_struct_0(X0)
% 2.16/1.02      | ~ l1_struct_0(X0) ),
% 2.16/1.02      inference(unflattening,[status(thm)],[c_929]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3207,plain,
% 2.16/1.02      ( m1_subset_1(k4_yellow_6(X0_54,sK2(X0_54)),u1_struct_0(X0_54))
% 2.16/1.02      | v2_struct_0(X0_54)
% 2.16/1.02      | ~ l1_struct_0(X0_54) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_930]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3637,plain,
% 2.16/1.02      ( m1_subset_1(k4_yellow_6(X0_54,sK2(X0_54)),u1_struct_0(X0_54)) = iProver_top
% 2.16/1.02      | v2_struct_0(X0_54) = iProver_top
% 2.16/1.02      | l1_struct_0(X0_54) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_3207]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_5,plain,
% 2.16/1.02      ( r1_waybel_0(X0,X1,X2)
% 2.16/1.02      | ~ l1_waybel_0(X1,X0)
% 2.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.16/1.02      | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
% 2.16/1.02      | v2_struct_0(X0)
% 2.16/1.02      | v2_struct_0(X1)
% 2.16/1.02      | ~ l1_struct_0(X0) ),
% 2.16/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_17,negated_conjecture,
% 2.16/1.02      ( l1_waybel_0(sK4,sK3) ),
% 2.16/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_806,plain,
% 2.16/1.02      ( r1_waybel_0(X0,X1,X2)
% 2.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.16/1.02      | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
% 2.16/1.02      | v2_struct_0(X0)
% 2.16/1.02      | v2_struct_0(X1)
% 2.16/1.02      | ~ l1_struct_0(X0)
% 2.16/1.02      | sK4 != X1
% 2.16/1.02      | sK3 != X0 ),
% 2.16/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_17]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_807,plain,
% 2.16/1.02      ( r1_waybel_0(sK3,sK4,X0)
% 2.16/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.16/1.02      | m1_subset_1(sK0(sK3,sK4,X0,X1),u1_struct_0(sK4))
% 2.16/1.02      | v2_struct_0(sK4)
% 2.16/1.02      | v2_struct_0(sK3)
% 2.16/1.02      | ~ l1_struct_0(sK3) ),
% 2.16/1.02      inference(unflattening,[status(thm)],[c_806]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_20,negated_conjecture,
% 2.16/1.02      ( ~ v2_struct_0(sK3) ),
% 2.16/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_19,negated_conjecture,
% 2.16/1.02      ( l1_struct_0(sK3) ),
% 2.16/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_18,negated_conjecture,
% 2.16/1.02      ( ~ v2_struct_0(sK4) ),
% 2.16/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_811,plain,
% 2.16/1.02      ( m1_subset_1(sK0(sK3,sK4,X0,X1),u1_struct_0(sK4))
% 2.16/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.16/1.02      | r1_waybel_0(sK3,sK4,X0) ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_807,c_20,c_19,c_18]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_812,plain,
% 2.16/1.02      ( r1_waybel_0(sK3,sK4,X0)
% 2.16/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.16/1.02      | m1_subset_1(sK0(sK3,sK4,X0,X1),u1_struct_0(sK4)) ),
% 2.16/1.02      inference(renaming,[status(thm)],[c_811]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3212,plain,
% 2.16/1.02      ( r1_waybel_0(sK3,sK4,X0_56)
% 2.16/1.02      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 2.16/1.02      | m1_subset_1(sK0(sK3,sK4,X0_56,X0_52),u1_struct_0(sK4)) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_812]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3632,plain,
% 2.16/1.02      ( r1_waybel_0(sK3,sK4,X0_56) = iProver_top
% 2.16/1.02      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.16/1.02      | m1_subset_1(sK0(sK3,sK4,X0_56,X0_52),u1_struct_0(sK4)) = iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_3212]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_8,plain,
% 2.16/1.02      ( ~ l1_waybel_0(X0,X1)
% 2.16/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.02      | v2_struct_0(X1)
% 2.16/1.02      | v2_struct_0(X0)
% 2.16/1.02      | ~ l1_struct_0(X1)
% 2.16/1.02      | k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2) = k2_waybel_0(X1,X0,X2) ),
% 2.16/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1063,plain,
% 2.16/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.16/1.02      | v2_struct_0(X1)
% 2.16/1.02      | v2_struct_0(X2)
% 2.16/1.02      | ~ l1_struct_0(X2)
% 2.16/1.02      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),X0) = k2_waybel_0(X2,X1,X0)
% 2.16/1.02      | sK4 != X1
% 2.16/1.02      | sK3 != X2 ),
% 2.16/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1064,plain,
% 2.16/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.16/1.02      | v2_struct_0(sK4)
% 2.16/1.02      | v2_struct_0(sK3)
% 2.16/1.02      | ~ l1_struct_0(sK3)
% 2.16/1.02      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0) = k2_waybel_0(sK3,sK4,X0) ),
% 2.16/1.02      inference(unflattening,[status(thm)],[c_1063]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1068,plain,
% 2.16/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.16/1.02      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0) = k2_waybel_0(sK3,sK4,X0) ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_1064,c_20,c_19,c_18]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3200,plain,
% 2.16/1.02      ( ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 2.16/1.02      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0_52) = k2_waybel_0(sK3,sK4,X0_52) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_1068]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3644,plain,
% 2.16/1.02      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0_52) = k2_waybel_0(sK3,sK4,X0_52)
% 2.16/1.02      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_3200]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_4287,plain,
% 2.16/1.02      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),sK0(sK3,sK4,X0_56,X0_52)) = k2_waybel_0(sK3,sK4,sK0(sK3,sK4,X0_56,X0_52))
% 2.16/1.02      | r1_waybel_0(sK3,sK4,X0_56) = iProver_top
% 2.16/1.02      | m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top ),
% 2.16/1.02      inference(superposition,[status(thm)],[c_3632,c_3644]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_4544,plain,
% 2.16/1.02      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),sK0(sK3,sK4,X0_56,k4_yellow_6(sK4,sK2(sK4)))) = k2_waybel_0(sK3,sK4,sK0(sK3,sK4,X0_56,k4_yellow_6(sK4,sK2(sK4))))
% 2.16/1.02      | r1_waybel_0(sK3,sK4,X0_56) = iProver_top
% 2.16/1.02      | v2_struct_0(sK4) = iProver_top
% 2.16/1.02      | l1_struct_0(sK4) != iProver_top ),
% 2.16/1.02      inference(superposition,[status(thm)],[c_3637,c_4287]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_22,plain,
% 2.16/1.02      ( l1_struct_0(sK3) = iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_23,plain,
% 2.16/1.02      ( v2_struct_0(sK4) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_9,plain,
% 2.16/1.02      ( ~ l1_waybel_0(X0,X1) | l1_orders_2(X0) | ~ l1_struct_0(X1) ),
% 2.16/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2,plain,
% 2.16/1.02      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.16/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_242,plain,
% 2.16/1.02      ( ~ l1_waybel_0(X0,X1) | ~ l1_struct_0(X1) | l1_struct_0(X0) ),
% 2.16/1.02      inference(resolution,[status(thm)],[c_9,c_2]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1030,plain,
% 2.16/1.02      ( ~ l1_struct_0(X0) | l1_struct_0(X1) | sK4 != X1 | sK3 != X0 ),
% 2.16/1.02      inference(resolution_lifted,[status(thm)],[c_242,c_17]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1031,plain,
% 2.16/1.02      ( l1_struct_0(sK4) | ~ l1_struct_0(sK3) ),
% 2.16/1.02      inference(unflattening,[status(thm)],[c_1030]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1032,plain,
% 2.16/1.02      ( l1_struct_0(sK4) = iProver_top
% 2.16/1.02      | l1_struct_0(sK3) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1031]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_5015,plain,
% 2.16/1.02      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),sK0(sK3,sK4,X0_56,k4_yellow_6(sK4,sK2(sK4)))) = k2_waybel_0(sK3,sK4,sK0(sK3,sK4,X0_56,k4_yellow_6(sK4,sK2(sK4))))
% 2.16/1.02      | r1_waybel_0(sK3,sK4,X0_56) = iProver_top ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_4544,c_22,c_23,c_1032]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_16,negated_conjecture,
% 2.16/1.02      ( ~ r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) ),
% 2.16/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3220,negated_conjecture,
% 2.16/1.02      ( ~ r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_16]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3624,plain,
% 2.16/1.02      ( r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_3220]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_5023,plain,
% 2.16/1.02      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),sK0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),k4_yellow_6(sK4,sK2(sK4)))) = k2_waybel_0(sK3,sK4,sK0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),k4_yellow_6(sK4,sK2(sK4)))) ),
% 2.16/1.02      inference(superposition,[status(thm)],[c_5015,c_3624]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1,plain,
% 2.16/1.02      ( v2_struct_0(X0)
% 2.16/1.02      | ~ l1_struct_0(X0)
% 2.16/1.02      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.16/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1865,plain,
% 2.16/1.02      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK4 != X0 ),
% 2.16/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_18]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1866,plain,
% 2.16/1.02      ( ~ l1_struct_0(sK4) | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 2.16/1.02      inference(unflattening,[status(thm)],[c_1865]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1868,plain,
% 2.16/1.02      ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_1866,c_19,c_1031]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_0,plain,
% 2.16/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.16/1.02      | ~ m1_subset_1(X3,X1)
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.02      | r2_hidden(k3_funct_2(X1,X2,X0,X3),k2_relset_1(X1,X2,X0))
% 2.16/1.02      | v1_xboole_0(X1)
% 2.16/1.02      | v1_xboole_0(X2)
% 2.16/1.02      | ~ v1_funct_1(X0) ),
% 2.16/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_11,plain,
% 2.16/1.02      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 2.16/1.02      | ~ l1_waybel_0(X1,X0)
% 2.16/1.02      | ~ l1_struct_0(X0) ),
% 2.16/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_258,plain,
% 2.16/1.02      ( ~ l1_waybel_0(X0,X1)
% 2.16/1.02      | ~ m1_subset_1(X2,X3)
% 2.16/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
% 2.16/1.02      | r2_hidden(k3_funct_2(X3,X5,X4,X2),k2_relset_1(X3,X5,X4))
% 2.16/1.02      | ~ l1_struct_0(X1)
% 2.16/1.02      | v1_xboole_0(X3)
% 2.16/1.02      | v1_xboole_0(X5)
% 2.16/1.02      | ~ v1_funct_1(X4)
% 2.16/1.02      | u1_waybel_0(X1,X0) != X4
% 2.16/1.02      | u1_struct_0(X1) != X5
% 2.16/1.02      | u1_struct_0(X0) != X3 ),
% 2.16/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_259,plain,
% 2.16/1.02      ( ~ l1_waybel_0(X0,X1)
% 2.16/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.02      | ~ m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.16/1.02      | r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
% 2.16/1.02      | ~ l1_struct_0(X1)
% 2.16/1.02      | v1_xboole_0(u1_struct_0(X0))
% 2.16/1.02      | v1_xboole_0(u1_struct_0(X1))
% 2.16/1.02      | ~ v1_funct_1(u1_waybel_0(X1,X0)) ),
% 2.16/1.02      inference(unflattening,[status(thm)],[c_258]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_12,plain,
% 2.16/1.02      ( ~ l1_waybel_0(X0,X1)
% 2.16/1.02      | ~ l1_struct_0(X1)
% 2.16/1.02      | v1_funct_1(u1_waybel_0(X1,X0)) ),
% 2.16/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_10,plain,
% 2.16/1.02      ( ~ l1_waybel_0(X0,X1)
% 2.16/1.02      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.16/1.02      | ~ l1_struct_0(X1) ),
% 2.16/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_263,plain,
% 2.16/1.02      ( v1_xboole_0(u1_struct_0(X1))
% 2.16/1.02      | v1_xboole_0(u1_struct_0(X0))
% 2.16/1.02      | ~ l1_struct_0(X1)
% 2.16/1.02      | r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
% 2.16/1.02      | ~ l1_waybel_0(X0,X1)
% 2.16/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0)) ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_259,c_12,c_10]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_264,plain,
% 2.16/1.02      ( ~ l1_waybel_0(X0,X1)
% 2.16/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.16/1.02      | r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
% 2.16/1.02      | ~ l1_struct_0(X1)
% 2.16/1.02      | v1_xboole_0(u1_struct_0(X0))
% 2.16/1.02      | v1_xboole_0(u1_struct_0(X1)) ),
% 2.16/1.02      inference(renaming,[status(thm)],[c_263]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1009,plain,
% 2.16/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.16/1.02      | r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),X0),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1)))
% 2.16/1.02      | ~ l1_struct_0(X2)
% 2.16/1.02      | v1_xboole_0(u1_struct_0(X1))
% 2.16/1.02      | v1_xboole_0(u1_struct_0(X2))
% 2.16/1.02      | sK4 != X1
% 2.16/1.02      | sK3 != X2 ),
% 2.16/1.02      inference(resolution_lifted,[status(thm)],[c_264,c_17]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1010,plain,
% 2.16/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.16/1.02      | r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
% 2.16/1.02      | ~ l1_struct_0(sK3)
% 2.16/1.02      | v1_xboole_0(u1_struct_0(sK4))
% 2.16/1.02      | v1_xboole_0(u1_struct_0(sK3)) ),
% 2.16/1.02      inference(unflattening,[status(thm)],[c_1009]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_67,plain,
% 2.16/1.02      ( v2_struct_0(sK3)
% 2.16/1.02      | ~ l1_struct_0(sK3)
% 2.16/1.02      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.16/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1014,plain,
% 2.16/1.02      ( v1_xboole_0(u1_struct_0(sK4))
% 2.16/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.16/1.02      | r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_1010,c_20,c_19,c_67]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1015,plain,
% 2.16/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.16/1.02      | r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
% 2.16/1.02      | v1_xboole_0(u1_struct_0(sK4)) ),
% 2.16/1.02      inference(renaming,[status(thm)],[c_1014]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2104,plain,
% 2.16/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.16/1.02      | r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) ),
% 2.16/1.02      inference(backward_subsumption_resolution,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_1868,c_1015]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3197,plain,
% 2.16/1.02      ( ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 2.16/1.02      | r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0_52),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_2104]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3647,plain,
% 2.16/1.02      ( m1_subset_1(X0_52,u1_struct_0(sK4)) != iProver_top
% 2.16/1.02      | r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0_52),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) = iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_3197]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_5051,plain,
% 2.16/1.02      ( m1_subset_1(sK0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),k4_yellow_6(sK4,sK2(sK4))),u1_struct_0(sK4)) != iProver_top
% 2.16/1.02      | r2_hidden(k2_waybel_0(sK3,sK4,sK0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),k4_yellow_6(sK4,sK2(sK4)))),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) = iProver_top ),
% 2.16/1.02      inference(superposition,[status(thm)],[c_5023,c_3647]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3848,plain,
% 2.16/1.02      ( r1_waybel_0(sK3,sK4,X0_56)
% 2.16/1.02      | m1_subset_1(sK0(sK3,sK4,X0_56,k4_yellow_6(sK4,sK2(sK4))),u1_struct_0(sK4))
% 2.16/1.02      | ~ m1_subset_1(k4_yellow_6(sK4,sK2(sK4)),u1_struct_0(sK4)) ),
% 2.16/1.02      inference(instantiation,[status(thm)],[c_3212]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3991,plain,
% 2.16/1.02      ( r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
% 2.16/1.02      | m1_subset_1(sK0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),k4_yellow_6(sK4,sK2(sK4))),u1_struct_0(sK4))
% 2.16/1.02      | ~ m1_subset_1(k4_yellow_6(sK4,sK2(sK4)),u1_struct_0(sK4)) ),
% 2.16/1.02      inference(instantiation,[status(thm)],[c_3848]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3992,plain,
% 2.16/1.02      ( r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) = iProver_top
% 2.16/1.02      | m1_subset_1(sK0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),k4_yellow_6(sK4,sK2(sK4))),u1_struct_0(sK4)) = iProver_top
% 2.16/1.02      | m1_subset_1(k4_yellow_6(sK4,sK2(sK4)),u1_struct_0(sK4)) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_3991]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3,plain,
% 2.16/1.02      ( r1_waybel_0(X0,X1,X2)
% 2.16/1.02      | ~ l1_waybel_0(X1,X0)
% 2.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.16/1.02      | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
% 2.16/1.02      | v2_struct_0(X0)
% 2.16/1.02      | v2_struct_0(X1)
% 2.16/1.02      | ~ l1_struct_0(X0) ),
% 2.16/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_827,plain,
% 2.16/1.02      ( r1_waybel_0(X0,X1,X2)
% 2.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.16/1.02      | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
% 2.16/1.02      | v2_struct_0(X0)
% 2.16/1.02      | v2_struct_0(X1)
% 2.16/1.02      | ~ l1_struct_0(X0)
% 2.16/1.02      | sK4 != X1
% 2.16/1.02      | sK3 != X0 ),
% 2.16/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_17]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_828,plain,
% 2.16/1.02      ( r1_waybel_0(sK3,sK4,X0)
% 2.16/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.16/1.02      | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK0(sK3,sK4,X0,X1)),X0)
% 2.16/1.02      | v2_struct_0(sK4)
% 2.16/1.02      | v2_struct_0(sK3)
% 2.16/1.02      | ~ l1_struct_0(sK3) ),
% 2.16/1.02      inference(unflattening,[status(thm)],[c_827]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_832,plain,
% 2.16/1.02      ( ~ r2_hidden(k2_waybel_0(sK3,sK4,sK0(sK3,sK4,X0,X1)),X0)
% 2.16/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.16/1.02      | r1_waybel_0(sK3,sK4,X0) ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_828,c_20,c_19,c_18]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_833,plain,
% 2.16/1.02      ( r1_waybel_0(sK3,sK4,X0)
% 2.16/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.16/1.02      | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK0(sK3,sK4,X0,X1)),X0) ),
% 2.16/1.02      inference(renaming,[status(thm)],[c_832]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3211,plain,
% 2.16/1.02      ( r1_waybel_0(sK3,sK4,X0_56)
% 2.16/1.02      | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
% 2.16/1.02      | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK0(sK3,sK4,X0_56,X0_52)),X0_56) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_833]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3846,plain,
% 2.16/1.02      ( r1_waybel_0(sK3,sK4,X0_56)
% 2.16/1.02      | ~ m1_subset_1(k4_yellow_6(sK4,sK2(sK4)),u1_struct_0(sK4))
% 2.16/1.02      | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK0(sK3,sK4,X0_56,k4_yellow_6(sK4,sK2(sK4)))),X0_56) ),
% 2.16/1.02      inference(instantiation,[status(thm)],[c_3211]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3952,plain,
% 2.16/1.02      ( r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
% 2.16/1.02      | ~ m1_subset_1(k4_yellow_6(sK4,sK2(sK4)),u1_struct_0(sK4))
% 2.16/1.02      | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),k4_yellow_6(sK4,sK2(sK4)))),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) ),
% 2.16/1.02      inference(instantiation,[status(thm)],[c_3846]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3953,plain,
% 2.16/1.02      ( r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) = iProver_top
% 2.16/1.02      | m1_subset_1(k4_yellow_6(sK4,sK2(sK4)),u1_struct_0(sK4)) != iProver_top
% 2.16/1.02      | r2_hidden(k2_waybel_0(sK3,sK4,sK0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),k4_yellow_6(sK4,sK2(sK4)))),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_3952]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1773,plain,
% 2.16/1.02      ( m1_subset_1(k4_yellow_6(X0,sK2(X0)),u1_struct_0(X0))
% 2.16/1.02      | ~ l1_struct_0(X0)
% 2.16/1.02      | sK4 != X0 ),
% 2.16/1.02      inference(resolution_lifted,[status(thm)],[c_930,c_18]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1774,plain,
% 2.16/1.02      ( m1_subset_1(k4_yellow_6(sK4,sK2(sK4)),u1_struct_0(sK4))
% 2.16/1.02      | ~ l1_struct_0(sK4) ),
% 2.16/1.02      inference(unflattening,[status(thm)],[c_1773]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1775,plain,
% 2.16/1.02      ( m1_subset_1(k4_yellow_6(sK4,sK2(sK4)),u1_struct_0(sK4)) = iProver_top
% 2.16/1.02      | l1_struct_0(sK4) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1774]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_25,plain,
% 2.16/1.02      ( r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(contradiction,plain,
% 2.16/1.02      ( $false ),
% 2.16/1.02      inference(minisat,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_5051,c_3992,c_3953,c_1775,c_1032,c_25,c_22]) ).
% 2.16/1.02  
% 2.16/1.02  
% 2.16/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.16/1.02  
% 2.16/1.02  ------                               Statistics
% 2.16/1.02  
% 2.16/1.02  ------ General
% 2.16/1.02  
% 2.16/1.02  abstr_ref_over_cycles:                  0
% 2.16/1.02  abstr_ref_under_cycles:                 0
% 2.16/1.02  gc_basic_clause_elim:                   0
% 2.16/1.02  forced_gc_time:                         0
% 2.16/1.02  parsing_time:                           0.01
% 2.16/1.02  unif_index_cands_time:                  0.
% 2.16/1.02  unif_index_add_time:                    0.
% 2.16/1.02  orderings_time:                         0.
% 2.16/1.02  out_proof_time:                         0.011
% 2.16/1.02  total_time:                             0.172
% 2.16/1.02  num_of_symbols:                         58
% 2.16/1.02  num_of_terms:                           4969
% 2.16/1.02  
% 2.16/1.02  ------ Preprocessing
% 2.16/1.02  
% 2.16/1.02  num_of_splits:                          0
% 2.16/1.02  num_of_split_atoms:                     0
% 2.16/1.02  num_of_reused_defs:                     0
% 2.16/1.02  num_eq_ax_congr_red:                    53
% 2.16/1.02  num_of_sem_filtered_clauses:            4
% 2.16/1.02  num_of_subtypes:                        6
% 2.16/1.02  monotx_restored_types:                  0
% 2.16/1.02  sat_num_of_epr_types:                   0
% 2.16/1.02  sat_num_of_non_cyclic_types:            0
% 2.16/1.02  sat_guarded_non_collapsed_types:        0
% 2.16/1.02  num_pure_diseq_elim:                    0
% 2.16/1.02  simp_replaced_by:                       0
% 2.16/1.02  res_preprocessed:                       77
% 2.16/1.02  prep_upred:                             0
% 2.16/1.02  prep_unflattend:                        156
% 2.16/1.02  smt_new_axioms:                         0
% 2.16/1.02  pred_elim_cands:                        11
% 2.16/1.02  pred_elim:                              4
% 2.16/1.02  pred_elim_cl:                           -5
% 2.16/1.02  pred_elim_cycles:                       13
% 2.16/1.02  merged_defs:                            0
% 2.16/1.02  merged_defs_ncl:                        0
% 2.16/1.02  bin_hyper_res:                          0
% 2.16/1.02  prep_cycles:                            3
% 2.16/1.02  pred_elim_time:                         0.078
% 2.16/1.02  splitting_time:                         0.
% 2.16/1.02  sem_filter_time:                        0.
% 2.16/1.02  monotx_time:                            0.
% 2.16/1.02  subtype_inf_time:                       0.
% 2.16/1.02  
% 2.16/1.02  ------ Problem properties
% 2.16/1.02  
% 2.16/1.02  clauses:                                26
% 2.16/1.02  conjectures:                            4
% 2.16/1.02  epr:                                    4
% 2.16/1.02  horn:                                   16
% 2.16/1.02  ground:                                 7
% 2.16/1.02  unary:                                  7
% 2.16/1.02  binary:                                 6
% 2.16/1.02  lits:                                   71
% 2.16/1.02  lits_eq:                                2
% 2.16/1.02  fd_pure:                                0
% 2.16/1.02  fd_pseudo:                              0
% 2.16/1.02  fd_cond:                                0
% 2.16/1.02  fd_pseudo_cond:                         0
% 2.16/1.02  ac_symbols:                             0
% 2.16/1.02  
% 2.16/1.02  ------ Propositional Solver
% 2.16/1.02  
% 2.16/1.02  prop_solver_calls:                      25
% 2.16/1.02  prop_fast_solver_calls:                 1398
% 2.16/1.02  smt_solver_calls:                       0
% 2.16/1.02  smt_fast_solver_calls:                  0
% 2.16/1.02  prop_num_of_clauses:                    1396
% 2.16/1.02  prop_preprocess_simplified:             3619
% 2.16/1.02  prop_fo_subsumed:                       109
% 2.16/1.02  prop_solver_time:                       0.
% 2.16/1.02  smt_solver_time:                        0.
% 2.16/1.02  smt_fast_solver_time:                   0.
% 2.16/1.02  prop_fast_solver_time:                  0.
% 2.16/1.02  prop_unsat_core_time:                   0.
% 2.16/1.02  
% 2.16/1.02  ------ QBF
% 2.16/1.02  
% 2.16/1.02  qbf_q_res:                              0
% 2.16/1.02  qbf_num_tautologies:                    0
% 2.16/1.02  qbf_prep_cycles:                        0
% 2.16/1.02  
% 2.16/1.02  ------ BMC1
% 2.16/1.02  
% 2.16/1.02  bmc1_current_bound:                     -1
% 2.16/1.02  bmc1_last_solved_bound:                 -1
% 2.16/1.02  bmc1_unsat_core_size:                   -1
% 2.16/1.02  bmc1_unsat_core_parents_size:           -1
% 2.16/1.02  bmc1_merge_next_fun:                    0
% 2.16/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.16/1.02  
% 2.16/1.02  ------ Instantiation
% 2.16/1.02  
% 2.16/1.02  inst_num_of_clauses:                    190
% 2.16/1.02  inst_num_in_passive:                    14
% 2.16/1.02  inst_num_in_active:                     152
% 2.16/1.02  inst_num_in_unprocessed:                24
% 2.16/1.02  inst_num_of_loops:                      190
% 2.16/1.02  inst_num_of_learning_restarts:          0
% 2.16/1.02  inst_num_moves_active_passive:          32
% 2.16/1.02  inst_lit_activity:                      0
% 2.16/1.02  inst_lit_activity_moves:                0
% 2.16/1.02  inst_num_tautologies:                   0
% 2.16/1.02  inst_num_prop_implied:                  0
% 2.16/1.02  inst_num_existing_simplified:           0
% 2.16/1.02  inst_num_eq_res_simplified:             0
% 2.16/1.02  inst_num_child_elim:                    0
% 2.16/1.02  inst_num_of_dismatching_blockings:      17
% 2.16/1.02  inst_num_of_non_proper_insts:           111
% 2.16/1.02  inst_num_of_duplicates:                 0
% 2.16/1.02  inst_inst_num_from_inst_to_res:         0
% 2.16/1.02  inst_dismatching_checking_time:         0.
% 2.16/1.02  
% 2.16/1.02  ------ Resolution
% 2.16/1.02  
% 2.16/1.02  res_num_of_clauses:                     0
% 2.16/1.02  res_num_in_passive:                     0
% 2.16/1.02  res_num_in_active:                      0
% 2.16/1.02  res_num_of_loops:                       80
% 2.16/1.02  res_forward_subset_subsumed:            7
% 2.16/1.02  res_backward_subset_subsumed:           4
% 2.16/1.02  res_forward_subsumed:                   0
% 2.16/1.02  res_backward_subsumed:                  0
% 2.16/1.02  res_forward_subsumption_resolution:     2
% 2.16/1.02  res_backward_subsumption_resolution:    2
% 2.16/1.02  res_clause_to_clause_subsumption:       201
% 2.16/1.02  res_orphan_elimination:                 0
% 2.16/1.02  res_tautology_del:                      29
% 2.16/1.02  res_num_eq_res_simplified:              0
% 2.16/1.02  res_num_sel_changes:                    0
% 2.16/1.02  res_moves_from_active_to_pass:          0
% 2.16/1.02  
% 2.16/1.02  ------ Superposition
% 2.16/1.02  
% 2.16/1.02  sup_time_total:                         0.
% 2.16/1.02  sup_time_generating:                    0.
% 2.16/1.02  sup_time_sim_full:                      0.
% 2.16/1.02  sup_time_sim_immed:                     0.
% 2.16/1.02  
% 2.16/1.02  sup_num_of_clauses:                     57
% 2.16/1.02  sup_num_in_active:                      38
% 2.16/1.02  sup_num_in_passive:                     19
% 2.16/1.02  sup_num_of_loops:                       37
% 2.16/1.02  sup_fw_superposition:                   19
% 2.16/1.02  sup_bw_superposition:                   12
% 2.16/1.02  sup_immediate_simplified:               0
% 2.16/1.02  sup_given_eliminated:                   0
% 2.16/1.02  comparisons_done:                       0
% 2.16/1.02  comparisons_avoided:                    0
% 2.16/1.02  
% 2.16/1.02  ------ Simplifications
% 2.16/1.02  
% 2.16/1.02  
% 2.16/1.02  sim_fw_subset_subsumed:                 0
% 2.16/1.02  sim_bw_subset_subsumed:                 0
% 2.16/1.02  sim_fw_subsumed:                        0
% 2.16/1.02  sim_bw_subsumed:                        0
% 2.16/1.02  sim_fw_subsumption_res:                 0
% 2.16/1.02  sim_bw_subsumption_res:                 0
% 2.16/1.02  sim_tautology_del:                      1
% 2.16/1.02  sim_eq_tautology_del:                   0
% 2.16/1.02  sim_eq_res_simp:                        0
% 2.16/1.02  sim_fw_demodulated:                     0
% 2.16/1.02  sim_bw_demodulated:                     0
% 2.16/1.02  sim_light_normalised:                   0
% 2.16/1.02  sim_joinable_taut:                      0
% 2.16/1.02  sim_joinable_simp:                      0
% 2.16/1.02  sim_ac_normalised:                      0
% 2.16/1.02  sim_smt_subsumption:                    0
% 2.16/1.02  
%------------------------------------------------------------------------------
