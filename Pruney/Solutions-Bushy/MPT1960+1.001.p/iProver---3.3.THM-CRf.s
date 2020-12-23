%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1960+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:56 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 719 expanded)
%              Number of clauses        :   92 ( 246 expanded)
%              Number of leaves         :   24 ( 153 expanded)
%              Depth                    :   26
%              Number of atoms          :  584 (2124 expanded)
%              Number of equality atoms :  193 ( 532 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => k6_subset_1(X0,X1) = k7_waybel_1(k3_yellow_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
       => k6_subset_1(X0,X1) = k7_waybel_1(k3_yellow_1(X0),X1) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f44,plain,(
    ? [X0,X1] :
      ( k6_subset_1(X0,X1) != k7_waybel_1(k3_yellow_1(X0),X1)
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f49,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(X0,X1) != k7_waybel_1(k3_yellow_1(X0),X1)
        & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) )
   => ( k6_subset_1(sK0,sK1) != k7_waybel_1(k3_yellow_1(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( k6_subset_1(sK0,sK1) != k7_waybel_1(k3_yellow_1(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f49])).

fof(f84,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,axiom,(
    ! [X0] : u1_struct_0(k3_yellow_1(X0)) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : u1_struct_0(k3_yellow_1(X0)) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f86,plain,(
    ! [X0] : u1_struct_0(k3_yellow_1(X0)) = k1_zfmisc_1(X0) ),
    inference(definition_unfolding,[],[f72,f82])).

fof(f87,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),u1_struct_0(k3_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f63,f71,f86])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v10_waybel_1(X0)
          & v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f28,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f29,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f28])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f56,plain,(
    ! [X0] :
      ( v2_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f65,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( v11_waybel_1(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f64,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f62,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
            & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
            & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) )
          | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r6_waybel_1(X0,X1,X2)
              <=> ( k11_lattice3(X0,X1,X2) = k3_yellow_0(X0)
                  & k10_lattice3(X0,X1,X2) = k4_yellow_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r6_waybel_1(X0,X1,X2)
              <=> ( k11_lattice3(X0,X1,X2) = k3_yellow_0(X0)
                  & k10_lattice3(X0,X1,X2) = k4_yellow_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r6_waybel_1(X0,X1,X2)
              <=> ( k11_lattice3(X0,X1,X2) = k3_yellow_0(X0)
                  & k10_lattice3(X0,X1,X2) = k4_yellow_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r6_waybel_1(X0,X1,X2)
                  | k11_lattice3(X0,X1,X2) != k3_yellow_0(X0)
                  | k10_lattice3(X0,X1,X2) != k4_yellow_0(X0) )
                & ( ( k11_lattice3(X0,X1,X2) = k3_yellow_0(X0)
                    & k10_lattice3(X0,X1,X2) = k4_yellow_0(X0) )
                  | ~ r6_waybel_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r6_waybel_1(X0,X1,X2)
                  | k11_lattice3(X0,X1,X2) != k3_yellow_0(X0)
                  | k10_lattice3(X0,X1,X2) != k4_yellow_0(X0) )
                & ( ( k11_lattice3(X0,X1,X2) = k3_yellow_0(X0)
                    & k10_lattice3(X0,X1,X2) = k4_yellow_0(X0) )
                  | ~ r6_waybel_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r6_waybel_1(X0,X1,X2)
      | k11_lattice3(X0,X1,X2) != k3_yellow_0(X0)
      | k10_lattice3(X0,X1,X2) != k4_yellow_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f15,axiom,(
    ! [X0] : k3_yellow_0(k3_yellow_1(X0)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k3_yellow_0(k3_yellow_1(X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ! [X0] :
      ( v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f17])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) ) ),
    inference(definition_unfolding,[],[f80,f86])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v11_waybel_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r6_waybel_1(X0,X1,X2)
              <=> k7_waybel_1(X0,X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r6_waybel_1(X0,X1,X2)
              <=> k7_waybel_1(X0,X1) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r6_waybel_1(X0,X1,X2)
              <=> k7_waybel_1(X0,X1) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r6_waybel_1(X0,X1,X2)
                  | k7_waybel_1(X0,X1) != X2 )
                & ( k7_waybel_1(X0,X1) = X2
                  | ~ r6_waybel_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k7_waybel_1(X0,X1) = X2
      | ~ r6_waybel_1(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f66,plain,(
    ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    k6_subset_1(sK0,sK1) != k7_waybel_1(k3_yellow_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f89,plain,(
    k4_xboole_0(sK0,sK1) != k7_waybel_1(k3_yellow_1(sK0),sK1) ),
    inference(definition_unfolding,[],[f85,f71])).

cnf(c_29,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1464,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_20,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1467,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1768,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_1467])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1469,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1838,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1768,c_1469])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1463,plain,
    ( m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_12,plain,
    ( m1_subset_1(k4_xboole_0(X0,X1),u1_struct_0(k3_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1468,plain,
    ( m1_subset_1(k4_xboole_0(X0,X1),u1_struct_0(k3_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v11_waybel_1(X0)
    | v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_17,plain,
    ( ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_511,plain,
    ( ~ l1_orders_2(X0)
    | ~ v11_waybel_1(X0)
    | v2_lattice3(X0)
    | k3_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_512,plain,
    ( ~ l1_orders_2(k3_yellow_1(X0))
    | ~ v11_waybel_1(k3_yellow_1(X0))
    | v2_lattice3(k3_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_13,plain,
    ( v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_11,plain,
    ( l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_516,plain,
    ( v2_lattice3(k3_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_13,c_11])).

cnf(c_600,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,X2,X0) = k11_lattice3(X1,X2,X0)
    | k3_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_516])).

cnf(c_601,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | ~ v5_orders_2(k3_yellow_1(X1))
    | ~ l1_orders_2(k3_yellow_1(X1))
    | k12_lattice3(k3_yellow_1(X1),X0,X2) = k11_lattice3(k3_yellow_1(X1),X0,X2) ),
    inference(unflattening,[status(thm)],[c_600])).

cnf(c_14,plain,
    ( v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_615,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | k12_lattice3(k3_yellow_1(X1),X0,X2) = k11_lattice3(k3_yellow_1(X1),X0,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_601,c_11,c_14])).

cnf(c_1456,plain,
    ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k11_lattice3(k3_yellow_1(X0),X1,X2)
    | m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_2327,plain,
    ( k12_lattice3(k3_yellow_1(X0),X1,k4_xboole_0(X0,X2)) = k11_lattice3(k3_yellow_1(X0),X1,k4_xboole_0(X0,X2))
    | m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1456])).

cnf(c_3838,plain,
    ( k12_lattice3(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,X0)) = k11_lattice3(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_1463,c_2327])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | k12_lattice3(k3_yellow_1(X1),X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1466,plain,
    ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2048,plain,
    ( k12_lattice3(k3_yellow_1(X0),X1,k4_xboole_0(X0,X2)) = k3_xboole_0(X1,k4_xboole_0(X0,X2))
    | m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1466])).

cnf(c_3221,plain,
    ( k12_lattice3(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,X0)) = k3_xboole_0(sK1,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_1463,c_2048])).

cnf(c_3840,plain,
    ( k11_lattice3(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,X0)) = k3_xboole_0(sK1,k4_xboole_0(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_3838,c_3221])).

cnf(c_6,plain,
    ( r6_waybel_1(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k10_lattice3(X0,X1,X2) != k4_yellow_0(X0)
    | k11_lattice3(X0,X1,X2) != k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_463,plain,
    ( r6_waybel_1(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k10_lattice3(X0,X1,X2) != k4_yellow_0(X0)
    | k11_lattice3(X0,X1,X2) != k3_yellow_0(X0)
    | k3_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_464,plain,
    ( r6_waybel_1(k3_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
    | ~ l1_orders_2(k3_yellow_1(X0))
    | k10_lattice3(k3_yellow_1(X0),X1,X2) != k4_yellow_0(k3_yellow_1(X0))
    | k11_lattice3(k3_yellow_1(X0),X1,X2) != k3_yellow_0(k3_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_468,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
    | r6_waybel_1(k3_yellow_1(X0),X1,X2)
    | k10_lattice3(k3_yellow_1(X0),X1,X2) != k4_yellow_0(k3_yellow_1(X0))
    | k11_lattice3(k3_yellow_1(X0),X1,X2) != k3_yellow_0(k3_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_464,c_11])).

cnf(c_469,plain,
    ( r6_waybel_1(k3_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
    | k10_lattice3(k3_yellow_1(X0),X1,X2) != k4_yellow_0(k3_yellow_1(X0))
    | k11_lattice3(k3_yellow_1(X0),X1,X2) != k3_yellow_0(k3_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_468])).

cnf(c_1459,plain,
    ( k10_lattice3(k3_yellow_1(X0),X1,X2) != k4_yellow_0(k3_yellow_1(X0))
    | k11_lattice3(k3_yellow_1(X0),X1,X2) != k3_yellow_0(k3_yellow_1(X0))
    | r6_waybel_1(k3_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(c_25,plain,
    ( k3_yellow_0(k3_yellow_1(X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_26,plain,
    ( k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1555,plain,
    ( k10_lattice3(k3_yellow_1(X0),X1,X2) != X0
    | k11_lattice3(k3_yellow_1(X0),X1,X2) != k1_xboole_0
    | r6_waybel_1(k3_yellow_1(X0),X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1459,c_25,c_26])).

cnf(c_3848,plain,
    ( k10_lattice3(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,X0)) != sK0
    | k3_xboole_0(sK1,k4_xboole_0(sK0,X0)) != k1_xboole_0
    | r6_waybel_1(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,X0)) = iProver_top
    | m1_subset_1(k4_xboole_0(sK0,X0),u1_struct_0(k3_yellow_1(sK0))) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3840,c_1555])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | k13_lattice3(X1,X2,X0) = k10_lattice3(X1,X2,X0)
    | k3_yellow_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | ~ v5_orders_2(k3_yellow_1(X1))
    | ~ v1_lattice3(k3_yellow_1(X1))
    | k13_lattice3(k3_yellow_1(X1),X0,X2) = k10_lattice3(k3_yellow_1(X1),X0,X2) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_1,plain,
    ( v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v11_waybel_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_496,plain,
    ( v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v11_waybel_1(X0)
    | k3_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_17])).

cnf(c_497,plain,
    ( v1_lattice3(k3_yellow_1(X0))
    | ~ l1_orders_2(k3_yellow_1(X0))
    | ~ v11_waybel_1(k3_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_501,plain,
    ( v1_lattice3(k3_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_13,c_11])).

cnf(c_641,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | k13_lattice3(k3_yellow_1(X1),X0,X2) = k10_lattice3(k3_yellow_1(X1),X0,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_627,c_501,c_14])).

cnf(c_1455,plain,
    ( k13_lattice3(k3_yellow_1(X0),X1,X2) = k10_lattice3(k3_yellow_1(X0),X1,X2)
    | m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_1818,plain,
    ( k13_lattice3(k3_yellow_1(X0),X1,k4_xboole_0(X0,X2)) = k10_lattice3(k3_yellow_1(X0),X1,k4_xboole_0(X0,X2))
    | m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1455])).

cnf(c_3506,plain,
    ( k13_lattice3(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,X0)) = k10_lattice3(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_1463,c_1818])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | k13_lattice3(k3_yellow_1(X1),X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1465,plain,
    ( k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1908,plain,
    ( k13_lattice3(k3_yellow_1(X0),X1,k4_xboole_0(X0,X2)) = k2_xboole_0(X1,k4_xboole_0(X0,X2))
    | m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1465])).

cnf(c_3120,plain,
    ( k13_lattice3(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,X0)) = k2_xboole_0(sK1,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_1463,c_1908])).

cnf(c_3508,plain,
    ( k10_lattice3(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,X0)) = k2_xboole_0(sK1,k4_xboole_0(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_3506,c_3120])).

cnf(c_3849,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK0,X0)) != sK0
    | k3_xboole_0(sK1,k4_xboole_0(sK0,X0)) != k1_xboole_0
    | r6_waybel_1(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,X0)) = iProver_top
    | m1_subset_1(k4_xboole_0(sK0,X0),u1_struct_0(k3_yellow_1(sK0))) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3848,c_3508])).

cnf(c_32,plain,
    ( m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1753,plain,
    ( m1_subset_1(k4_xboole_0(sK0,X0),u1_struct_0(k3_yellow_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1758,plain,
    ( m1_subset_1(k4_xboole_0(sK0,X0),u1_struct_0(k3_yellow_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1753])).

cnf(c_3926,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK0,X0)) != sK0
    | k3_xboole_0(sK1,k4_xboole_0(sK0,X0)) != k1_xboole_0
    | r6_waybel_1(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3849,c_32,c_1758])).

cnf(c_3935,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) != sK0
    | r6_waybel_1(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_3926])).

cnf(c_27,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_28,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_401,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(resolution,[status(thm)],[c_27,c_28])).

cnf(c_1462,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
    | m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_2885,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_1463,c_1462])).

cnf(c_3936,plain,
    ( sK0 != sK0
    | r6_waybel_1(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3935,c_2885])).

cnf(c_3937,plain,
    ( r6_waybel_1(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,sK1)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3936])).

cnf(c_22,plain,
    ( ~ r6_waybel_1(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v11_waybel_1(X0)
    | ~ v2_lattice3(X0)
    | k7_waybel_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_546,plain,
    ( ~ r6_waybel_1(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | k7_waybel_1(X0,X1) = X2
    | k3_yellow_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_13])).

cnf(c_547,plain,
    ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
    | ~ v3_orders_2(k3_yellow_1(X0))
    | ~ v4_orders_2(k3_yellow_1(X0))
    | ~ v5_orders_2(k3_yellow_1(X0))
    | ~ v1_lattice3(k3_yellow_1(X0))
    | ~ l1_orders_2(k3_yellow_1(X0))
    | ~ v2_lattice3(k3_yellow_1(X0))
    | k7_waybel_1(k3_yellow_1(X0),X1) = X2 ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_16,plain,
    ( v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_15,plain,
    ( v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_551,plain,
    ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
    | k7_waybel_1(k3_yellow_1(X0),X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_547,c_16,c_15,c_14,c_13,c_11,c_497,c_512])).

cnf(c_552,plain,
    ( ~ r6_waybel_1(k3_yellow_1(X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
    | k7_waybel_1(k3_yellow_1(X0),X1) = X2 ),
    inference(renaming,[status(thm)],[c_551])).

cnf(c_1458,plain,
    ( k7_waybel_1(k3_yellow_1(X0),X1) = X2
    | r6_waybel_1(k3_yellow_1(X0),X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_4070,plain,
    ( k7_waybel_1(k3_yellow_1(sK0),sK1) = k4_xboole_0(sK0,sK1)
    | m1_subset_1(k4_xboole_0(sK0,sK1),u1_struct_0(k3_yellow_1(sK0))) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3937,c_1458])).

cnf(c_30,negated_conjecture,
    ( k4_xboole_0(sK0,sK1) != k7_waybel_1(k3_yellow_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1032,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1624,plain,
    ( k7_waybel_1(k3_yellow_1(sK0),sK1) != X0
    | k4_xboole_0(sK0,sK1) != X0
    | k4_xboole_0(sK0,sK1) = k7_waybel_1(k3_yellow_1(sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_1745,plain,
    ( k7_waybel_1(k3_yellow_1(sK0),sK1) != k4_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) = k7_waybel_1(k3_yellow_1(sK0),sK1)
    | k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1624])).

cnf(c_1031,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1746,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_1676,plain,
    ( ~ r6_waybel_1(k3_yellow_1(X0),X1,k4_xboole_0(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
    | ~ m1_subset_1(k4_xboole_0(X0,X2),u1_struct_0(k3_yellow_1(X0)))
    | k7_waybel_1(k3_yellow_1(X0),X1) = k4_xboole_0(X0,X2) ),
    inference(instantiation,[status(thm)],[c_552])).

cnf(c_2027,plain,
    ( ~ r6_waybel_1(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,X0))
    | ~ m1_subset_1(k4_xboole_0(sK0,X0),u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))
    | k7_waybel_1(k3_yellow_1(sK0),sK1) = k4_xboole_0(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_1676])).

cnf(c_2143,plain,
    ( ~ r6_waybel_1(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_xboole_0(sK0,sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))
    | k7_waybel_1(k3_yellow_1(sK0),sK1) = k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_2027])).

cnf(c_2144,plain,
    ( k7_waybel_1(k3_yellow_1(sK0),sK1) = k4_xboole_0(sK0,sK1)
    | r6_waybel_1(k3_yellow_1(sK0),sK1,k4_xboole_0(sK0,sK1)) != iProver_top
    | m1_subset_1(k4_xboole_0(sK0,sK1),u1_struct_0(k3_yellow_1(sK0))) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2143])).

cnf(c_4089,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),u1_struct_0(k3_yellow_1(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4070,c_32,c_30,c_1745,c_1746,c_2144,c_3937])).

cnf(c_4094,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4089,c_1468])).


%------------------------------------------------------------------------------
