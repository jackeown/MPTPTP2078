%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1652+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:05 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 493 expanded)
%              Number of clauses        :   66 ( 115 expanded)
%              Number of leaves         :    6 ( 109 expanded)
%              Depth                    :   16
%              Number of atoms          :  464 (3545 expanded)
%              Number of equality atoms :   81 (  81 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_lattice3(X0,X1,X2)
              <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattice3(X0,X1,X2)
              <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattice3(X0,X1,X2)
              <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattice3(X0,X1,X2)
                  | ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2) )
                & ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                  | ~ r2_lattice3(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r1_yellow_0(X0,X1)
          <=> r1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r1_yellow_0(X0,X1)
            <=> r1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r1_yellow_0(X0,X1)
          <~> r1_yellow_0(X0,k3_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r1_yellow_0(X0,X1)
          <~> r1_yellow_0(X0,k3_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_yellow_0(X0,k3_waybel_0(X0,X1))
            | ~ r1_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,k3_waybel_0(X0,X1))
            | r1_yellow_0(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_yellow_0(X0,k3_waybel_0(X0,X1))
            | ~ r1_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,k3_waybel_0(X0,X1))
            | r1_yellow_0(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_yellow_0(X0,k3_waybel_0(X0,X1))
            | ~ r1_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,k3_waybel_0(X0,X1))
            | r1_yellow_0(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r1_yellow_0(X0,k3_waybel_0(X0,sK2))
          | ~ r1_yellow_0(X0,sK2) )
        & ( r1_yellow_0(X0,k3_waybel_0(X0,sK2))
          | r1_yellow_0(X0,sK2) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_yellow_0(X0,k3_waybel_0(X0,X1))
              | ~ r1_yellow_0(X0,X1) )
            & ( r1_yellow_0(X0,k3_waybel_0(X0,X1))
              | r1_yellow_0(X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ r1_yellow_0(sK1,k3_waybel_0(sK1,X1))
            | ~ r1_yellow_0(sK1,X1) )
          & ( r1_yellow_0(sK1,k3_waybel_0(sK1,X1))
            | r1_yellow_0(sK1,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ( ~ r1_yellow_0(sK1,k3_waybel_0(sK1,sK2))
      | ~ r1_yellow_0(sK1,sK2) )
    & ( r1_yellow_0(sK1,k3_waybel_0(sK1,sK2))
      | r1_yellow_0(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f17,f19,f18])).

fof(f28,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f26,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f27,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) ) )
         => r1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK0(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK0(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK0(X0,X1,X2))
          | r2_lattice3(X0,X1,sK0(X0,X1,X2)) )
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ( ( ~ r2_lattice3(X0,X2,sK0(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK0(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK0(X0,X1,X2))
              | r2_lattice3(X0,X1,sK0(X0,X1,X2)) )
            & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X2,sK0(X0,X1,X2))
      | r2_lattice3(X0,X1,sK0(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X2,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK0(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,
    ( ~ r1_yellow_0(sK1,k3_waybel_0(sK1,sK2))
    | ~ r1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,
    ( r1_yellow_0(sK1,k3_waybel_0(sK1,sK2))
    | r1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_9,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_148,plain,
    ( ~ r2_lattice3(sK1,X0,X1)
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[status(thm)],[c_1,c_9])).

cnf(c_11,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_10,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_8,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_152,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0),X1)
    | ~ r2_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_148,c_11,c_10,c_8])).

cnf(c_153,plain,
    ( ~ r2_lattice3(sK1,X0,X1)
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_152])).

cnf(c_352,plain,
    ( ~ r2_lattice3(sK1,X0_42,X1_42)
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0_42),X1_42)
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_153])).

cnf(c_434,plain,
    ( ~ r2_lattice3(sK1,X0_42,sK0(sK1,X1_42,k3_waybel_0(sK1,sK2)))
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0_42),sK0(sK1,X1_42,k3_waybel_0(sK1,sK2)))
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(sK1,X1_42,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_440,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,X1_42,k3_waybel_0(sK1,sK2))) != iProver_top
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0_42),sK0(sK1,X1_42,k3_waybel_0(sK1,sK2))) = iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,X1_42,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_442,plain,
    ( r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) = iProver_top
    | r2_lattice3(sK1,sK2,sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_0,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_171,plain,
    ( r2_lattice3(sK1,X0,X1)
    | ~ r2_lattice3(sK1,k3_waybel_0(sK1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[status(thm)],[c_0,c_9])).

cnf(c_175,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_lattice3(sK1,k3_waybel_0(sK1,X0),X1)
    | r2_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_171,c_11,c_10,c_8])).

cnf(c_176,plain,
    ( r2_lattice3(sK1,X0,X1)
    | ~ r2_lattice3(sK1,k3_waybel_0(sK1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_351,plain,
    ( r2_lattice3(sK1,X0_42,X1_42)
    | ~ r2_lattice3(sK1,k3_waybel_0(sK1,X0_42),X1_42)
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_176])).

cnf(c_435,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,X1_42,k3_waybel_0(sK1,sK2)))
    | ~ r2_lattice3(sK1,k3_waybel_0(sK1,X0_42),sK0(sK1,X1_42,k3_waybel_0(sK1,sK2)))
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(sK1,X1_42,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_436,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,X1_42,k3_waybel_0(sK1,sK2))) = iProver_top
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0_42),sK0(sK1,X1_42,k3_waybel_0(sK1,sK2))) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,X1_42,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_438,plain,
    ( r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) != iProver_top
    | r2_lattice3(sK1,sK2,sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_3,plain,
    ( r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | r2_lattice3(X0,X2,sK0(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | r1_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_220,plain,
    ( r2_lattice3(sK1,X0,sK0(sK1,X1,X0))
    | r2_lattice3(sK1,X1,sK0(sK1,X1,X0))
    | ~ r1_yellow_0(sK1,X1)
    | r1_yellow_0(sK1,X0)
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_3,c_8])).

cnf(c_222,plain,
    ( r1_yellow_0(sK1,X0)
    | ~ r1_yellow_0(sK1,X1)
    | r2_lattice3(sK1,X1,sK0(sK1,X1,X0))
    | r2_lattice3(sK1,X0,sK0(sK1,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_220,c_11])).

cnf(c_223,plain,
    ( r2_lattice3(sK1,X0,sK0(sK1,X1,X0))
    | r2_lattice3(sK1,X1,sK0(sK1,X1,X0))
    | ~ r1_yellow_0(sK1,X1)
    | r1_yellow_0(sK1,X0) ),
    inference(renaming,[status(thm)],[c_222])).

cnf(c_349,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,X1_42,X0_42))
    | r2_lattice3(sK1,X1_42,sK0(sK1,X1_42,X0_42))
    | ~ r1_yellow_0(sK1,X1_42)
    | r1_yellow_0(sK1,X0_42) ),
    inference(subtyping,[status(esa)],[c_223])).

cnf(c_429,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,X0_42,k3_waybel_0(sK1,sK2)))
    | r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,X0_42,k3_waybel_0(sK1,sK2)))
    | ~ r1_yellow_0(sK1,X0_42)
    | r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_430,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,X0_42,k3_waybel_0(sK1,sK2))) = iProver_top
    | r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,X0_42,k3_waybel_0(sK1,sK2))) = iProver_top
    | r1_yellow_0(sK1,X0_42) != iProver_top
    | r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_432,plain,
    ( r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) = iProver_top
    | r2_lattice3(sK1,sK2,sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) = iProver_top
    | r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) = iProver_top
    | r1_yellow_0(sK1,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_430])).

cnf(c_2,plain,
    ( ~ r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ r2_lattice3(X0,X2,sK0(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | r1_yellow_0(X0,X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_239,plain,
    ( ~ r2_lattice3(sK1,X0,sK0(sK1,X1,X0))
    | ~ r2_lattice3(sK1,X1,sK0(sK1,X1,X0))
    | ~ r1_yellow_0(sK1,X1)
    | r1_yellow_0(sK1,X0)
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_2,c_8])).

cnf(c_241,plain,
    ( r1_yellow_0(sK1,X0)
    | ~ r1_yellow_0(sK1,X1)
    | ~ r2_lattice3(sK1,X1,sK0(sK1,X1,X0))
    | ~ r2_lattice3(sK1,X0,sK0(sK1,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_239,c_11])).

cnf(c_242,plain,
    ( ~ r2_lattice3(sK1,X0,sK0(sK1,X1,X0))
    | ~ r2_lattice3(sK1,X1,sK0(sK1,X1,X0))
    | ~ r1_yellow_0(sK1,X1)
    | r1_yellow_0(sK1,X0) ),
    inference(renaming,[status(thm)],[c_241])).

cnf(c_348,plain,
    ( ~ r2_lattice3(sK1,X0_42,sK0(sK1,X1_42,X0_42))
    | ~ r2_lattice3(sK1,X1_42,sK0(sK1,X1_42,X0_42))
    | ~ r1_yellow_0(sK1,X1_42)
    | r1_yellow_0(sK1,X0_42) ),
    inference(subtyping,[status(esa)],[c_242])).

cnf(c_424,plain,
    ( ~ r2_lattice3(sK1,X0_42,sK0(sK1,X0_42,k3_waybel_0(sK1,sK2)))
    | ~ r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,X0_42,k3_waybel_0(sK1,sK2)))
    | ~ r1_yellow_0(sK1,X0_42)
    | r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_425,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,X0_42,k3_waybel_0(sK1,sK2))) != iProver_top
    | r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,X0_42,k3_waybel_0(sK1,sK2))) != iProver_top
    | r1_yellow_0(sK1,X0_42) != iProver_top
    | r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_427,plain,
    ( r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) != iProver_top
    | r2_lattice3(sK1,sK2,sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) != iProver_top
    | r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) = iProver_top
    | r1_yellow_0(sK1,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_4,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r1_yellow_0(X0,X2)
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_204,plain,
    ( ~ r1_yellow_0(sK1,X0)
    | r1_yellow_0(sK1,X1)
    | m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_4,c_8])).

cnf(c_206,plain,
    ( m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1))
    | r1_yellow_0(sK1,X1)
    | ~ r1_yellow_0(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_204,c_11])).

cnf(c_207,plain,
    ( ~ r1_yellow_0(sK1,X0)
    | r1_yellow_0(sK1,X1)
    | m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_206])).

cnf(c_350,plain,
    ( ~ r1_yellow_0(sK1,X0_42)
    | r1_yellow_0(sK1,X1_42)
    | m1_subset_1(sK0(sK1,X0_42,X1_42),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_207])).

cnf(c_418,plain,
    ( ~ r1_yellow_0(sK1,X0_42)
    | r1_yellow_0(sK1,k3_waybel_0(sK1,sK2))
    | m1_subset_1(sK0(sK1,X0_42,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_419,plain,
    ( r1_yellow_0(sK1,X0_42) != iProver_top
    | r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) = iProver_top
    | m1_subset_1(sK0(sK1,X0_42,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_421,plain,
    ( r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) = iProver_top
    | r1_yellow_0(sK1,sK2) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_419])).

cnf(c_407,plain,
    ( ~ r2_lattice3(sK1,X0_42,sK0(sK1,k3_waybel_0(sK1,sK2),X1_42))
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0_42),sK0(sK1,k3_waybel_0(sK1,sK2),X1_42))
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(sK1,k3_waybel_0(sK1,sK2),X1_42),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_413,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,k3_waybel_0(sK1,sK2),X1_42)) != iProver_top
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0_42),sK0(sK1,k3_waybel_0(sK1,sK2),X1_42)) = iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,k3_waybel_0(sK1,sK2),X1_42),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_415,plain,
    ( r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,k3_waybel_0(sK1,sK2),sK2)) = iProver_top
    | r2_lattice3(sK1,sK2,sK0(sK1,k3_waybel_0(sK1,sK2),sK2)) != iProver_top
    | m1_subset_1(sK0(sK1,k3_waybel_0(sK1,sK2),sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_408,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,k3_waybel_0(sK1,sK2),X1_42))
    | ~ r2_lattice3(sK1,k3_waybel_0(sK1,X0_42),sK0(sK1,k3_waybel_0(sK1,sK2),X1_42))
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(sK1,k3_waybel_0(sK1,sK2),X1_42),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_409,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,k3_waybel_0(sK1,sK2),X1_42)) = iProver_top
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0_42),sK0(sK1,k3_waybel_0(sK1,sK2),X1_42)) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,k3_waybel_0(sK1,sK2),X1_42),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_411,plain,
    ( r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,k3_waybel_0(sK1,sK2),sK2)) != iProver_top
    | r2_lattice3(sK1,sK2,sK0(sK1,k3_waybel_0(sK1,sK2),sK2)) = iProver_top
    | m1_subset_1(sK0(sK1,k3_waybel_0(sK1,sK2),sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_402,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,k3_waybel_0(sK1,sK2),X0_42))
    | r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,k3_waybel_0(sK1,sK2),X0_42))
    | r1_yellow_0(sK1,X0_42)
    | ~ r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_403,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,k3_waybel_0(sK1,sK2),X0_42)) = iProver_top
    | r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,k3_waybel_0(sK1,sK2),X0_42)) = iProver_top
    | r1_yellow_0(sK1,X0_42) = iProver_top
    | r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_405,plain,
    ( r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,k3_waybel_0(sK1,sK2),sK2)) = iProver_top
    | r2_lattice3(sK1,sK2,sK0(sK1,k3_waybel_0(sK1,sK2),sK2)) = iProver_top
    | r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) != iProver_top
    | r1_yellow_0(sK1,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_403])).

cnf(c_397,plain,
    ( ~ r2_lattice3(sK1,X0_42,sK0(sK1,k3_waybel_0(sK1,sK2),X0_42))
    | ~ r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,k3_waybel_0(sK1,sK2),X0_42))
    | r1_yellow_0(sK1,X0_42)
    | ~ r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_398,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,k3_waybel_0(sK1,sK2),X0_42)) != iProver_top
    | r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,k3_waybel_0(sK1,sK2),X0_42)) != iProver_top
    | r1_yellow_0(sK1,X0_42) = iProver_top
    | r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_400,plain,
    ( r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,k3_waybel_0(sK1,sK2),sK2)) != iProver_top
    | r2_lattice3(sK1,sK2,sK0(sK1,k3_waybel_0(sK1,sK2),sK2)) != iProver_top
    | r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) != iProver_top
    | r1_yellow_0(sK1,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_392,plain,
    ( r1_yellow_0(sK1,X0_42)
    | ~ r1_yellow_0(sK1,k3_waybel_0(sK1,sK2))
    | m1_subset_1(sK0(sK1,k3_waybel_0(sK1,sK2),X0_42),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_393,plain,
    ( r1_yellow_0(sK1,X0_42) = iProver_top
    | r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) != iProver_top
    | m1_subset_1(sK0(sK1,k3_waybel_0(sK1,sK2),X0_42),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_395,plain,
    ( r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) != iProver_top
    | r1_yellow_0(sK1,sK2) = iProver_top
    | m1_subset_1(sK0(sK1,k3_waybel_0(sK1,sK2),sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_5,negated_conjecture,
    ( ~ r1_yellow_0(sK1,k3_waybel_0(sK1,sK2))
    | ~ r1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_18,plain,
    ( r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) != iProver_top
    | r1_yellow_0(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,negated_conjecture,
    ( r1_yellow_0(sK1,k3_waybel_0(sK1,sK2))
    | r1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_17,plain,
    ( r1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) = iProver_top
    | r1_yellow_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_16,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_442,c_438,c_432,c_427,c_421,c_415,c_411,c_405,c_400,c_395,c_18,c_17,c_16])).


%------------------------------------------------------------------------------
