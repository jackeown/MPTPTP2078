%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1653+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:06 EST 2020

% Result     : Theorem 0.52s
% Output     : CNFRefutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 256 expanded)
%              Number of clauses        :   58 (  70 expanded)
%              Number of leaves         :    6 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  407 (1571 expanded)
%              Number of equality atoms :   84 ( 258 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   4 average)
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

fof(f19,plain,(
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
           => k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
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
             => k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_waybel_0(X0,X1))
          & r1_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_waybel_0(X0,X1))
          & r1_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_waybel_0(X0,X1))
          & r1_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_yellow_0(X0,sK2) != k1_yellow_0(X0,k3_waybel_0(X0,sK2))
        & r1_yellow_0(X0,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_waybel_0(X0,X1))
            & r1_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_yellow_0(sK1,X1) != k1_yellow_0(sK1,k3_waybel_0(sK1,X1))
          & r1_yellow_0(sK1,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( k1_yellow_0(sK1,sK2) != k1_yellow_0(sK1,k3_waybel_0(sK1,sK2))
    & r1_yellow_0(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f10,f17,f16])).

fof(f26,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f20,plain,(
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

fof(f29,plain,(
    r1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) )
            & r1_yellow_0(X0,X1) )
         => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
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
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ( ( ~ r2_lattice3(X0,X2,sK0(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK0(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK0(X0,X1,X2))
              | r2_lattice3(X0,X1,sK0(X0,X1,X2)) )
            & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,sK0(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK0(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,sK0(X0,X1,X2))
      | r2_lattice3(X0,X1,sK0(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    k1_yellow_0(sK1,sK2) != k1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_1,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_9,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_124,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_125,plain,
    ( ~ r2_lattice3(sK1,X0,X1)
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_124])).

cnf(c_11,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_10,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_8,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_129,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0),X1)
    | ~ r2_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_125,c_11,c_10,c_8])).

cnf(c_130,plain,
    ( ~ r2_lattice3(sK1,X0,X1)
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_129])).

cnf(c_369,plain,
    ( ~ r2_lattice3(sK1,X0_42,X1_42)
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0_42),X1_42)
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_130])).

cnf(c_508,plain,
    ( ~ r2_lattice3(sK1,X0_42,sK0(sK1,sK2,k3_waybel_0(sK1,sK2)))
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0_42),sK0(sK1,sK2,k3_waybel_0(sK1,sK2)))
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(sK1,sK2,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_514,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) != iProver_top
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0_42),sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) = iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_516,plain,
    ( r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) = iProver_top
    | r2_lattice3(sK1,sK2,sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_0,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_148,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_149,plain,
    ( r2_lattice3(sK1,X0,X1)
    | ~ r2_lattice3(sK1,k3_waybel_0(sK1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_148])).

cnf(c_153,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_lattice3(sK1,k3_waybel_0(sK1,X0),X1)
    | r2_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_149,c_11,c_10,c_8])).

cnf(c_154,plain,
    ( r2_lattice3(sK1,X0,X1)
    | ~ r2_lattice3(sK1,k3_waybel_0(sK1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_153])).

cnf(c_368,plain,
    ( r2_lattice3(sK1,X0_42,X1_42)
    | ~ r2_lattice3(sK1,k3_waybel_0(sK1,X0_42),X1_42)
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_42,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_154])).

cnf(c_509,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,sK2,k3_waybel_0(sK1,sK2)))
    | ~ r2_lattice3(sK1,k3_waybel_0(sK1,X0_42),sK0(sK1,sK2,k3_waybel_0(sK1,sK2)))
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(sK1,sK2,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_510,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) = iProver_top
    | r2_lattice3(sK1,k3_waybel_0(sK1,X0_42),sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_512,plain,
    ( r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) != iProver_top
    | r2_lattice3(sK1,sK2,sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_6,negated_conjecture,
    ( r1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2,plain,
    ( ~ r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ r2_lattice3(X0,X2,sK0(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_227,plain,
    ( ~ r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | ~ r2_lattice3(X0,X2,sK0(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | v2_struct_0(X0)
    | k1_yellow_0(X0,X2) = k1_yellow_0(X0,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_228,plain,
    ( ~ r2_lattice3(sK1,X0,sK0(sK1,X0,X1))
    | ~ r2_lattice3(sK1,X1,sK0(sK1,X0,X1))
    | ~ r1_yellow_0(sK1,X0)
    | v2_struct_0(sK1)
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK1,X1) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_232,plain,
    ( ~ r1_yellow_0(sK1,X0)
    | ~ r2_lattice3(sK1,X1,sK0(sK1,X0,X1))
    | ~ r2_lattice3(sK1,X0,sK0(sK1,X0,X1))
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_228,c_11])).

cnf(c_233,plain,
    ( ~ r2_lattice3(sK1,X0,sK0(sK1,X0,X1))
    | ~ r2_lattice3(sK1,X1,sK0(sK1,X0,X1))
    | ~ r1_yellow_0(sK1,X0)
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK1,X1) ),
    inference(renaming,[status(thm)],[c_232])).

cnf(c_265,plain,
    ( ~ r2_lattice3(sK1,X0,sK0(sK1,X0,X1))
    | ~ r2_lattice3(sK1,X1,sK0(sK1,X0,X1))
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK1,X1)
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_233])).

cnf(c_266,plain,
    ( ~ r2_lattice3(sK1,X0,sK0(sK1,sK2,X0))
    | ~ r2_lattice3(sK1,sK2,sK0(sK1,sK2,X0))
    | k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_367,plain,
    ( ~ r2_lattice3(sK1,X0_42,sK0(sK1,sK2,X0_42))
    | ~ r2_lattice3(sK1,sK2,sK0(sK1,sK2,X0_42))
    | k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,X0_42) ),
    inference(subtyping,[status(esa)],[c_266])).

cnf(c_500,plain,
    ( ~ r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,sK2,k3_waybel_0(sK1,sK2)))
    | ~ r2_lattice3(sK1,sK2,sK0(sK1,sK2,k3_waybel_0(sK1,sK2)))
    | k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_501,plain,
    ( k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,k3_waybel_0(sK1,sK2))
    | r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) != iProver_top
    | r2_lattice3(sK1,sK2,sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_3,plain,
    ( r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | r2_lattice3(X0,X2,sK0(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_203,plain,
    ( r2_lattice3(X0,X1,sK0(X0,X2,X1))
    | r2_lattice3(X0,X2,sK0(X0,X2,X1))
    | ~ r1_yellow_0(X0,X2)
    | v2_struct_0(X0)
    | k1_yellow_0(X0,X2) = k1_yellow_0(X0,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_204,plain,
    ( r2_lattice3(sK1,X0,sK0(sK1,X0,X1))
    | r2_lattice3(sK1,X1,sK0(sK1,X0,X1))
    | ~ r1_yellow_0(sK1,X0)
    | v2_struct_0(sK1)
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK1,X1) ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_208,plain,
    ( ~ r1_yellow_0(sK1,X0)
    | r2_lattice3(sK1,X1,sK0(sK1,X0,X1))
    | r2_lattice3(sK1,X0,sK0(sK1,X0,X1))
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_204,c_11])).

cnf(c_209,plain,
    ( r2_lattice3(sK1,X0,sK0(sK1,X0,X1))
    | r2_lattice3(sK1,X1,sK0(sK1,X0,X1))
    | ~ r1_yellow_0(sK1,X0)
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK1,X1) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_280,plain,
    ( r2_lattice3(sK1,X0,sK0(sK1,X0,X1))
    | r2_lattice3(sK1,X1,sK0(sK1,X0,X1))
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK1,X1)
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_209])).

cnf(c_281,plain,
    ( r2_lattice3(sK1,X0,sK0(sK1,sK2,X0))
    | r2_lattice3(sK1,sK2,sK0(sK1,sK2,X0))
    | k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_366,plain,
    ( r2_lattice3(sK1,X0_42,sK0(sK1,sK2,X0_42))
    | r2_lattice3(sK1,sK2,sK0(sK1,sK2,X0_42))
    | k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,X0_42) ),
    inference(subtyping,[status(esa)],[c_281])).

cnf(c_497,plain,
    ( r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,sK2,k3_waybel_0(sK1,sK2)))
    | r2_lattice3(sK1,sK2,sK0(sK1,sK2,k3_waybel_0(sK1,sK2)))
    | k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_498,plain,
    ( k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,k3_waybel_0(sK1,sK2))
    | r2_lattice3(sK1,k3_waybel_0(sK1,sK2),sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) = iProver_top
    | r2_lattice3(sK1,sK2,sK0(sK1,sK2,k3_waybel_0(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_4,plain,
    ( ~ r1_yellow_0(X0,X1)
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X2) = k1_yellow_0(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_182,plain,
    ( ~ r1_yellow_0(X0,X1)
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | k1_yellow_0(X0,X2) = k1_yellow_0(X0,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_183,plain,
    ( ~ r1_yellow_0(sK1,X0)
    | m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | k1_yellow_0(sK1,X1) = k1_yellow_0(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_182])).

cnf(c_187,plain,
    ( m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1))
    | ~ r1_yellow_0(sK1,X0)
    | k1_yellow_0(sK1,X1) = k1_yellow_0(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_183,c_11])).

cnf(c_188,plain,
    ( ~ r1_yellow_0(sK1,X0)
    | m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1))
    | k1_yellow_0(sK1,X1) = k1_yellow_0(sK1,X0) ),
    inference(renaming,[status(thm)],[c_187])).

cnf(c_295,plain,
    ( m1_subset_1(sK0(sK1,X0,X1),u1_struct_0(sK1))
    | k1_yellow_0(sK1,X0) = k1_yellow_0(sK1,X1)
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_188])).

cnf(c_296,plain,
    ( m1_subset_1(sK0(sK1,sK2,X0),u1_struct_0(sK1))
    | k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_365,plain,
    ( m1_subset_1(sK0(sK1,sK2,X0_42),u1_struct_0(sK1))
    | k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,X0_42) ),
    inference(subtyping,[status(esa)],[c_296])).

cnf(c_494,plain,
    ( m1_subset_1(sK0(sK1,sK2,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1))
    | k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_495,plain,
    ( k1_yellow_0(sK1,sK2) = k1_yellow_0(sK1,k3_waybel_0(sK1,sK2))
    | m1_subset_1(sK0(sK1,sK2,k3_waybel_0(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_5,negated_conjecture,
    ( k1_yellow_0(sK1,sK2) != k1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_371,negated_conjecture,
    ( k1_yellow_0(sK1,sK2) != k1_yellow_0(sK1,k3_waybel_0(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_16,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_516,c_512,c_501,c_498,c_495,c_371,c_16])).


%------------------------------------------------------------------------------
