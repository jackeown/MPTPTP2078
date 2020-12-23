%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1915+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:52 EST 2020

% Result     : Theorem 1.23s
% Output     : CNFRefutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 108 expanded)
%              Number of clauses        :   32 (  33 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :   19
%              Number of atoms          :  243 ( 498 expanded)
%              Number of equality atoms :   75 ( 130 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => u1_struct_0(X0) = u1_struct_0(k3_yellow_6(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => u1_struct_0(X0) = u1_struct_0(k3_yellow_6(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,sK2))
        & m1_subset_1(sK2,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,sK1,X2))
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        & l1_struct_0(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f19,f18,f17])).

fof(f32,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X1)
                    & v6_waybel_0(X3,X1) )
                 => ( k3_yellow_6(X0,X1,X2) = X3
                  <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_yellow_6(X0,X1,X2) = X3
                  <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_yellow_6(X0,X1,X2) = X3
                  <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_yellow_6(X0,X1,X2) = X3
                      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                    & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                        & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                      | k3_yellow_6(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_yellow_6(X0,X1,X2) = X3
                      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                    & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                        & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                      | k3_yellow_6(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
      | k3_yellow_6(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X1)
      | ~ v6_waybel_0(X3,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,X1,X2)),u1_orders_2(k3_yellow_6(X0,X1,X2)))
      | ~ l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ v6_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1)
        & l1_orders_2(X0) )
     => ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
        & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
        & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
        & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1110,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_12,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v6_waybel_0(k3_yellow_6(X2,X1,X0),X1)
    | ~ l1_waybel_0(k3_yellow_6(X2,X1,X0),X1)
    | ~ l1_orders_2(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | g1_orders_2(u1_struct_0(k3_yellow_6(X2,X1,X0)),u1_orders_2(k3_yellow_6(X2,X1,X0))) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v6_waybel_0(k3_yellow_6(X2,X1,X0),X1)
    | ~ l1_orders_2(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | l1_waybel_0(k3_yellow_6(X2,X1,X0),X1)
    | ~ l1_orders_2(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_73,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | g1_orders_2(u1_struct_0(k3_yellow_6(X2,X1,X0)),u1_orders_2(k3_yellow_6(X2,X1,X0))) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_4,c_3])).

cnf(c_10,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X2)
    | v2_struct_0(X1)
    | g1_orders_2(u1_struct_0(k3_yellow_6(X2,X1,X0)),u1_orders_2(k3_yellow_6(X2,X1,X0))) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_73,c_10])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ l1_orders_2(X1)
    | v2_struct_0(sK1)
    | g1_orders_2(u1_struct_0(k3_yellow_6(X1,sK1,X0)),u1_orders_2(k3_yellow_6(X1,sK1,X0))) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_11,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_391,plain,
    ( ~ l1_orders_2(X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | g1_orders_2(u1_struct_0(k3_yellow_6(X1,sK1,X0)),u1_orders_2(k3_yellow_6(X1,sK1,X0))) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_11])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ l1_orders_2(X1)
    | g1_orders_2(u1_struct_0(k3_yellow_6(X1,sK1,X0)),u1_orders_2(k3_yellow_6(X1,sK1,X0))) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ),
    inference(renaming,[status(thm)],[c_391])).

cnf(c_717,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | g1_orders_2(u1_struct_0(k3_yellow_6(X1,sK1,X0)),u1_orders_2(k3_yellow_6(X1,sK1,X0))) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_392])).

cnf(c_718,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | g1_orders_2(u1_struct_0(k3_yellow_6(sK0,sK1,X0)),u1_orders_2(k3_yellow_6(sK0,sK1,X0))) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) ),
    inference(unflattening,[status(thm)],[c_717])).

cnf(c_1107,plain,
    ( g1_orders_2(u1_struct_0(k3_yellow_6(sK0,sK1,X0)),u1_orders_2(k3_yellow_6(sK0,sK1,X0))) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_1205,plain,
    ( g1_orders_2(u1_struct_0(k3_yellow_6(sK0,sK1,sK2)),u1_orders_2(k3_yellow_6(sK0,sK1,sK2))) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) ),
    inference(superposition,[status(thm)],[c_1110,c_1107])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1111,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1367,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_1111])).

cnf(c_1477,plain,
    ( u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) = u1_struct_0(sK0)
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1367])).

cnf(c_954,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1235,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_955,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_1178,plain,
    ( u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) != X0
    | u1_struct_0(sK0) != X0
    | u1_struct_0(sK0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_955])).

cnf(c_1234,plain,
    ( u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) != u1_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k3_yellow_6(sK0,sK1,sK2))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1178])).

cnf(c_5,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_662,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_12])).

cnf(c_663,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_662])).

cnf(c_664,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_8,negated_conjecture,
    ( u1_struct_0(sK0) != u1_struct_0(k3_yellow_6(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1477,c_1235,c_1234,c_664,c_8])).


%------------------------------------------------------------------------------
