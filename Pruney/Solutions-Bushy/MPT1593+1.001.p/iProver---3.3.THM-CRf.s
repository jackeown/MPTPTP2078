%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1593+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:59 EST 2020

% Result     : Theorem 1.02s
% Output     : CNFRefutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 207 expanded)
%              Number of clauses        :   32 (  76 expanded)
%              Number of leaves         :    7 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  123 ( 409 expanded)
%              Number of equality atoms :   84 ( 212 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f18,f16])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f15,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f17,f16])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,conjecture,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
        & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) != k1_yellow_1(X0)
      | u1_struct_0(k2_yellow_1(X0)) != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,
    ( ? [X0] :
        ( u1_orders_2(k2_yellow_1(X0)) != k1_yellow_1(X0)
        | u1_struct_0(k2_yellow_1(X0)) != X0 )
   => ( u1_orders_2(k2_yellow_1(sK0)) != k1_yellow_1(sK0)
      | u1_struct_0(k2_yellow_1(sK0)) != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( u1_orders_2(k2_yellow_1(sK0)) != k1_yellow_1(sK0)
    | u1_struct_0(k2_yellow_1(sK0)) != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f22,plain,
    ( u1_orders_2(k2_yellow_1(sK0)) != k1_yellow_1(sK0)
    | u1_struct_0(k2_yellow_1(sK0)) != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,
    ( u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) != k1_yellow_1(sK0)
    | u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) != sK0 ),
    inference(definition_unfolding,[],[f22,f16,f16])).

cnf(c_1,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_305,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_306,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | l1_orders_2(X0) != iProver_top
    | v1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_489,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) = g1_orders_2(X0,k1_yellow_1(X0))
    | v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_305,c_306])).

cnf(c_2,plain,
    ( v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_78,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(X1,k1_yellow_1(X1)) != X0
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_79,plain,
    ( ~ l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))
    | g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_78])).

cnf(c_645,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_1,c_79])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_302,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_650,plain,
    ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
    | u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = X2
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_645,c_302])).

cnf(c_3,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_90,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | g1_orders_2(X1,k1_yellow_1(X1)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_1])).

cnf(c_91,plain,
    ( m1_subset_1(u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))))) ),
    inference(unflattening,[status(thm)],[c_90])).

cnf(c_651,plain,
    ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
    | u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = X2
    | m1_subset_1(u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_645,c_302])).

cnf(c_685,plain,
    ( ~ m1_subset_1(u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))))
    | g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
    | u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = X2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_651])).

cnf(c_778,plain,
    ( u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = X2
    | g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_650,c_91,c_685])).

cnf(c_779,plain,
    ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
    | u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = X2 ),
    inference(renaming,[status(thm)],[c_778])).

cnf(c_784,plain,
    ( u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = k1_yellow_1(X0) ),
    inference(equality_resolution,[status(thm)],[c_779])).

cnf(c_794,plain,
    ( u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) = k1_yellow_1(sK0) ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_301,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_648,plain,
    ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_645,c_301])).

cnf(c_649,plain,
    ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1
    | m1_subset_1(u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_645,c_301])).

cnf(c_679,plain,
    ( ~ m1_subset_1(u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))))
    | g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_649])).

cnf(c_760,plain,
    ( u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1
    | g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_648,c_91,c_679])).

cnf(c_761,plain,
    ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1 ),
    inference(renaming,[status(thm)],[c_760])).

cnf(c_766,plain,
    ( u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0 ),
    inference(equality_resolution,[status(thm)],[c_761])).

cnf(c_776,plain,
    ( u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) = sK0 ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_6,negated_conjecture,
    ( u1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) != k1_yellow_1(sK0)
    | u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) != sK0 ),
    inference(cnf_transformation,[],[f25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_794,c_776,c_6])).


%------------------------------------------------------------------------------
