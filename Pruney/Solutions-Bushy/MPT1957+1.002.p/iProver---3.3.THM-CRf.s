%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1957+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:55 EST 2020

% Result     : Theorem 0.87s
% Output     : CNFRefutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 120 expanded)
%              Number of clauses        :   23 (  39 expanded)
%              Number of leaves         :    9 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  100 ( 222 expanded)
%              Number of equality atoms :   61 ( 119 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f17,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f8,conjecture,(
    ! [X0] : u1_struct_0(k3_yellow_1(X0)) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] : u1_struct_0(k3_yellow_1(X0)) = k9_setfam_1(X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f14,plain,(
    ? [X0] : u1_struct_0(k3_yellow_1(X0)) != k9_setfam_1(X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,
    ( ? [X0] : u1_struct_0(k3_yellow_1(X0)) != k9_setfam_1(X0)
   => u1_struct_0(k3_yellow_1(sK0)) != k9_setfam_1(sK0) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    u1_struct_0(k3_yellow_1(sK0)) != k9_setfam_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f26,plain,(
    u1_struct_0(k3_yellow_1(sK0)) != k9_setfam_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0] : k2_yellow_1(k9_setfam_1(X0)) = k3_yellow_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k2_yellow_1(k9_setfam_1(X0)) = k3_yellow_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] : g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) = k3_yellow_1(X0) ),
    inference(definition_unfolding,[],[f25,f18])).

fof(f33,plain,(
    u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0)))) != k9_setfam_1(sK0) ),
    inference(definition_unfolding,[],[f26,f27])).

cnf(c_1,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_302,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_303,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | l1_orders_2(X0) != iProver_top
    | v1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_472,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) = g1_orders_2(X0,k1_yellow_1(X0))
    | v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_302,c_303])).

cnf(c_2,plain,
    ( v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_77,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(X1,k1_yellow_1(X1)) != X0
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_78,plain,
    ( ~ l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))
    | g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_77])).

cnf(c_614,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_472,c_1,c_78])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_298,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k9_setfam_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_617,plain,
    ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1
    | m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_298])).

cnf(c_3,plain,
    ( m1_subset_1(u1_orders_2(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_89,plain,
    ( m1_subset_1(u1_orders_2(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | g1_orders_2(X1,k1_yellow_1(X1)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_1])).

cnf(c_90,plain,
    ( m1_subset_1(u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))),k9_setfam_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))))) ),
    inference(unflattening,[status(thm)],[c_89])).

cnf(c_618,plain,
    ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1
    | m1_subset_1(u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))),k9_setfam_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_298])).

cnf(c_648,plain,
    ( ~ m1_subset_1(u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))),k9_setfam_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))))
    | g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_618])).

cnf(c_734,plain,
    ( u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1
    | g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_617,c_90,c_648])).

cnf(c_735,plain,
    ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1 ),
    inference(renaming,[status(thm)],[c_734])).

cnf(c_740,plain,
    ( u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0 ),
    inference(equality_resolution,[status(thm)],[c_735])).

cnf(c_6,negated_conjecture,
    ( u1_struct_0(g1_orders_2(k9_setfam_1(sK0),k1_yellow_1(k9_setfam_1(sK0)))) != k9_setfam_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_855,plain,
    ( k9_setfam_1(sK0) != k9_setfam_1(sK0) ),
    inference(demodulation,[status(thm)],[c_740,c_6])).

cnf(c_859,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_855])).


%------------------------------------------------------------------------------
