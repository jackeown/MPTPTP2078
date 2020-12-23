%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:06 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 175 expanded)
%              Number of clauses        :   48 (  76 expanded)
%              Number of leaves         :   11 (  42 expanded)
%              Depth                    :   17
%              Number of atoms          :  148 ( 433 expanded)
%              Number of equality atoms :   76 ( 171 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,X1) != k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,X1) != k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_tops_1(X0,sK1) != k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),sK1))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_tops_1(X0,X1) != k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_tops_1(sK0,X1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16,f15])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_171,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_314,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_171])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_7,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_100,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_7])).

cnf(c_101,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_100])).

cnf(c_169,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_101])).

cnf(c_316,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_169])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_173,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X0_40))
    | k3_subset_1(X0_40,k3_subset_1(X0_40,X0_38)) = X0_38 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_313,plain,
    ( k3_subset_1(X0_40,k3_subset_1(X0_40,X0_38)) = X0_38
    | m1_subset_1(X0_38,k1_zfmisc_1(X0_40)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_173])).

cnf(c_570,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_38))) = k2_pre_topc(sK0,X0_38)
    | m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_316,c_313])).

cnf(c_808,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_314,c_570])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_174,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X0_40))
    | m1_subset_1(k3_subset_1(X0_40,X0_38),k1_zfmisc_1(X0_40)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_312,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(X0_40)) != iProver_top
    | m1_subset_1(k3_subset_1(X0_40,X0_38),k1_zfmisc_1(X0_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_174])).

cnf(c_828,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_808,c_312])).

cnf(c_9,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_207,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_169])).

cnf(c_209,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_900,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_828,c_9,c_209])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_175,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X0_40))
    | k9_subset_1(X0_40,X0_38,X1_38) = k9_subset_1(X0_40,X1_38,X0_38) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_311,plain,
    ( k9_subset_1(X0_40,X0_38,X1_38) = k9_subset_1(X0_40,X1_38,X0_38)
    | m1_subset_1(X0_38,k1_zfmisc_1(X0_40)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_175])).

cnf(c_910,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_38,k2_pre_topc(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0_38) ),
    inference(superposition,[status(thm)],[c_900,c_311])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_88,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_7])).

cnf(c_89,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_88])).

cnf(c_170,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_38),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_38))) = k2_tops_1(sK0,X0_38) ),
    inference(subtyping,[status(esa)],[c_89])).

cnf(c_315,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_38),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_38))) = k2_tops_1(sK0,X0_38)
    | m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_170])).

cnf(c_641,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_38)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0_38)))) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0_38))
    | m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_312,c_315])).

cnf(c_1906,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_314,c_641])).

cnf(c_569,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_314,c_313])).

cnf(c_1922,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(light_normalisation,[status(thm)],[c_1906,c_569])).

cnf(c_1931,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_910,c_1922])).

cnf(c_399,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_314,c_315])).

cnf(c_1933,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1931,c_399])).

cnf(c_180,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_370,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != X0_42
    | k2_tops_1(sK0,sK1) != X0_42
    | k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_180])).

cnf(c_410,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_tops_1(sK0,sK1)
    | k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_5,negated_conjecture,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_172,negated_conjecture,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_177,plain,
    ( X0_38 = X0_38 ),
    theory(equality)).

cnf(c_192,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_185,plain,
    ( k2_tops_1(X0_41,X0_38) = k2_tops_1(X0_41,X1_38)
    | X0_38 != X1_38 ),
    theory(equality)).

cnf(c_190,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1933,c_410,c_172,c_192,c_190])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:38:44 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running in FOF mode
% 2.46/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/0.99  
% 2.46/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.46/0.99  
% 2.46/0.99  ------  iProver source info
% 2.46/0.99  
% 2.46/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.46/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.46/0.99  git: non_committed_changes: false
% 2.46/0.99  git: last_make_outside_of_git: false
% 2.46/0.99  
% 2.46/0.99  ------ 
% 2.46/0.99  
% 2.46/0.99  ------ Input Options
% 2.46/0.99  
% 2.46/0.99  --out_options                           all
% 2.46/0.99  --tptp_safe_out                         true
% 2.46/0.99  --problem_path                          ""
% 2.46/0.99  --include_path                          ""
% 2.46/0.99  --clausifier                            res/vclausify_rel
% 2.46/0.99  --clausifier_options                    --mode clausify
% 2.46/0.99  --stdin                                 false
% 2.46/0.99  --stats_out                             all
% 2.46/0.99  
% 2.46/0.99  ------ General Options
% 2.46/0.99  
% 2.46/0.99  --fof                                   false
% 2.46/0.99  --time_out_real                         305.
% 2.46/0.99  --time_out_virtual                      -1.
% 2.46/0.99  --symbol_type_check                     false
% 2.46/0.99  --clausify_out                          false
% 2.46/0.99  --sig_cnt_out                           false
% 2.46/0.99  --trig_cnt_out                          false
% 2.46/0.99  --trig_cnt_out_tolerance                1.
% 2.46/0.99  --trig_cnt_out_sk_spl                   false
% 2.46/0.99  --abstr_cl_out                          false
% 2.46/0.99  
% 2.46/0.99  ------ Global Options
% 2.46/0.99  
% 2.46/0.99  --schedule                              default
% 2.46/0.99  --add_important_lit                     false
% 2.46/0.99  --prop_solver_per_cl                    1000
% 2.46/0.99  --min_unsat_core                        false
% 2.46/0.99  --soft_assumptions                      false
% 2.46/0.99  --soft_lemma_size                       3
% 2.46/0.99  --prop_impl_unit_size                   0
% 2.46/0.99  --prop_impl_unit                        []
% 2.46/0.99  --share_sel_clauses                     true
% 2.46/0.99  --reset_solvers                         false
% 2.46/0.99  --bc_imp_inh                            [conj_cone]
% 2.46/0.99  --conj_cone_tolerance                   3.
% 2.46/0.99  --extra_neg_conj                        none
% 2.46/0.99  --large_theory_mode                     true
% 2.46/0.99  --prolific_symb_bound                   200
% 2.46/0.99  --lt_threshold                          2000
% 2.46/0.99  --clause_weak_htbl                      true
% 2.46/0.99  --gc_record_bc_elim                     false
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing Options
% 2.46/0.99  
% 2.46/0.99  --preprocessing_flag                    true
% 2.46/0.99  --time_out_prep_mult                    0.1
% 2.46/0.99  --splitting_mode                        input
% 2.46/0.99  --splitting_grd                         true
% 2.46/0.99  --splitting_cvd                         false
% 2.46/0.99  --splitting_cvd_svl                     false
% 2.46/0.99  --splitting_nvd                         32
% 2.46/0.99  --sub_typing                            true
% 2.46/0.99  --prep_gs_sim                           true
% 2.46/0.99  --prep_unflatten                        true
% 2.46/0.99  --prep_res_sim                          true
% 2.46/0.99  --prep_upred                            true
% 2.46/0.99  --prep_sem_filter                       exhaustive
% 2.46/0.99  --prep_sem_filter_out                   false
% 2.46/0.99  --pred_elim                             true
% 2.46/0.99  --res_sim_input                         true
% 2.46/0.99  --eq_ax_congr_red                       true
% 2.46/0.99  --pure_diseq_elim                       true
% 2.46/0.99  --brand_transform                       false
% 2.46/0.99  --non_eq_to_eq                          false
% 2.46/0.99  --prep_def_merge                        true
% 2.46/0.99  --prep_def_merge_prop_impl              false
% 2.46/0.99  --prep_def_merge_mbd                    true
% 2.46/0.99  --prep_def_merge_tr_red                 false
% 2.46/0.99  --prep_def_merge_tr_cl                  false
% 2.46/0.99  --smt_preprocessing                     true
% 2.46/0.99  --smt_ac_axioms                         fast
% 2.46/0.99  --preprocessed_out                      false
% 2.46/0.99  --preprocessed_stats                    false
% 2.46/0.99  
% 2.46/0.99  ------ Abstraction refinement Options
% 2.46/0.99  
% 2.46/0.99  --abstr_ref                             []
% 2.46/0.99  --abstr_ref_prep                        false
% 2.46/0.99  --abstr_ref_until_sat                   false
% 2.46/0.99  --abstr_ref_sig_restrict                funpre
% 2.46/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/0.99  --abstr_ref_under                       []
% 2.46/0.99  
% 2.46/0.99  ------ SAT Options
% 2.46/0.99  
% 2.46/0.99  --sat_mode                              false
% 2.46/0.99  --sat_fm_restart_options                ""
% 2.46/0.99  --sat_gr_def                            false
% 2.46/0.99  --sat_epr_types                         true
% 2.46/0.99  --sat_non_cyclic_types                  false
% 2.46/0.99  --sat_finite_models                     false
% 2.46/0.99  --sat_fm_lemmas                         false
% 2.46/0.99  --sat_fm_prep                           false
% 2.46/0.99  --sat_fm_uc_incr                        true
% 2.46/0.99  --sat_out_model                         small
% 2.46/0.99  --sat_out_clauses                       false
% 2.46/0.99  
% 2.46/0.99  ------ QBF Options
% 2.46/0.99  
% 2.46/0.99  --qbf_mode                              false
% 2.46/0.99  --qbf_elim_univ                         false
% 2.46/0.99  --qbf_dom_inst                          none
% 2.46/0.99  --qbf_dom_pre_inst                      false
% 2.46/0.99  --qbf_sk_in                             false
% 2.46/0.99  --qbf_pred_elim                         true
% 2.46/0.99  --qbf_split                             512
% 2.46/0.99  
% 2.46/0.99  ------ BMC1 Options
% 2.46/0.99  
% 2.46/0.99  --bmc1_incremental                      false
% 2.46/0.99  --bmc1_axioms                           reachable_all
% 2.46/0.99  --bmc1_min_bound                        0
% 2.46/0.99  --bmc1_max_bound                        -1
% 2.46/0.99  --bmc1_max_bound_default                -1
% 2.46/0.99  --bmc1_symbol_reachability              true
% 2.46/0.99  --bmc1_property_lemmas                  false
% 2.46/0.99  --bmc1_k_induction                      false
% 2.46/0.99  --bmc1_non_equiv_states                 false
% 2.46/0.99  --bmc1_deadlock                         false
% 2.46/0.99  --bmc1_ucm                              false
% 2.46/0.99  --bmc1_add_unsat_core                   none
% 2.46/0.99  --bmc1_unsat_core_children              false
% 2.46/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/0.99  --bmc1_out_stat                         full
% 2.46/0.99  --bmc1_ground_init                      false
% 2.46/0.99  --bmc1_pre_inst_next_state              false
% 2.46/0.99  --bmc1_pre_inst_state                   false
% 2.46/0.99  --bmc1_pre_inst_reach_state             false
% 2.46/0.99  --bmc1_out_unsat_core                   false
% 2.46/0.99  --bmc1_aig_witness_out                  false
% 2.46/0.99  --bmc1_verbose                          false
% 2.46/0.99  --bmc1_dump_clauses_tptp                false
% 2.46/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.46/0.99  --bmc1_dump_file                        -
% 2.46/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.46/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.46/0.99  --bmc1_ucm_extend_mode                  1
% 2.46/0.99  --bmc1_ucm_init_mode                    2
% 2.46/0.99  --bmc1_ucm_cone_mode                    none
% 2.46/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.46/0.99  --bmc1_ucm_relax_model                  4
% 2.46/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.46/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/0.99  --bmc1_ucm_layered_model                none
% 2.46/0.99  --bmc1_ucm_max_lemma_size               10
% 2.46/0.99  
% 2.46/0.99  ------ AIG Options
% 2.46/0.99  
% 2.46/0.99  --aig_mode                              false
% 2.46/0.99  
% 2.46/0.99  ------ Instantiation Options
% 2.46/0.99  
% 2.46/0.99  --instantiation_flag                    true
% 2.46/0.99  --inst_sos_flag                         false
% 2.46/0.99  --inst_sos_phase                        true
% 2.46/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/0.99  --inst_lit_sel_side                     num_symb
% 2.46/0.99  --inst_solver_per_active                1400
% 2.46/0.99  --inst_solver_calls_frac                1.
% 2.46/0.99  --inst_passive_queue_type               priority_queues
% 2.46/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/0.99  --inst_passive_queues_freq              [25;2]
% 2.46/0.99  --inst_dismatching                      true
% 2.46/0.99  --inst_eager_unprocessed_to_passive     true
% 2.46/0.99  --inst_prop_sim_given                   true
% 2.46/0.99  --inst_prop_sim_new                     false
% 2.46/0.99  --inst_subs_new                         false
% 2.46/0.99  --inst_eq_res_simp                      false
% 2.46/0.99  --inst_subs_given                       false
% 2.46/0.99  --inst_orphan_elimination               true
% 2.46/0.99  --inst_learning_loop_flag               true
% 2.46/0.99  --inst_learning_start                   3000
% 2.46/0.99  --inst_learning_factor                  2
% 2.46/0.99  --inst_start_prop_sim_after_learn       3
% 2.46/0.99  --inst_sel_renew                        solver
% 2.46/0.99  --inst_lit_activity_flag                true
% 2.46/0.99  --inst_restr_to_given                   false
% 2.46/0.99  --inst_activity_threshold               500
% 2.46/0.99  --inst_out_proof                        true
% 2.46/0.99  
% 2.46/0.99  ------ Resolution Options
% 2.46/0.99  
% 2.46/0.99  --resolution_flag                       true
% 2.46/0.99  --res_lit_sel                           adaptive
% 2.46/0.99  --res_lit_sel_side                      none
% 2.46/0.99  --res_ordering                          kbo
% 2.46/0.99  --res_to_prop_solver                    active
% 2.46/0.99  --res_prop_simpl_new                    false
% 2.46/0.99  --res_prop_simpl_given                  true
% 2.46/0.99  --res_passive_queue_type                priority_queues
% 2.46/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/0.99  --res_passive_queues_freq               [15;5]
% 2.46/0.99  --res_forward_subs                      full
% 2.46/0.99  --res_backward_subs                     full
% 2.46/0.99  --res_forward_subs_resolution           true
% 2.46/0.99  --res_backward_subs_resolution          true
% 2.46/0.99  --res_orphan_elimination                true
% 2.46/0.99  --res_time_limit                        2.
% 2.46/0.99  --res_out_proof                         true
% 2.46/0.99  
% 2.46/0.99  ------ Superposition Options
% 2.46/0.99  
% 2.46/0.99  --superposition_flag                    true
% 2.46/0.99  --sup_passive_queue_type                priority_queues
% 2.46/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.46/0.99  --demod_completeness_check              fast
% 2.46/0.99  --demod_use_ground                      true
% 2.46/0.99  --sup_to_prop_solver                    passive
% 2.46/0.99  --sup_prop_simpl_new                    true
% 2.46/0.99  --sup_prop_simpl_given                  true
% 2.46/0.99  --sup_fun_splitting                     false
% 2.46/0.99  --sup_smt_interval                      50000
% 2.46/0.99  
% 2.46/0.99  ------ Superposition Simplification Setup
% 2.46/0.99  
% 2.46/0.99  --sup_indices_passive                   []
% 2.46/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.99  --sup_full_bw                           [BwDemod]
% 2.46/0.99  --sup_immed_triv                        [TrivRules]
% 2.46/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.99  --sup_immed_bw_main                     []
% 2.46/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.99  
% 2.46/0.99  ------ Combination Options
% 2.46/0.99  
% 2.46/0.99  --comb_res_mult                         3
% 2.46/0.99  --comb_sup_mult                         2
% 2.46/0.99  --comb_inst_mult                        10
% 2.46/0.99  
% 2.46/0.99  ------ Debug Options
% 2.46/0.99  
% 2.46/0.99  --dbg_backtrace                         false
% 2.46/0.99  --dbg_dump_prop_clauses                 false
% 2.46/0.99  --dbg_dump_prop_clauses_file            -
% 2.46/0.99  --dbg_out_stat                          false
% 2.46/0.99  ------ Parsing...
% 2.46/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.46/0.99  ------ Proving...
% 2.46/0.99  ------ Problem Properties 
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  clauses                                 7
% 2.46/0.99  conjectures                             2
% 2.46/0.99  EPR                                     0
% 2.46/0.99  Horn                                    7
% 2.46/0.99  unary                                   2
% 2.46/0.99  binary                                  5
% 2.46/0.99  lits                                    12
% 2.46/0.99  lits eq                                 4
% 2.46/0.99  fd_pure                                 0
% 2.46/0.99  fd_pseudo                               0
% 2.46/0.99  fd_cond                                 0
% 2.46/0.99  fd_pseudo_cond                          0
% 2.46/0.99  AC symbols                              0
% 2.46/0.99  
% 2.46/0.99  ------ Schedule dynamic 5 is on 
% 2.46/0.99  
% 2.46/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  ------ 
% 2.46/0.99  Current options:
% 2.46/0.99  ------ 
% 2.46/0.99  
% 2.46/0.99  ------ Input Options
% 2.46/0.99  
% 2.46/0.99  --out_options                           all
% 2.46/0.99  --tptp_safe_out                         true
% 2.46/0.99  --problem_path                          ""
% 2.46/0.99  --include_path                          ""
% 2.46/0.99  --clausifier                            res/vclausify_rel
% 2.46/0.99  --clausifier_options                    --mode clausify
% 2.46/0.99  --stdin                                 false
% 2.46/0.99  --stats_out                             all
% 2.46/0.99  
% 2.46/0.99  ------ General Options
% 2.46/0.99  
% 2.46/0.99  --fof                                   false
% 2.46/0.99  --time_out_real                         305.
% 2.46/0.99  --time_out_virtual                      -1.
% 2.46/0.99  --symbol_type_check                     false
% 2.46/0.99  --clausify_out                          false
% 2.46/0.99  --sig_cnt_out                           false
% 2.46/0.99  --trig_cnt_out                          false
% 2.46/0.99  --trig_cnt_out_tolerance                1.
% 2.46/0.99  --trig_cnt_out_sk_spl                   false
% 2.46/0.99  --abstr_cl_out                          false
% 2.46/0.99  
% 2.46/0.99  ------ Global Options
% 2.46/0.99  
% 2.46/0.99  --schedule                              default
% 2.46/0.99  --add_important_lit                     false
% 2.46/0.99  --prop_solver_per_cl                    1000
% 2.46/0.99  --min_unsat_core                        false
% 2.46/0.99  --soft_assumptions                      false
% 2.46/0.99  --soft_lemma_size                       3
% 2.46/0.99  --prop_impl_unit_size                   0
% 2.46/0.99  --prop_impl_unit                        []
% 2.46/0.99  --share_sel_clauses                     true
% 2.46/0.99  --reset_solvers                         false
% 2.46/0.99  --bc_imp_inh                            [conj_cone]
% 2.46/0.99  --conj_cone_tolerance                   3.
% 2.46/1.00  --extra_neg_conj                        none
% 2.46/1.00  --large_theory_mode                     true
% 2.46/1.00  --prolific_symb_bound                   200
% 2.46/1.00  --lt_threshold                          2000
% 2.46/1.00  --clause_weak_htbl                      true
% 2.46/1.00  --gc_record_bc_elim                     false
% 2.46/1.00  
% 2.46/1.00  ------ Preprocessing Options
% 2.46/1.00  
% 2.46/1.00  --preprocessing_flag                    true
% 2.46/1.00  --time_out_prep_mult                    0.1
% 2.46/1.00  --splitting_mode                        input
% 2.46/1.00  --splitting_grd                         true
% 2.46/1.00  --splitting_cvd                         false
% 2.46/1.00  --splitting_cvd_svl                     false
% 2.46/1.00  --splitting_nvd                         32
% 2.46/1.00  --sub_typing                            true
% 2.46/1.00  --prep_gs_sim                           true
% 2.46/1.00  --prep_unflatten                        true
% 2.46/1.00  --prep_res_sim                          true
% 2.46/1.00  --prep_upred                            true
% 2.46/1.00  --prep_sem_filter                       exhaustive
% 2.46/1.00  --prep_sem_filter_out                   false
% 2.46/1.00  --pred_elim                             true
% 2.46/1.00  --res_sim_input                         true
% 2.46/1.00  --eq_ax_congr_red                       true
% 2.46/1.00  --pure_diseq_elim                       true
% 2.46/1.00  --brand_transform                       false
% 2.46/1.00  --non_eq_to_eq                          false
% 2.46/1.00  --prep_def_merge                        true
% 2.46/1.00  --prep_def_merge_prop_impl              false
% 2.46/1.00  --prep_def_merge_mbd                    true
% 2.46/1.00  --prep_def_merge_tr_red                 false
% 2.46/1.00  --prep_def_merge_tr_cl                  false
% 2.46/1.00  --smt_preprocessing                     true
% 2.46/1.00  --smt_ac_axioms                         fast
% 2.46/1.00  --preprocessed_out                      false
% 2.46/1.00  --preprocessed_stats                    false
% 2.46/1.00  
% 2.46/1.00  ------ Abstraction refinement Options
% 2.46/1.00  
% 2.46/1.00  --abstr_ref                             []
% 2.46/1.00  --abstr_ref_prep                        false
% 2.46/1.00  --abstr_ref_until_sat                   false
% 2.46/1.00  --abstr_ref_sig_restrict                funpre
% 2.46/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/1.00  --abstr_ref_under                       []
% 2.46/1.00  
% 2.46/1.00  ------ SAT Options
% 2.46/1.00  
% 2.46/1.00  --sat_mode                              false
% 2.46/1.00  --sat_fm_restart_options                ""
% 2.46/1.00  --sat_gr_def                            false
% 2.46/1.00  --sat_epr_types                         true
% 2.46/1.00  --sat_non_cyclic_types                  false
% 2.46/1.00  --sat_finite_models                     false
% 2.46/1.00  --sat_fm_lemmas                         false
% 2.46/1.00  --sat_fm_prep                           false
% 2.46/1.00  --sat_fm_uc_incr                        true
% 2.46/1.00  --sat_out_model                         small
% 2.46/1.00  --sat_out_clauses                       false
% 2.46/1.00  
% 2.46/1.00  ------ QBF Options
% 2.46/1.00  
% 2.46/1.00  --qbf_mode                              false
% 2.46/1.00  --qbf_elim_univ                         false
% 2.46/1.00  --qbf_dom_inst                          none
% 2.46/1.00  --qbf_dom_pre_inst                      false
% 2.46/1.00  --qbf_sk_in                             false
% 2.46/1.00  --qbf_pred_elim                         true
% 2.46/1.00  --qbf_split                             512
% 2.46/1.00  
% 2.46/1.00  ------ BMC1 Options
% 2.46/1.00  
% 2.46/1.00  --bmc1_incremental                      false
% 2.46/1.00  --bmc1_axioms                           reachable_all
% 2.46/1.00  --bmc1_min_bound                        0
% 2.46/1.00  --bmc1_max_bound                        -1
% 2.46/1.00  --bmc1_max_bound_default                -1
% 2.46/1.00  --bmc1_symbol_reachability              true
% 2.46/1.00  --bmc1_property_lemmas                  false
% 2.46/1.00  --bmc1_k_induction                      false
% 2.46/1.00  --bmc1_non_equiv_states                 false
% 2.46/1.00  --bmc1_deadlock                         false
% 2.46/1.00  --bmc1_ucm                              false
% 2.46/1.00  --bmc1_add_unsat_core                   none
% 2.46/1.00  --bmc1_unsat_core_children              false
% 2.46/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/1.00  --bmc1_out_stat                         full
% 2.46/1.00  --bmc1_ground_init                      false
% 2.46/1.00  --bmc1_pre_inst_next_state              false
% 2.46/1.00  --bmc1_pre_inst_state                   false
% 2.46/1.00  --bmc1_pre_inst_reach_state             false
% 2.46/1.00  --bmc1_out_unsat_core                   false
% 2.46/1.00  --bmc1_aig_witness_out                  false
% 2.46/1.00  --bmc1_verbose                          false
% 2.46/1.00  --bmc1_dump_clauses_tptp                false
% 2.46/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.46/1.00  --bmc1_dump_file                        -
% 2.46/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.46/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.46/1.00  --bmc1_ucm_extend_mode                  1
% 2.46/1.00  --bmc1_ucm_init_mode                    2
% 2.46/1.00  --bmc1_ucm_cone_mode                    none
% 2.46/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.46/1.00  --bmc1_ucm_relax_model                  4
% 2.46/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.46/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/1.00  --bmc1_ucm_layered_model                none
% 2.46/1.00  --bmc1_ucm_max_lemma_size               10
% 2.46/1.00  
% 2.46/1.00  ------ AIG Options
% 2.46/1.00  
% 2.46/1.00  --aig_mode                              false
% 2.46/1.00  
% 2.46/1.00  ------ Instantiation Options
% 2.46/1.00  
% 2.46/1.00  --instantiation_flag                    true
% 2.46/1.00  --inst_sos_flag                         false
% 2.46/1.00  --inst_sos_phase                        true
% 2.46/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/1.00  --inst_lit_sel_side                     none
% 2.46/1.00  --inst_solver_per_active                1400
% 2.46/1.00  --inst_solver_calls_frac                1.
% 2.46/1.00  --inst_passive_queue_type               priority_queues
% 2.46/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/1.00  --inst_passive_queues_freq              [25;2]
% 2.46/1.00  --inst_dismatching                      true
% 2.46/1.00  --inst_eager_unprocessed_to_passive     true
% 2.46/1.00  --inst_prop_sim_given                   true
% 2.46/1.00  --inst_prop_sim_new                     false
% 2.46/1.00  --inst_subs_new                         false
% 2.46/1.00  --inst_eq_res_simp                      false
% 2.46/1.00  --inst_subs_given                       false
% 2.46/1.00  --inst_orphan_elimination               true
% 2.46/1.00  --inst_learning_loop_flag               true
% 2.46/1.00  --inst_learning_start                   3000
% 2.46/1.00  --inst_learning_factor                  2
% 2.46/1.00  --inst_start_prop_sim_after_learn       3
% 2.46/1.00  --inst_sel_renew                        solver
% 2.46/1.00  --inst_lit_activity_flag                true
% 2.46/1.00  --inst_restr_to_given                   false
% 2.46/1.00  --inst_activity_threshold               500
% 2.46/1.00  --inst_out_proof                        true
% 2.46/1.00  
% 2.46/1.00  ------ Resolution Options
% 2.46/1.00  
% 2.46/1.00  --resolution_flag                       false
% 2.46/1.00  --res_lit_sel                           adaptive
% 2.46/1.00  --res_lit_sel_side                      none
% 2.46/1.00  --res_ordering                          kbo
% 2.46/1.00  --res_to_prop_solver                    active
% 2.46/1.00  --res_prop_simpl_new                    false
% 2.46/1.00  --res_prop_simpl_given                  true
% 2.46/1.00  --res_passive_queue_type                priority_queues
% 2.46/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/1.00  --res_passive_queues_freq               [15;5]
% 2.46/1.00  --res_forward_subs                      full
% 2.46/1.00  --res_backward_subs                     full
% 2.46/1.00  --res_forward_subs_resolution           true
% 2.46/1.00  --res_backward_subs_resolution          true
% 2.46/1.00  --res_orphan_elimination                true
% 2.46/1.00  --res_time_limit                        2.
% 2.46/1.00  --res_out_proof                         true
% 2.46/1.00  
% 2.46/1.00  ------ Superposition Options
% 2.46/1.00  
% 2.46/1.00  --superposition_flag                    true
% 2.46/1.00  --sup_passive_queue_type                priority_queues
% 2.46/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.46/1.00  --demod_completeness_check              fast
% 2.46/1.00  --demod_use_ground                      true
% 2.46/1.00  --sup_to_prop_solver                    passive
% 2.46/1.00  --sup_prop_simpl_new                    true
% 2.46/1.00  --sup_prop_simpl_given                  true
% 2.46/1.00  --sup_fun_splitting                     false
% 2.46/1.00  --sup_smt_interval                      50000
% 2.46/1.00  
% 2.46/1.00  ------ Superposition Simplification Setup
% 2.46/1.00  
% 2.46/1.00  --sup_indices_passive                   []
% 2.46/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.00  --sup_full_bw                           [BwDemod]
% 2.46/1.00  --sup_immed_triv                        [TrivRules]
% 2.46/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.00  --sup_immed_bw_main                     []
% 2.46/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.00  
% 2.46/1.00  ------ Combination Options
% 2.46/1.00  
% 2.46/1.00  --comb_res_mult                         3
% 2.46/1.00  --comb_sup_mult                         2
% 2.46/1.00  --comb_inst_mult                        10
% 2.46/1.00  
% 2.46/1.00  ------ Debug Options
% 2.46/1.00  
% 2.46/1.00  --dbg_backtrace                         false
% 2.46/1.00  --dbg_dump_prop_clauses                 false
% 2.46/1.00  --dbg_dump_prop_clauses_file            -
% 2.46/1.00  --dbg_out_stat                          false
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  ------ Proving...
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  % SZS status Theorem for theBenchmark.p
% 2.46/1.00  
% 2.46/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.46/1.00  
% 2.46/1.00  fof(f6,conjecture,(
% 2.46/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f7,negated_conjecture,(
% 2.46/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 2.46/1.00    inference(negated_conjecture,[],[f6])).
% 2.46/1.00  
% 2.46/1.00  fof(f14,plain,(
% 2.46/1.00    ? [X0] : (? [X1] : (k2_tops_1(X0,X1) != k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.46/1.00    inference(ennf_transformation,[],[f7])).
% 2.46/1.00  
% 2.46/1.00  fof(f16,plain,(
% 2.46/1.00    ( ! [X0] : (? [X1] : (k2_tops_1(X0,X1) != k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k2_tops_1(X0,sK1) != k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.46/1.00    introduced(choice_axiom,[])).
% 2.46/1.00  
% 2.46/1.00  fof(f15,plain,(
% 2.46/1.00    ? [X0] : (? [X1] : (k2_tops_1(X0,X1) != k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (k2_tops_1(sK0,X1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.46/1.00    introduced(choice_axiom,[])).
% 2.46/1.00  
% 2.46/1.00  fof(f17,plain,(
% 2.46/1.00    (k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.46/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16,f15])).
% 2.46/1.00  
% 2.46/1.00  fof(f24,plain,(
% 2.46/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.46/1.00    inference(cnf_transformation,[],[f17])).
% 2.46/1.00  
% 2.46/1.00  fof(f4,axiom,(
% 2.46/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f11,plain,(
% 2.46/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.46/1.00    inference(ennf_transformation,[],[f4])).
% 2.46/1.00  
% 2.46/1.00  fof(f12,plain,(
% 2.46/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.46/1.00    inference(flattening,[],[f11])).
% 2.46/1.00  
% 2.46/1.00  fof(f21,plain,(
% 2.46/1.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f12])).
% 2.46/1.00  
% 2.46/1.00  fof(f23,plain,(
% 2.46/1.00    l1_pre_topc(sK0)),
% 2.46/1.00    inference(cnf_transformation,[],[f17])).
% 2.46/1.00  
% 2.46/1.00  fof(f3,axiom,(
% 2.46/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f10,plain,(
% 2.46/1.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.46/1.00    inference(ennf_transformation,[],[f3])).
% 2.46/1.00  
% 2.46/1.00  fof(f20,plain,(
% 2.46/1.00    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.46/1.00    inference(cnf_transformation,[],[f10])).
% 2.46/1.00  
% 2.46/1.00  fof(f2,axiom,(
% 2.46/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f9,plain,(
% 2.46/1.00    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.46/1.00    inference(ennf_transformation,[],[f2])).
% 2.46/1.00  
% 2.46/1.00  fof(f19,plain,(
% 2.46/1.00    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.46/1.00    inference(cnf_transformation,[],[f9])).
% 2.46/1.00  
% 2.46/1.00  fof(f1,axiom,(
% 2.46/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f8,plain,(
% 2.46/1.00    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.46/1.00    inference(ennf_transformation,[],[f1])).
% 2.46/1.00  
% 2.46/1.00  fof(f18,plain,(
% 2.46/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.46/1.00    inference(cnf_transformation,[],[f8])).
% 2.46/1.00  
% 2.46/1.00  fof(f5,axiom,(
% 2.46/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)))),
% 2.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/1.00  
% 2.46/1.00  fof(f13,plain,(
% 2.46/1.00    ! [X0] : (! [X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.46/1.00    inference(ennf_transformation,[],[f5])).
% 2.46/1.00  
% 2.46/1.00  fof(f22,plain,(
% 2.46/1.00    ( ! [X0,X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.46/1.00    inference(cnf_transformation,[],[f13])).
% 2.46/1.00  
% 2.46/1.00  fof(f25,plain,(
% 2.46/1.00    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.46/1.00    inference(cnf_transformation,[],[f17])).
% 2.46/1.00  
% 2.46/1.00  cnf(c_6,negated_conjecture,
% 2.46/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.46/1.00      inference(cnf_transformation,[],[f24]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_171,negated_conjecture,
% 2.46/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_314,plain,
% 2.46/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_171]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_3,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/1.00      | ~ l1_pre_topc(X1) ),
% 2.46/1.00      inference(cnf_transformation,[],[f21]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_7,negated_conjecture,
% 2.46/1.00      ( l1_pre_topc(sK0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f23]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_100,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/1.00      | sK0 != X1 ),
% 2.46/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_7]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_101,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.46/1.00      inference(unflattening,[status(thm)],[c_100]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_169,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | m1_subset_1(k2_pre_topc(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_101]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_316,plain,
% 2.46/1.00      ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.46/1.00      | m1_subset_1(k2_pre_topc(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_169]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_2,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.46/1.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 2.46/1.00      inference(cnf_transformation,[],[f20]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_173,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X0_40))
% 2.46/1.00      | k3_subset_1(X0_40,k3_subset_1(X0_40,X0_38)) = X0_38 ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_313,plain,
% 2.46/1.00      ( k3_subset_1(X0_40,k3_subset_1(X0_40,X0_38)) = X0_38
% 2.46/1.00      | m1_subset_1(X0_38,k1_zfmisc_1(X0_40)) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_173]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_570,plain,
% 2.46/1.00      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_38))) = k2_pre_topc(sK0,X0_38)
% 2.46/1.00      | m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_316,c_313]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_808,plain,
% 2.46/1.00      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_314,c_570]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.46/1.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.46/1.00      inference(cnf_transformation,[],[f19]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_174,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X0_40))
% 2.46/1.00      | m1_subset_1(k3_subset_1(X0_40,X0_38),k1_zfmisc_1(X0_40)) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_312,plain,
% 2.46/1.00      ( m1_subset_1(X0_38,k1_zfmisc_1(X0_40)) != iProver_top
% 2.46/1.00      | m1_subset_1(k3_subset_1(X0_40,X0_38),k1_zfmisc_1(X0_40)) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_174]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_828,plain,
% 2.46/1.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.46/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_808,c_312]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_9,plain,
% 2.46/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_207,plain,
% 2.46/1.00      ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.46/1.00      | m1_subset_1(k2_pre_topc(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_169]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_209,plain,
% 2.46/1.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.46/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_207]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_900,plain,
% 2.46/1.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.46/1.00      inference(global_propositional_subsumption,
% 2.46/1.00                [status(thm)],
% 2.46/1.00                [c_828,c_9,c_209]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_0,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.46/1.00      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f18]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_175,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0_38,k1_zfmisc_1(X0_40))
% 2.46/1.00      | k9_subset_1(X0_40,X0_38,X1_38) = k9_subset_1(X0_40,X1_38,X0_38) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_311,plain,
% 2.46/1.00      ( k9_subset_1(X0_40,X0_38,X1_38) = k9_subset_1(X0_40,X1_38,X0_38)
% 2.46/1.00      | m1_subset_1(X0_38,k1_zfmisc_1(X0_40)) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_175]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_910,plain,
% 2.46/1.00      ( k9_subset_1(u1_struct_0(sK0),X0_38,k2_pre_topc(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0_38) ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_900,c_311]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_4,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/1.00      | ~ l1_pre_topc(X1)
% 2.46/1.00      | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
% 2.46/1.00      inference(cnf_transformation,[],[f22]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_88,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.46/1.00      | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0)
% 2.46/1.00      | sK0 != X1 ),
% 2.46/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_7]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_89,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0) ),
% 2.46/1.00      inference(unflattening,[status(thm)],[c_88]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_170,plain,
% 2.46/1.00      ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.46/1.00      | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_38),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_38))) = k2_tops_1(sK0,X0_38) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_89]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_315,plain,
% 2.46/1.00      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_38),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_38))) = k2_tops_1(sK0,X0_38)
% 2.46/1.00      | m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.46/1.00      inference(predicate_to_equality,[status(thm)],[c_170]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_641,plain,
% 2.46/1.00      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_38)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0_38)))) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0_38))
% 2.46/1.00      | m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_312,c_315]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1906,plain,
% 2.46/1.00      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_314,c_641]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_569,plain,
% 2.46/1.00      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_314,c_313]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1922,plain,
% 2.46/1.00      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 2.46/1.00      inference(light_normalisation,[status(thm)],[c_1906,c_569]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1931,plain,
% 2.46/1.00      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_910,c_1922]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_399,plain,
% 2.46/1.00      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
% 2.46/1.00      inference(superposition,[status(thm)],[c_314,c_315]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_1933,plain,
% 2.46/1.00      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
% 2.46/1.00      inference(light_normalisation,[status(thm)],[c_1931,c_399]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_180,plain,
% 2.46/1.00      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 2.46/1.00      theory(equality) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_370,plain,
% 2.46/1.00      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != X0_42
% 2.46/1.00      | k2_tops_1(sK0,sK1) != X0_42
% 2.46/1.00      | k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_180]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_410,plain,
% 2.46/1.00      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_tops_1(sK0,sK1)
% 2.46/1.00      | k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
% 2.46/1.00      | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_370]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_5,negated_conjecture,
% 2.46/1.00      ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 2.46/1.00      inference(cnf_transformation,[],[f25]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_172,negated_conjecture,
% 2.46/1.00      ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 2.46/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_177,plain,( X0_38 = X0_38 ),theory(equality) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_192,plain,
% 2.46/1.00      ( sK1 = sK1 ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_177]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_185,plain,
% 2.46/1.00      ( k2_tops_1(X0_41,X0_38) = k2_tops_1(X0_41,X1_38)
% 2.46/1.00      | X0_38 != X1_38 ),
% 2.46/1.00      theory(equality) ).
% 2.46/1.00  
% 2.46/1.00  cnf(c_190,plain,
% 2.46/1.00      ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,sK1) | sK1 != sK1 ),
% 2.46/1.00      inference(instantiation,[status(thm)],[c_185]) ).
% 2.46/1.00  
% 2.46/1.00  cnf(contradiction,plain,
% 2.46/1.00      ( $false ),
% 2.46/1.00      inference(minisat,[status(thm)],[c_1933,c_410,c_172,c_192,c_190]) ).
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.46/1.00  
% 2.46/1.00  ------                               Statistics
% 2.46/1.00  
% 2.46/1.00  ------ General
% 2.46/1.00  
% 2.46/1.00  abstr_ref_over_cycles:                  0
% 2.46/1.00  abstr_ref_under_cycles:                 0
% 2.46/1.00  gc_basic_clause_elim:                   0
% 2.46/1.00  forced_gc_time:                         0
% 2.46/1.00  parsing_time:                           0.011
% 2.46/1.00  unif_index_cands_time:                  0.
% 2.46/1.00  unif_index_add_time:                    0.
% 2.46/1.00  orderings_time:                         0.
% 2.46/1.00  out_proof_time:                         0.024
% 2.46/1.00  total_time:                             0.105
% 2.46/1.00  num_of_symbols:                         43
% 2.46/1.00  num_of_terms:                           1557
% 2.46/1.00  
% 2.46/1.00  ------ Preprocessing
% 2.46/1.00  
% 2.46/1.00  num_of_splits:                          0
% 2.46/1.00  num_of_split_atoms:                     0
% 2.46/1.00  num_of_reused_defs:                     0
% 2.46/1.00  num_eq_ax_congr_red:                    8
% 2.46/1.00  num_of_sem_filtered_clauses:            1
% 2.46/1.00  num_of_subtypes:                        5
% 2.46/1.00  monotx_restored_types:                  0
% 2.46/1.00  sat_num_of_epr_types:                   0
% 2.46/1.00  sat_num_of_non_cyclic_types:            0
% 2.46/1.00  sat_guarded_non_collapsed_types:        1
% 2.46/1.00  num_pure_diseq_elim:                    0
% 2.46/1.00  simp_replaced_by:                       0
% 2.46/1.00  res_preprocessed:                       48
% 2.46/1.00  prep_upred:                             0
% 2.46/1.00  prep_unflattend:                        2
% 2.46/1.00  smt_new_axioms:                         0
% 2.46/1.00  pred_elim_cands:                        1
% 2.46/1.00  pred_elim:                              1
% 2.46/1.00  pred_elim_cl:                           1
% 2.46/1.00  pred_elim_cycles:                       3
% 2.46/1.00  merged_defs:                            0
% 2.46/1.00  merged_defs_ncl:                        0
% 2.46/1.00  bin_hyper_res:                          0
% 2.46/1.00  prep_cycles:                            4
% 2.46/1.00  pred_elim_time:                         0.
% 2.46/1.00  splitting_time:                         0.
% 2.46/1.00  sem_filter_time:                        0.
% 2.46/1.00  monotx_time:                            0.
% 2.46/1.00  subtype_inf_time:                       0.
% 2.46/1.00  
% 2.46/1.00  ------ Problem properties
% 2.46/1.00  
% 2.46/1.00  clauses:                                7
% 2.46/1.00  conjectures:                            2
% 2.46/1.00  epr:                                    0
% 2.46/1.00  horn:                                   7
% 2.46/1.00  ground:                                 2
% 2.46/1.00  unary:                                  2
% 2.46/1.00  binary:                                 5
% 2.46/1.00  lits:                                   12
% 2.46/1.00  lits_eq:                                4
% 2.46/1.00  fd_pure:                                0
% 2.46/1.00  fd_pseudo:                              0
% 2.46/1.00  fd_cond:                                0
% 2.46/1.00  fd_pseudo_cond:                         0
% 2.46/1.00  ac_symbols:                             0
% 2.46/1.00  
% 2.46/1.00  ------ Propositional Solver
% 2.46/1.00  
% 2.46/1.00  prop_solver_calls:                      28
% 2.46/1.00  prop_fast_solver_calls:                 242
% 2.46/1.00  smt_solver_calls:                       0
% 2.46/1.00  smt_fast_solver_calls:                  0
% 2.46/1.00  prop_num_of_clauses:                    579
% 2.46/1.00  prop_preprocess_simplified:             2010
% 2.46/1.00  prop_fo_subsumed:                       1
% 2.46/1.00  prop_solver_time:                       0.
% 2.46/1.00  smt_solver_time:                        0.
% 2.46/1.00  smt_fast_solver_time:                   0.
% 2.46/1.00  prop_fast_solver_time:                  0.
% 2.46/1.00  prop_unsat_core_time:                   0.
% 2.46/1.00  
% 2.46/1.00  ------ QBF
% 2.46/1.00  
% 2.46/1.00  qbf_q_res:                              0
% 2.46/1.00  qbf_num_tautologies:                    0
% 2.46/1.00  qbf_prep_cycles:                        0
% 2.46/1.00  
% 2.46/1.00  ------ BMC1
% 2.46/1.00  
% 2.46/1.00  bmc1_current_bound:                     -1
% 2.46/1.00  bmc1_last_solved_bound:                 -1
% 2.46/1.00  bmc1_unsat_core_size:                   -1
% 2.46/1.00  bmc1_unsat_core_parents_size:           -1
% 2.46/1.00  bmc1_merge_next_fun:                    0
% 2.46/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.46/1.00  
% 2.46/1.00  ------ Instantiation
% 2.46/1.00  
% 2.46/1.00  inst_num_of_clauses:                    274
% 2.46/1.00  inst_num_in_passive:                    11
% 2.46/1.00  inst_num_in_active:                     156
% 2.46/1.00  inst_num_in_unprocessed:                108
% 2.46/1.00  inst_num_of_loops:                      160
% 2.46/1.00  inst_num_of_learning_restarts:          0
% 2.46/1.00  inst_num_moves_active_passive:          0
% 2.46/1.00  inst_lit_activity:                      0
% 2.46/1.00  inst_lit_activity_moves:                0
% 2.46/1.00  inst_num_tautologies:                   0
% 2.46/1.00  inst_num_prop_implied:                  0
% 2.46/1.00  inst_num_existing_simplified:           0
% 2.46/1.00  inst_num_eq_res_simplified:             0
% 2.46/1.00  inst_num_child_elim:                    0
% 2.46/1.00  inst_num_of_dismatching_blockings:      171
% 2.46/1.00  inst_num_of_non_proper_insts:           363
% 2.46/1.00  inst_num_of_duplicates:                 0
% 2.46/1.00  inst_inst_num_from_inst_to_res:         0
% 2.46/1.00  inst_dismatching_checking_time:         0.
% 2.46/1.00  
% 2.46/1.00  ------ Resolution
% 2.46/1.00  
% 2.46/1.00  res_num_of_clauses:                     0
% 2.46/1.00  res_num_in_passive:                     0
% 2.46/1.00  res_num_in_active:                      0
% 2.46/1.00  res_num_of_loops:                       52
% 2.46/1.00  res_forward_subset_subsumed:            62
% 2.46/1.00  res_backward_subset_subsumed:           4
% 2.46/1.00  res_forward_subsumed:                   0
% 2.46/1.00  res_backward_subsumed:                  0
% 2.46/1.00  res_forward_subsumption_resolution:     0
% 2.46/1.00  res_backward_subsumption_resolution:    0
% 2.46/1.00  res_clause_to_clause_subsumption:       217
% 2.46/1.00  res_orphan_elimination:                 0
% 2.46/1.00  res_tautology_del:                      63
% 2.46/1.00  res_num_eq_res_simplified:              0
% 2.46/1.00  res_num_sel_changes:                    0
% 2.46/1.00  res_moves_from_active_to_pass:          0
% 2.46/1.00  
% 2.46/1.00  ------ Superposition
% 2.46/1.00  
% 2.46/1.00  sup_time_total:                         0.
% 2.46/1.00  sup_time_generating:                    0.
% 2.46/1.00  sup_time_sim_full:                      0.
% 2.46/1.00  sup_time_sim_immed:                     0.
% 2.46/1.00  
% 2.46/1.00  sup_num_of_clauses:                     67
% 2.46/1.00  sup_num_in_active:                      32
% 2.46/1.00  sup_num_in_passive:                     35
% 2.46/1.00  sup_num_of_loops:                       31
% 2.46/1.00  sup_fw_superposition:                   62
% 2.46/1.00  sup_bw_superposition:                   14
% 2.46/1.00  sup_immediate_simplified:               6
% 2.46/1.00  sup_given_eliminated:                   0
% 2.46/1.00  comparisons_done:                       0
% 2.46/1.00  comparisons_avoided:                    0
% 2.46/1.00  
% 2.46/1.00  ------ Simplifications
% 2.46/1.00  
% 2.46/1.00  
% 2.46/1.00  sim_fw_subset_subsumed:                 1
% 2.46/1.00  sim_bw_subset_subsumed:                 0
% 2.46/1.00  sim_fw_subsumed:                        0
% 2.46/1.00  sim_bw_subsumed:                        0
% 2.46/1.00  sim_fw_subsumption_res:                 0
% 2.46/1.00  sim_bw_subsumption_res:                 0
% 2.46/1.00  sim_tautology_del:                      0
% 2.46/1.00  sim_eq_tautology_del:                   2
% 2.46/1.00  sim_eq_res_simp:                        0
% 2.46/1.00  sim_fw_demodulated:                     0
% 2.46/1.00  sim_bw_demodulated:                     0
% 2.46/1.00  sim_light_normalised:                   5
% 2.46/1.00  sim_joinable_taut:                      0
% 2.46/1.00  sim_joinable_simp:                      0
% 2.46/1.00  sim_ac_normalised:                      0
% 2.46/1.00  sim_smt_subsumption:                    0
% 2.46/1.00  
%------------------------------------------------------------------------------
