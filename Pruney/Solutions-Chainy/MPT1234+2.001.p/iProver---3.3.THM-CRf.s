%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:43 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 168 expanded)
%              Number of clauses        :   68 (  80 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  248 ( 430 expanded)
%              Number of equality atoms :   58 (  60 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_tops_1(X0,X1),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_tops_1(X0,X1),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k1_tops_1(X0,sK1),sK1)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_tops_1(X0,X1),X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_tops_1(sK0,X1),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f21,f20])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),X1)
      | ~ r1_tarski(k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ~ r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_315,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(X2_40,X3_40)
    | X2_40 != X0_40
    | X3_40 != X1_40 ),
    theory(equality)).

cnf(c_956,plain,
    ( r1_tarski(X0_40,X1_40)
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X2_40))),X2_40)
    | X1_40 != X2_40
    | X0_40 != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X2_40))) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_8493,plain,
    ( r1_tarski(k1_tops_1(sK0,X0_40),X1_40)
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40))),X0_40)
    | X1_40 != X0_40
    | k1_tops_1(sK0,X0_40) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40))) ),
    inference(instantiation,[status(thm)],[c_956])).

cnf(c_8495,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)
    | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_8493])).

cnf(c_313,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_2325,plain,
    ( X0_40 != X1_40
    | X0_40 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X2_40))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X2_40)) != X1_40 ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_6314,plain,
    ( X0_40 != k1_tops_1(sK0,X1_40)
    | X0_40 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1_40)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1_40))) != k1_tops_1(sK0,X1_40) ),
    inference(instantiation,[status(thm)],[c_2325])).

cnf(c_6884,plain,
    ( k1_tops_1(sK0,X0_40) != k1_tops_1(sK0,X0_40)
    | k1_tops_1(sK0,X0_40) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40))) != k1_tops_1(sK0,X0_40) ),
    inference(instantiation,[status(thm)],[c_6314])).

cnf(c_6886,plain,
    ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_6884])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_307,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | ~ r1_tarski(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1078,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_40,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_2127,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_40),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_40),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_2129,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_2127])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_304,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_611,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | r1_tarski(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_609,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) != iProver_top
    | r1_tarski(X0_40,X1_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_1123,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_609])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_85,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_86,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_85])).

cnf(c_104,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_86])).

cnf(c_303,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40)) = k3_subset_1(X1_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_104])).

cnf(c_612,plain,
    ( k5_xboole_0(X0_40,k3_xboole_0(X0_40,X1_40)) = k3_subset_1(X0_40,X1_40)
    | r1_tarski(X1_40,X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_1713,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_1123,c_612])).

cnf(c_0,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_308,plain,
    ( r1_tarski(k5_xboole_0(X0_40,k3_xboole_0(X0_40,X1_40)),X0_40) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_607,plain,
    ( r1_tarski(k5_xboole_0(X0_40,k3_xboole_0(X0_40,X1_40)),X0_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_1888,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1713,c_607])).

cnf(c_1901,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1888])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_10,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_179,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

cnf(c_180,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_179])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_180])).

cnf(c_1687,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_680,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,X0_40),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,X0_40),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_1070,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_167,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_168,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_167])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0_40,k2_pre_topc(sK0,X0_40)) ),
    inference(subtyping,[status(esa)],[c_168])).

cnf(c_888,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_40),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_40),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40))) ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_894,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(instantiation,[status(thm)],[c_888])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,X0),X2)
    | r1_tarski(k3_subset_1(X1,X2),X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_105,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(k3_subset_1(X1,X2),X0)
    | r1_tarski(k3_subset_1(X1,X0),X2) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_86])).

cnf(c_238,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_239,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_238])).

cnf(c_257,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(k3_subset_1(X1,X2),X0)
    | r1_tarski(k3_subset_1(X1,X0),X2) ),
    inference(bin_hyper_res,[status(thm)],[c_105,c_239])).

cnf(c_299,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | ~ r1_tarski(X2_40,X1_40)
    | ~ r1_tarski(k3_subset_1(X1_40,X2_40),X0_40)
    | r1_tarski(k3_subset_1(X1_40,X0_40),X2_40) ),
    inference(subtyping,[status(esa)],[c_257])).

cnf(c_767,plain,
    ( ~ r1_tarski(X0_40,u1_struct_0(sK0))
    | ~ r1_tarski(k2_pre_topc(sK0,X1_40),u1_struct_0(sK0))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_40),k2_pre_topc(sK0,X1_40))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1_40)),X0_40) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_887,plain,
    ( ~ r1_tarski(X0_40,u1_struct_0(sK0))
    | ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40)),u1_struct_0(sK0))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_40),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40))),X0_40) ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_890,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_887])).

cnf(c_677,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_155,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_10])).

cnf(c_156,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_155])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40))) = k1_tops_1(sK0,X0_40) ),
    inference(subtyping,[status(esa)],[c_156])).

cnf(c_347,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_310,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_329,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_320,plain,
    ( X0_40 != X1_40
    | k1_tops_1(X0_42,X0_40) = k1_tops_1(X0_42,X1_40) ),
    theory(equality)).

cnf(c_327,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_320])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8495,c_6886,c_2129,c_1901,c_1687,c_1070,c_894,c_890,c_677,c_347,c_329,c_327,c_8,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.57/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.00  
% 3.57/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.57/1.00  
% 3.57/1.00  ------  iProver source info
% 3.57/1.00  
% 3.57/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.57/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.57/1.00  git: non_committed_changes: false
% 3.57/1.00  git: last_make_outside_of_git: false
% 3.57/1.00  
% 3.57/1.00  ------ 
% 3.57/1.00  
% 3.57/1.00  ------ Input Options
% 3.57/1.00  
% 3.57/1.00  --out_options                           all
% 3.57/1.00  --tptp_safe_out                         true
% 3.57/1.00  --problem_path                          ""
% 3.57/1.00  --include_path                          ""
% 3.57/1.00  --clausifier                            res/vclausify_rel
% 3.57/1.00  --clausifier_options                    --mode clausify
% 3.57/1.00  --stdin                                 false
% 3.57/1.00  --stats_out                             all
% 3.57/1.00  
% 3.57/1.00  ------ General Options
% 3.57/1.00  
% 3.57/1.00  --fof                                   false
% 3.57/1.00  --time_out_real                         305.
% 3.57/1.00  --time_out_virtual                      -1.
% 3.57/1.00  --symbol_type_check                     false
% 3.57/1.00  --clausify_out                          false
% 3.57/1.00  --sig_cnt_out                           false
% 3.57/1.00  --trig_cnt_out                          false
% 3.57/1.00  --trig_cnt_out_tolerance                1.
% 3.57/1.00  --trig_cnt_out_sk_spl                   false
% 3.57/1.00  --abstr_cl_out                          false
% 3.57/1.00  
% 3.57/1.00  ------ Global Options
% 3.57/1.00  
% 3.57/1.00  --schedule                              default
% 3.57/1.00  --add_important_lit                     false
% 3.57/1.00  --prop_solver_per_cl                    1000
% 3.57/1.00  --min_unsat_core                        false
% 3.57/1.00  --soft_assumptions                      false
% 3.57/1.00  --soft_lemma_size                       3
% 3.57/1.00  --prop_impl_unit_size                   0
% 3.57/1.00  --prop_impl_unit                        []
% 3.57/1.00  --share_sel_clauses                     true
% 3.57/1.00  --reset_solvers                         false
% 3.57/1.00  --bc_imp_inh                            [conj_cone]
% 3.57/1.00  --conj_cone_tolerance                   3.
% 3.57/1.00  --extra_neg_conj                        none
% 3.57/1.00  --large_theory_mode                     true
% 3.57/1.00  --prolific_symb_bound                   200
% 3.57/1.00  --lt_threshold                          2000
% 3.57/1.00  --clause_weak_htbl                      true
% 3.57/1.00  --gc_record_bc_elim                     false
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing Options
% 3.57/1.00  
% 3.57/1.00  --preprocessing_flag                    true
% 3.57/1.00  --time_out_prep_mult                    0.1
% 3.57/1.00  --splitting_mode                        input
% 3.57/1.00  --splitting_grd                         true
% 3.57/1.00  --splitting_cvd                         false
% 3.57/1.00  --splitting_cvd_svl                     false
% 3.57/1.00  --splitting_nvd                         32
% 3.57/1.00  --sub_typing                            true
% 3.57/1.00  --prep_gs_sim                           true
% 3.57/1.00  --prep_unflatten                        true
% 3.57/1.00  --prep_res_sim                          true
% 3.57/1.00  --prep_upred                            true
% 3.57/1.00  --prep_sem_filter                       exhaustive
% 3.57/1.00  --prep_sem_filter_out                   false
% 3.57/1.00  --pred_elim                             true
% 3.57/1.00  --res_sim_input                         true
% 3.57/1.00  --eq_ax_congr_red                       true
% 3.57/1.00  --pure_diseq_elim                       true
% 3.57/1.00  --brand_transform                       false
% 3.57/1.00  --non_eq_to_eq                          false
% 3.57/1.00  --prep_def_merge                        true
% 3.57/1.00  --prep_def_merge_prop_impl              false
% 3.57/1.00  --prep_def_merge_mbd                    true
% 3.57/1.00  --prep_def_merge_tr_red                 false
% 3.57/1.00  --prep_def_merge_tr_cl                  false
% 3.57/1.00  --smt_preprocessing                     true
% 3.57/1.00  --smt_ac_axioms                         fast
% 3.57/1.00  --preprocessed_out                      false
% 3.57/1.00  --preprocessed_stats                    false
% 3.57/1.00  
% 3.57/1.00  ------ Abstraction refinement Options
% 3.57/1.00  
% 3.57/1.00  --abstr_ref                             []
% 3.57/1.00  --abstr_ref_prep                        false
% 3.57/1.00  --abstr_ref_until_sat                   false
% 3.57/1.00  --abstr_ref_sig_restrict                funpre
% 3.57/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/1.00  --abstr_ref_under                       []
% 3.57/1.00  
% 3.57/1.00  ------ SAT Options
% 3.57/1.00  
% 3.57/1.00  --sat_mode                              false
% 3.57/1.00  --sat_fm_restart_options                ""
% 3.57/1.00  --sat_gr_def                            false
% 3.57/1.00  --sat_epr_types                         true
% 3.57/1.00  --sat_non_cyclic_types                  false
% 3.57/1.00  --sat_finite_models                     false
% 3.57/1.00  --sat_fm_lemmas                         false
% 3.57/1.00  --sat_fm_prep                           false
% 3.57/1.00  --sat_fm_uc_incr                        true
% 3.57/1.00  --sat_out_model                         small
% 3.57/1.00  --sat_out_clauses                       false
% 3.57/1.00  
% 3.57/1.00  ------ QBF Options
% 3.57/1.00  
% 3.57/1.00  --qbf_mode                              false
% 3.57/1.00  --qbf_elim_univ                         false
% 3.57/1.00  --qbf_dom_inst                          none
% 3.57/1.00  --qbf_dom_pre_inst                      false
% 3.57/1.00  --qbf_sk_in                             false
% 3.57/1.00  --qbf_pred_elim                         true
% 3.57/1.00  --qbf_split                             512
% 3.57/1.00  
% 3.57/1.00  ------ BMC1 Options
% 3.57/1.00  
% 3.57/1.00  --bmc1_incremental                      false
% 3.57/1.00  --bmc1_axioms                           reachable_all
% 3.57/1.00  --bmc1_min_bound                        0
% 3.57/1.00  --bmc1_max_bound                        -1
% 3.57/1.00  --bmc1_max_bound_default                -1
% 3.57/1.00  --bmc1_symbol_reachability              true
% 3.57/1.00  --bmc1_property_lemmas                  false
% 3.57/1.00  --bmc1_k_induction                      false
% 3.57/1.00  --bmc1_non_equiv_states                 false
% 3.57/1.00  --bmc1_deadlock                         false
% 3.57/1.00  --bmc1_ucm                              false
% 3.57/1.00  --bmc1_add_unsat_core                   none
% 3.57/1.00  --bmc1_unsat_core_children              false
% 3.57/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/1.00  --bmc1_out_stat                         full
% 3.57/1.00  --bmc1_ground_init                      false
% 3.57/1.00  --bmc1_pre_inst_next_state              false
% 3.57/1.00  --bmc1_pre_inst_state                   false
% 3.57/1.00  --bmc1_pre_inst_reach_state             false
% 3.57/1.00  --bmc1_out_unsat_core                   false
% 3.57/1.00  --bmc1_aig_witness_out                  false
% 3.57/1.00  --bmc1_verbose                          false
% 3.57/1.00  --bmc1_dump_clauses_tptp                false
% 3.57/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.57/1.00  --bmc1_dump_file                        -
% 3.57/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.57/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.57/1.00  --bmc1_ucm_extend_mode                  1
% 3.57/1.00  --bmc1_ucm_init_mode                    2
% 3.57/1.00  --bmc1_ucm_cone_mode                    none
% 3.57/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.57/1.00  --bmc1_ucm_relax_model                  4
% 3.57/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.57/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/1.00  --bmc1_ucm_layered_model                none
% 3.57/1.00  --bmc1_ucm_max_lemma_size               10
% 3.57/1.00  
% 3.57/1.00  ------ AIG Options
% 3.57/1.00  
% 3.57/1.00  --aig_mode                              false
% 3.57/1.00  
% 3.57/1.00  ------ Instantiation Options
% 3.57/1.00  
% 3.57/1.00  --instantiation_flag                    true
% 3.57/1.00  --inst_sos_flag                         false
% 3.57/1.00  --inst_sos_phase                        true
% 3.57/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/1.00  --inst_lit_sel_side                     num_symb
% 3.57/1.00  --inst_solver_per_active                1400
% 3.57/1.00  --inst_solver_calls_frac                1.
% 3.57/1.00  --inst_passive_queue_type               priority_queues
% 3.57/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/1.00  --inst_passive_queues_freq              [25;2]
% 3.57/1.00  --inst_dismatching                      true
% 3.57/1.00  --inst_eager_unprocessed_to_passive     true
% 3.57/1.00  --inst_prop_sim_given                   true
% 3.57/1.00  --inst_prop_sim_new                     false
% 3.57/1.00  --inst_subs_new                         false
% 3.57/1.00  --inst_eq_res_simp                      false
% 3.57/1.00  --inst_subs_given                       false
% 3.57/1.00  --inst_orphan_elimination               true
% 3.57/1.00  --inst_learning_loop_flag               true
% 3.57/1.00  --inst_learning_start                   3000
% 3.57/1.00  --inst_learning_factor                  2
% 3.57/1.00  --inst_start_prop_sim_after_learn       3
% 3.57/1.00  --inst_sel_renew                        solver
% 3.57/1.00  --inst_lit_activity_flag                true
% 3.57/1.00  --inst_restr_to_given                   false
% 3.57/1.00  --inst_activity_threshold               500
% 3.57/1.00  --inst_out_proof                        true
% 3.57/1.00  
% 3.57/1.00  ------ Resolution Options
% 3.57/1.00  
% 3.57/1.00  --resolution_flag                       true
% 3.57/1.00  --res_lit_sel                           adaptive
% 3.57/1.00  --res_lit_sel_side                      none
% 3.57/1.00  --res_ordering                          kbo
% 3.57/1.00  --res_to_prop_solver                    active
% 3.57/1.00  --res_prop_simpl_new                    false
% 3.57/1.00  --res_prop_simpl_given                  true
% 3.57/1.00  --res_passive_queue_type                priority_queues
% 3.57/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/1.00  --res_passive_queues_freq               [15;5]
% 3.57/1.00  --res_forward_subs                      full
% 3.57/1.00  --res_backward_subs                     full
% 3.57/1.00  --res_forward_subs_resolution           true
% 3.57/1.00  --res_backward_subs_resolution          true
% 3.57/1.00  --res_orphan_elimination                true
% 3.57/1.00  --res_time_limit                        2.
% 3.57/1.00  --res_out_proof                         true
% 3.57/1.00  
% 3.57/1.00  ------ Superposition Options
% 3.57/1.00  
% 3.57/1.00  --superposition_flag                    true
% 3.57/1.00  --sup_passive_queue_type                priority_queues
% 3.57/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.57/1.00  --demod_completeness_check              fast
% 3.57/1.00  --demod_use_ground                      true
% 3.57/1.00  --sup_to_prop_solver                    passive
% 3.57/1.00  --sup_prop_simpl_new                    true
% 3.57/1.00  --sup_prop_simpl_given                  true
% 3.57/1.00  --sup_fun_splitting                     false
% 3.57/1.00  --sup_smt_interval                      50000
% 3.57/1.00  
% 3.57/1.00  ------ Superposition Simplification Setup
% 3.57/1.00  
% 3.57/1.00  --sup_indices_passive                   []
% 3.57/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/1.00  --sup_full_bw                           [BwDemod]
% 3.57/1.00  --sup_immed_triv                        [TrivRules]
% 3.57/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/1.00  --sup_immed_bw_main                     []
% 3.57/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/1.00  
% 3.57/1.00  ------ Combination Options
% 3.57/1.00  
% 3.57/1.00  --comb_res_mult                         3
% 3.57/1.00  --comb_sup_mult                         2
% 3.57/1.00  --comb_inst_mult                        10
% 3.57/1.00  
% 3.57/1.00  ------ Debug Options
% 3.57/1.00  
% 3.57/1.00  --dbg_backtrace                         false
% 3.57/1.00  --dbg_dump_prop_clauses                 false
% 3.57/1.00  --dbg_dump_prop_clauses_file            -
% 3.57/1.00  --dbg_out_stat                          false
% 3.57/1.00  ------ Parsing...
% 3.57/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.57/1.00  ------ Proving...
% 3.57/1.00  ------ Problem Properties 
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  clauses                                 10
% 3.57/1.00  conjectures                             2
% 3.57/1.00  EPR                                     0
% 3.57/1.00  Horn                                    10
% 3.57/1.00  unary                                   3
% 3.57/1.00  binary                                  6
% 3.57/1.00  lits                                    19
% 3.57/1.00  lits eq                                 2
% 3.57/1.00  fd_pure                                 0
% 3.57/1.00  fd_pseudo                               0
% 3.57/1.00  fd_cond                                 0
% 3.57/1.00  fd_pseudo_cond                          0
% 3.57/1.00  AC symbols                              0
% 3.57/1.00  
% 3.57/1.00  ------ Schedule dynamic 5 is on 
% 3.57/1.00  
% 3.57/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  ------ 
% 3.57/1.00  Current options:
% 3.57/1.00  ------ 
% 3.57/1.00  
% 3.57/1.00  ------ Input Options
% 3.57/1.00  
% 3.57/1.00  --out_options                           all
% 3.57/1.00  --tptp_safe_out                         true
% 3.57/1.00  --problem_path                          ""
% 3.57/1.00  --include_path                          ""
% 3.57/1.00  --clausifier                            res/vclausify_rel
% 3.57/1.00  --clausifier_options                    --mode clausify
% 3.57/1.00  --stdin                                 false
% 3.57/1.00  --stats_out                             all
% 3.57/1.00  
% 3.57/1.00  ------ General Options
% 3.57/1.00  
% 3.57/1.00  --fof                                   false
% 3.57/1.00  --time_out_real                         305.
% 3.57/1.00  --time_out_virtual                      -1.
% 3.57/1.00  --symbol_type_check                     false
% 3.57/1.00  --clausify_out                          false
% 3.57/1.00  --sig_cnt_out                           false
% 3.57/1.00  --trig_cnt_out                          false
% 3.57/1.00  --trig_cnt_out_tolerance                1.
% 3.57/1.00  --trig_cnt_out_sk_spl                   false
% 3.57/1.00  --abstr_cl_out                          false
% 3.57/1.00  
% 3.57/1.00  ------ Global Options
% 3.57/1.00  
% 3.57/1.00  --schedule                              default
% 3.57/1.00  --add_important_lit                     false
% 3.57/1.00  --prop_solver_per_cl                    1000
% 3.57/1.00  --min_unsat_core                        false
% 3.57/1.00  --soft_assumptions                      false
% 3.57/1.00  --soft_lemma_size                       3
% 3.57/1.00  --prop_impl_unit_size                   0
% 3.57/1.00  --prop_impl_unit                        []
% 3.57/1.00  --share_sel_clauses                     true
% 3.57/1.00  --reset_solvers                         false
% 3.57/1.00  --bc_imp_inh                            [conj_cone]
% 3.57/1.00  --conj_cone_tolerance                   3.
% 3.57/1.00  --extra_neg_conj                        none
% 3.57/1.00  --large_theory_mode                     true
% 3.57/1.00  --prolific_symb_bound                   200
% 3.57/1.00  --lt_threshold                          2000
% 3.57/1.00  --clause_weak_htbl                      true
% 3.57/1.00  --gc_record_bc_elim                     false
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing Options
% 3.57/1.00  
% 3.57/1.00  --preprocessing_flag                    true
% 3.57/1.00  --time_out_prep_mult                    0.1
% 3.57/1.00  --splitting_mode                        input
% 3.57/1.00  --splitting_grd                         true
% 3.57/1.00  --splitting_cvd                         false
% 3.57/1.00  --splitting_cvd_svl                     false
% 3.57/1.00  --splitting_nvd                         32
% 3.57/1.00  --sub_typing                            true
% 3.57/1.00  --prep_gs_sim                           true
% 3.57/1.00  --prep_unflatten                        true
% 3.57/1.00  --prep_res_sim                          true
% 3.57/1.00  --prep_upred                            true
% 3.57/1.00  --prep_sem_filter                       exhaustive
% 3.57/1.00  --prep_sem_filter_out                   false
% 3.57/1.00  --pred_elim                             true
% 3.57/1.00  --res_sim_input                         true
% 3.57/1.00  --eq_ax_congr_red                       true
% 3.57/1.00  --pure_diseq_elim                       true
% 3.57/1.00  --brand_transform                       false
% 3.57/1.00  --non_eq_to_eq                          false
% 3.57/1.00  --prep_def_merge                        true
% 3.57/1.00  --prep_def_merge_prop_impl              false
% 3.57/1.00  --prep_def_merge_mbd                    true
% 3.57/1.00  --prep_def_merge_tr_red                 false
% 3.57/1.00  --prep_def_merge_tr_cl                  false
% 3.57/1.00  --smt_preprocessing                     true
% 3.57/1.00  --smt_ac_axioms                         fast
% 3.57/1.00  --preprocessed_out                      false
% 3.57/1.00  --preprocessed_stats                    false
% 3.57/1.00  
% 3.57/1.00  ------ Abstraction refinement Options
% 3.57/1.00  
% 3.57/1.00  --abstr_ref                             []
% 3.57/1.00  --abstr_ref_prep                        false
% 3.57/1.00  --abstr_ref_until_sat                   false
% 3.57/1.00  --abstr_ref_sig_restrict                funpre
% 3.57/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/1.00  --abstr_ref_under                       []
% 3.57/1.00  
% 3.57/1.00  ------ SAT Options
% 3.57/1.00  
% 3.57/1.00  --sat_mode                              false
% 3.57/1.00  --sat_fm_restart_options                ""
% 3.57/1.00  --sat_gr_def                            false
% 3.57/1.00  --sat_epr_types                         true
% 3.57/1.00  --sat_non_cyclic_types                  false
% 3.57/1.00  --sat_finite_models                     false
% 3.57/1.00  --sat_fm_lemmas                         false
% 3.57/1.00  --sat_fm_prep                           false
% 3.57/1.00  --sat_fm_uc_incr                        true
% 3.57/1.00  --sat_out_model                         small
% 3.57/1.00  --sat_out_clauses                       false
% 3.57/1.00  
% 3.57/1.00  ------ QBF Options
% 3.57/1.00  
% 3.57/1.00  --qbf_mode                              false
% 3.57/1.00  --qbf_elim_univ                         false
% 3.57/1.00  --qbf_dom_inst                          none
% 3.57/1.00  --qbf_dom_pre_inst                      false
% 3.57/1.00  --qbf_sk_in                             false
% 3.57/1.00  --qbf_pred_elim                         true
% 3.57/1.00  --qbf_split                             512
% 3.57/1.00  
% 3.57/1.00  ------ BMC1 Options
% 3.57/1.00  
% 3.57/1.00  --bmc1_incremental                      false
% 3.57/1.00  --bmc1_axioms                           reachable_all
% 3.57/1.00  --bmc1_min_bound                        0
% 3.57/1.00  --bmc1_max_bound                        -1
% 3.57/1.00  --bmc1_max_bound_default                -1
% 3.57/1.00  --bmc1_symbol_reachability              true
% 3.57/1.00  --bmc1_property_lemmas                  false
% 3.57/1.00  --bmc1_k_induction                      false
% 3.57/1.00  --bmc1_non_equiv_states                 false
% 3.57/1.00  --bmc1_deadlock                         false
% 3.57/1.00  --bmc1_ucm                              false
% 3.57/1.00  --bmc1_add_unsat_core                   none
% 3.57/1.00  --bmc1_unsat_core_children              false
% 3.57/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/1.00  --bmc1_out_stat                         full
% 3.57/1.00  --bmc1_ground_init                      false
% 3.57/1.00  --bmc1_pre_inst_next_state              false
% 3.57/1.00  --bmc1_pre_inst_state                   false
% 3.57/1.00  --bmc1_pre_inst_reach_state             false
% 3.57/1.00  --bmc1_out_unsat_core                   false
% 3.57/1.00  --bmc1_aig_witness_out                  false
% 3.57/1.00  --bmc1_verbose                          false
% 3.57/1.00  --bmc1_dump_clauses_tptp                false
% 3.57/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.57/1.00  --bmc1_dump_file                        -
% 3.57/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.57/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.57/1.00  --bmc1_ucm_extend_mode                  1
% 3.57/1.00  --bmc1_ucm_init_mode                    2
% 3.57/1.00  --bmc1_ucm_cone_mode                    none
% 3.57/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.57/1.00  --bmc1_ucm_relax_model                  4
% 3.57/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.57/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/1.00  --bmc1_ucm_layered_model                none
% 3.57/1.00  --bmc1_ucm_max_lemma_size               10
% 3.57/1.00  
% 3.57/1.00  ------ AIG Options
% 3.57/1.00  
% 3.57/1.00  --aig_mode                              false
% 3.57/1.00  
% 3.57/1.00  ------ Instantiation Options
% 3.57/1.00  
% 3.57/1.00  --instantiation_flag                    true
% 3.57/1.00  --inst_sos_flag                         false
% 3.57/1.00  --inst_sos_phase                        true
% 3.57/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/1.00  --inst_lit_sel_side                     none
% 3.57/1.00  --inst_solver_per_active                1400
% 3.57/1.00  --inst_solver_calls_frac                1.
% 3.57/1.00  --inst_passive_queue_type               priority_queues
% 3.57/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/1.00  --inst_passive_queues_freq              [25;2]
% 3.57/1.00  --inst_dismatching                      true
% 3.57/1.00  --inst_eager_unprocessed_to_passive     true
% 3.57/1.00  --inst_prop_sim_given                   true
% 3.57/1.00  --inst_prop_sim_new                     false
% 3.57/1.00  --inst_subs_new                         false
% 3.57/1.00  --inst_eq_res_simp                      false
% 3.57/1.00  --inst_subs_given                       false
% 3.57/1.00  --inst_orphan_elimination               true
% 3.57/1.00  --inst_learning_loop_flag               true
% 3.57/1.00  --inst_learning_start                   3000
% 3.57/1.00  --inst_learning_factor                  2
% 3.57/1.00  --inst_start_prop_sim_after_learn       3
% 3.57/1.00  --inst_sel_renew                        solver
% 3.57/1.00  --inst_lit_activity_flag                true
% 3.57/1.00  --inst_restr_to_given                   false
% 3.57/1.00  --inst_activity_threshold               500
% 3.57/1.00  --inst_out_proof                        true
% 3.57/1.00  
% 3.57/1.00  ------ Resolution Options
% 3.57/1.00  
% 3.57/1.00  --resolution_flag                       false
% 3.57/1.00  --res_lit_sel                           adaptive
% 3.57/1.00  --res_lit_sel_side                      none
% 3.57/1.00  --res_ordering                          kbo
% 3.57/1.00  --res_to_prop_solver                    active
% 3.57/1.00  --res_prop_simpl_new                    false
% 3.57/1.00  --res_prop_simpl_given                  true
% 3.57/1.00  --res_passive_queue_type                priority_queues
% 3.57/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/1.00  --res_passive_queues_freq               [15;5]
% 3.57/1.00  --res_forward_subs                      full
% 3.57/1.00  --res_backward_subs                     full
% 3.57/1.00  --res_forward_subs_resolution           true
% 3.57/1.00  --res_backward_subs_resolution          true
% 3.57/1.00  --res_orphan_elimination                true
% 3.57/1.00  --res_time_limit                        2.
% 3.57/1.00  --res_out_proof                         true
% 3.57/1.00  
% 3.57/1.00  ------ Superposition Options
% 3.57/1.00  
% 3.57/1.00  --superposition_flag                    true
% 3.57/1.00  --sup_passive_queue_type                priority_queues
% 3.57/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.57/1.00  --demod_completeness_check              fast
% 3.57/1.00  --demod_use_ground                      true
% 3.57/1.00  --sup_to_prop_solver                    passive
% 3.57/1.00  --sup_prop_simpl_new                    true
% 3.57/1.00  --sup_prop_simpl_given                  true
% 3.57/1.00  --sup_fun_splitting                     false
% 3.57/1.00  --sup_smt_interval                      50000
% 3.57/1.00  
% 3.57/1.00  ------ Superposition Simplification Setup
% 3.57/1.00  
% 3.57/1.00  --sup_indices_passive                   []
% 3.57/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/1.00  --sup_full_bw                           [BwDemod]
% 3.57/1.00  --sup_immed_triv                        [TrivRules]
% 3.57/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/1.00  --sup_immed_bw_main                     []
% 3.57/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/1.00  
% 3.57/1.00  ------ Combination Options
% 3.57/1.00  
% 3.57/1.00  --comb_res_mult                         3
% 3.57/1.00  --comb_sup_mult                         2
% 3.57/1.00  --comb_inst_mult                        10
% 3.57/1.00  
% 3.57/1.00  ------ Debug Options
% 3.57/1.00  
% 3.57/1.00  --dbg_backtrace                         false
% 3.57/1.00  --dbg_dump_prop_clauses                 false
% 3.57/1.00  --dbg_dump_prop_clauses_file            -
% 3.57/1.00  --dbg_out_stat                          false
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  ------ Proving...
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  % SZS status Theorem for theBenchmark.p
% 3.57/1.00  
% 3.57/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.57/1.00  
% 3.57/1.00  fof(f5,axiom,(
% 3.57/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f19,plain,(
% 3.57/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.57/1.00    inference(nnf_transformation,[],[f5])).
% 3.57/1.00  
% 3.57/1.00  fof(f28,plain,(
% 3.57/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f19])).
% 3.57/1.00  
% 3.57/1.00  fof(f9,conjecture,(
% 3.57/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f10,negated_conjecture,(
% 3.57/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.57/1.00    inference(negated_conjecture,[],[f9])).
% 3.57/1.00  
% 3.57/1.00  fof(f18,plain,(
% 3.57/1.00    ? [X0] : (? [X1] : (~r1_tarski(k1_tops_1(X0,X1),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.57/1.00    inference(ennf_transformation,[],[f10])).
% 3.57/1.00  
% 3.57/1.00  fof(f21,plain,(
% 3.57/1.00    ( ! [X0] : (? [X1] : (~r1_tarski(k1_tops_1(X0,X1),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k1_tops_1(X0,sK1),sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.57/1.00    introduced(choice_axiom,[])).
% 3.57/1.00  
% 3.57/1.00  fof(f20,plain,(
% 3.57/1.00    ? [X0] : (? [X1] : (~r1_tarski(k1_tops_1(X0,X1),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k1_tops_1(sK0,X1),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.57/1.00    introduced(choice_axiom,[])).
% 3.57/1.00  
% 3.57/1.00  fof(f22,plain,(
% 3.57/1.00    (~r1_tarski(k1_tops_1(sK0,sK1),sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.57/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f21,f20])).
% 3.57/1.00  
% 3.57/1.00  fof(f33,plain,(
% 3.57/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.57/1.00    inference(cnf_transformation,[],[f22])).
% 3.57/1.00  
% 3.57/1.00  fof(f27,plain,(
% 3.57/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.57/1.00    inference(cnf_transformation,[],[f19])).
% 3.57/1.00  
% 3.57/1.00  fof(f3,axiom,(
% 3.57/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f11,plain,(
% 3.57/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.57/1.00    inference(ennf_transformation,[],[f3])).
% 3.57/1.00  
% 3.57/1.00  fof(f25,plain,(
% 3.57/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.57/1.00    inference(cnf_transformation,[],[f11])).
% 3.57/1.00  
% 3.57/1.00  fof(f1,axiom,(
% 3.57/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f23,plain,(
% 3.57/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.57/1.00    inference(cnf_transformation,[],[f1])).
% 3.57/1.00  
% 3.57/1.00  fof(f36,plain,(
% 3.57/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.57/1.00    inference(definition_unfolding,[],[f25,f23])).
% 3.57/1.00  
% 3.57/1.00  fof(f2,axiom,(
% 3.57/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f24,plain,(
% 3.57/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f2])).
% 3.57/1.00  
% 3.57/1.00  fof(f35,plain,(
% 3.57/1.00    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.57/1.00    inference(definition_unfolding,[],[f24,f23])).
% 3.57/1.00  
% 3.57/1.00  fof(f6,axiom,(
% 3.57/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f14,plain,(
% 3.57/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.57/1.00    inference(ennf_transformation,[],[f6])).
% 3.57/1.00  
% 3.57/1.00  fof(f15,plain,(
% 3.57/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.57/1.00    inference(flattening,[],[f14])).
% 3.57/1.00  
% 3.57/1.00  fof(f29,plain,(
% 3.57/1.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f15])).
% 3.57/1.00  
% 3.57/1.00  fof(f32,plain,(
% 3.57/1.00    l1_pre_topc(sK0)),
% 3.57/1.00    inference(cnf_transformation,[],[f22])).
% 3.57/1.00  
% 3.57/1.00  fof(f7,axiom,(
% 3.57/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f16,plain,(
% 3.57/1.00    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/1.00    inference(ennf_transformation,[],[f7])).
% 3.57/1.00  
% 3.57/1.00  fof(f30,plain,(
% 3.57/1.00    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f16])).
% 3.57/1.00  
% 3.57/1.00  fof(f4,axiom,(
% 3.57/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f12,plain,(
% 3.57/1.00    ! [X0,X1] : (! [X2] : ((r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.57/1.00    inference(ennf_transformation,[],[f4])).
% 3.57/1.00  
% 3.57/1.00  fof(f13,plain,(
% 3.57/1.00    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.57/1.00    inference(flattening,[],[f12])).
% 3.57/1.00  
% 3.57/1.00  fof(f26,plain,(
% 3.57/1.00    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.57/1.00    inference(cnf_transformation,[],[f13])).
% 3.57/1.00  
% 3.57/1.00  fof(f8,axiom,(
% 3.57/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f17,plain,(
% 3.57/1.00    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/1.00    inference(ennf_transformation,[],[f8])).
% 3.57/1.00  
% 3.57/1.00  fof(f31,plain,(
% 3.57/1.00    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f17])).
% 3.57/1.00  
% 3.57/1.00  fof(f34,plain,(
% 3.57/1.00    ~r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.57/1.00    inference(cnf_transformation,[],[f22])).
% 3.57/1.00  
% 3.57/1.00  cnf(c_315,plain,
% 3.57/1.00      ( ~ r1_tarski(X0_40,X1_40)
% 3.57/1.00      | r1_tarski(X2_40,X3_40)
% 3.57/1.00      | X2_40 != X0_40
% 3.57/1.00      | X3_40 != X1_40 ),
% 3.57/1.00      theory(equality) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_956,plain,
% 3.57/1.00      ( r1_tarski(X0_40,X1_40)
% 3.57/1.00      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X2_40))),X2_40)
% 3.57/1.00      | X1_40 != X2_40
% 3.57/1.00      | X0_40 != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X2_40))) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_315]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_8493,plain,
% 3.57/1.00      ( r1_tarski(k1_tops_1(sK0,X0_40),X1_40)
% 3.57/1.00      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40))),X0_40)
% 3.57/1.00      | X1_40 != X0_40
% 3.57/1.00      | k1_tops_1(sK0,X0_40) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40))) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_956]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_8495,plain,
% 3.57/1.00      ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 3.57/1.00      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)
% 3.57/1.00      | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
% 3.57/1.00      | sK1 != sK1 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_8493]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_313,plain,
% 3.57/1.00      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 3.57/1.00      theory(equality) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2325,plain,
% 3.57/1.00      ( X0_40 != X1_40
% 3.57/1.00      | X0_40 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X2_40))
% 3.57/1.00      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X2_40)) != X1_40 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_313]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6314,plain,
% 3.57/1.00      ( X0_40 != k1_tops_1(sK0,X1_40)
% 3.57/1.00      | X0_40 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1_40)))
% 3.57/1.00      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1_40))) != k1_tops_1(sK0,X1_40) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_2325]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6884,plain,
% 3.57/1.00      ( k1_tops_1(sK0,X0_40) != k1_tops_1(sK0,X0_40)
% 3.57/1.00      | k1_tops_1(sK0,X0_40) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40)))
% 3.57/1.00      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40))) != k1_tops_1(sK0,X0_40) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_6314]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6886,plain,
% 3.57/1.00      ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
% 3.57/1.00      | k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
% 3.57/1.00      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k1_tops_1(sK0,sK1) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_6884]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3,plain,
% 3.57/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.57/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_307,plain,
% 3.57/1.00      ( m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
% 3.57/1.00      | ~ r1_tarski(X0_40,X1_40) ),
% 3.57/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1078,plain,
% 3.57/1.00      ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.57/1.00      | ~ r1_tarski(X0_40,u1_struct_0(sK0)) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_307]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2127,plain,
% 3.57/1.00      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_40),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.57/1.00      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_40),u1_struct_0(sK0)) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_1078]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2129,plain,
% 3.57/1.00      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.57/1.00      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_2127]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_9,negated_conjecture,
% 3.57/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.57/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_304,negated_conjecture,
% 3.57/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.57/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_611,plain,
% 3.57/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.57/1.00      inference(cnf_transformation,[],[f27]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_306,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
% 3.57/1.00      | r1_tarski(X0_40,X1_40) ),
% 3.57/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_609,plain,
% 3.57/1.00      ( m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) != iProver_top
% 3.57/1.00      | r1_tarski(X0_40,X1_40) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1123,plain,
% 3.57/1.00      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_611,c_609]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.57/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_85,plain,
% 3.57/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.57/1.00      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_86,plain,
% 3.57/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.57/1.00      inference(renaming,[status(thm)],[c_85]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_104,plain,
% 3.57/1.00      ( ~ r1_tarski(X0,X1)
% 3.57/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.57/1.00      inference(bin_hyper_res,[status(thm)],[c_1,c_86]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_303,plain,
% 3.57/1.00      ( ~ r1_tarski(X0_40,X1_40)
% 3.57/1.00      | k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40)) = k3_subset_1(X1_40,X0_40) ),
% 3.57/1.00      inference(subtyping,[status(esa)],[c_104]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_612,plain,
% 3.57/1.00      ( k5_xboole_0(X0_40,k3_xboole_0(X0_40,X1_40)) = k3_subset_1(X0_40,X1_40)
% 3.57/1.00      | r1_tarski(X1_40,X0_40) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_303]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1713,plain,
% 3.57/1.00      ( k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1) ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1123,c_612]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_0,plain,
% 3.57/1.00      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_308,plain,
% 3.57/1.00      ( r1_tarski(k5_xboole_0(X0_40,k3_xboole_0(X0_40,X1_40)),X0_40) ),
% 3.57/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_607,plain,
% 3.57/1.00      ( r1_tarski(k5_xboole_0(X0_40,k3_xboole_0(X0_40,X1_40)),X0_40) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1888,plain,
% 3.57/1.00      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1713,c_607]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1901,plain,
% 3.57/1.00      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
% 3.57/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1888]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_5,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/1.00      | ~ l1_pre_topc(X1) ),
% 3.57/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_10,negated_conjecture,
% 3.57/1.00      ( l1_pre_topc(sK0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_179,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/1.00      | sK0 != X1 ),
% 3.57/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_10]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_180,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.57/1.00      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.57/1.00      inference(unflattening,[status(thm)],[c_179]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_300,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.57/1.00      | m1_subset_1(k2_pre_topc(sK0,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.57/1.00      inference(subtyping,[status(esa)],[c_180]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1687,plain,
% 3.57/1.00      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.57/1.00      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_300]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_680,plain,
% 3.57/1.00      ( ~ m1_subset_1(k2_pre_topc(sK0,X0_40),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.57/1.00      | r1_tarski(k2_pre_topc(sK0,X0_40),u1_struct_0(sK0)) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_306]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1070,plain,
% 3.57/1.00      ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.57/1.00      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_680]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/1.00      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.57/1.00      | ~ l1_pre_topc(X1) ),
% 3.57/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_167,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/1.00      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.57/1.00      | sK0 != X1 ),
% 3.57/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_10]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_168,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.57/1.00      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 3.57/1.00      inference(unflattening,[status(thm)],[c_167]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_301,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.57/1.00      | r1_tarski(X0_40,k2_pre_topc(sK0,X0_40)) ),
% 3.57/1.00      inference(subtyping,[status(esa)],[c_168]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_888,plain,
% 3.57/1.00      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_40),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.57/1.00      | r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_40),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40))) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_301]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_894,plain,
% 3.57/1.00      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.57/1.00      | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_888]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.57/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.57/1.00      | ~ r1_tarski(k3_subset_1(X1,X0),X2)
% 3.57/1.00      | r1_tarski(k3_subset_1(X1,X2),X0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f26]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_105,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.57/1.00      | ~ r1_tarski(X2,X1)
% 3.57/1.00      | ~ r1_tarski(k3_subset_1(X1,X2),X0)
% 3.57/1.00      | r1_tarski(k3_subset_1(X1,X0),X2) ),
% 3.57/1.00      inference(bin_hyper_res,[status(thm)],[c_2,c_86]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_238,plain,
% 3.57/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.57/1.00      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_239,plain,
% 3.57/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.57/1.00      inference(renaming,[status(thm)],[c_238]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_257,plain,
% 3.57/1.00      ( ~ r1_tarski(X0,X1)
% 3.57/1.00      | ~ r1_tarski(X2,X1)
% 3.57/1.00      | ~ r1_tarski(k3_subset_1(X1,X2),X0)
% 3.57/1.00      | r1_tarski(k3_subset_1(X1,X0),X2) ),
% 3.57/1.00      inference(bin_hyper_res,[status(thm)],[c_105,c_239]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_299,plain,
% 3.57/1.00      ( ~ r1_tarski(X0_40,X1_40)
% 3.57/1.00      | ~ r1_tarski(X2_40,X1_40)
% 3.57/1.00      | ~ r1_tarski(k3_subset_1(X1_40,X2_40),X0_40)
% 3.57/1.00      | r1_tarski(k3_subset_1(X1_40,X0_40),X2_40) ),
% 3.57/1.00      inference(subtyping,[status(esa)],[c_257]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_767,plain,
% 3.57/1.00      ( ~ r1_tarski(X0_40,u1_struct_0(sK0))
% 3.57/1.00      | ~ r1_tarski(k2_pre_topc(sK0,X1_40),u1_struct_0(sK0))
% 3.57/1.00      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_40),k2_pre_topc(sK0,X1_40))
% 3.57/1.00      | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1_40)),X0_40) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_299]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_887,plain,
% 3.57/1.00      ( ~ r1_tarski(X0_40,u1_struct_0(sK0))
% 3.57/1.00      | ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40)),u1_struct_0(sK0))
% 3.57/1.00      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_40),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40)))
% 3.57/1.00      | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40))),X0_40) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_767]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_890,plain,
% 3.57/1.00      ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
% 3.57/1.00      | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)
% 3.57/1.00      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
% 3.57/1.00      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_887]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_677,plain,
% 3.57/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.57/1.00      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_306]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/1.00      | ~ l1_pre_topc(X1)
% 3.57/1.00      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_155,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/1.00      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 3.57/1.00      | sK0 != X1 ),
% 3.57/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_10]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_156,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.57/1.00      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 3.57/1.00      inference(unflattening,[status(thm)],[c_155]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_302,plain,
% 3.57/1.00      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.57/1.00      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_40))) = k1_tops_1(sK0,X0_40) ),
% 3.57/1.00      inference(subtyping,[status(esa)],[c_156]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_347,plain,
% 3.57/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.57/1.00      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_302]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_310,plain,( X0_40 = X0_40 ),theory(equality) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_329,plain,
% 3.57/1.00      ( sK1 = sK1 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_310]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_320,plain,
% 3.57/1.00      ( X0_40 != X1_40
% 3.57/1.00      | k1_tops_1(X0_42,X0_40) = k1_tops_1(X0_42,X1_40) ),
% 3.57/1.00      theory(equality) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_327,plain,
% 3.57/1.00      ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) | sK1 != sK1 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_320]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_8,negated_conjecture,
% 3.57/1.00      ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 3.57/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(contradiction,plain,
% 3.57/1.00      ( $false ),
% 3.57/1.00      inference(minisat,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_8495,c_6886,c_2129,c_1901,c_1687,c_1070,c_894,c_890,
% 3.57/1.00                 c_677,c_347,c_329,c_327,c_8,c_9]) ).
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.57/1.00  
% 3.57/1.00  ------                               Statistics
% 3.57/1.00  
% 3.57/1.00  ------ General
% 3.57/1.00  
% 3.57/1.00  abstr_ref_over_cycles:                  0
% 3.57/1.00  abstr_ref_under_cycles:                 0
% 3.57/1.00  gc_basic_clause_elim:                   0
% 3.57/1.00  forced_gc_time:                         0
% 3.57/1.00  parsing_time:                           0.01
% 3.57/1.00  unif_index_cands_time:                  0.
% 3.57/1.00  unif_index_add_time:                    0.
% 3.57/1.00  orderings_time:                         0.
% 3.57/1.00  out_proof_time:                         0.007
% 3.57/1.00  total_time:                             0.418
% 3.57/1.00  num_of_symbols:                         47
% 3.57/1.00  num_of_terms:                           10934
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing
% 3.57/1.00  
% 3.57/1.00  num_of_splits:                          0
% 3.57/1.00  num_of_split_atoms:                     0
% 3.57/1.00  num_of_reused_defs:                     0
% 3.57/1.00  num_eq_ax_congr_red:                    13
% 3.57/1.00  num_of_sem_filtered_clauses:            1
% 3.57/1.00  num_of_subtypes:                        4
% 3.57/1.00  monotx_restored_types:                  0
% 3.57/1.00  sat_num_of_epr_types:                   0
% 3.57/1.00  sat_num_of_non_cyclic_types:            0
% 3.57/1.00  sat_guarded_non_collapsed_types:        0
% 3.57/1.00  num_pure_diseq_elim:                    0
% 3.57/1.00  simp_replaced_by:                       0
% 3.57/1.00  res_preprocessed:                       64
% 3.57/1.00  prep_upred:                             0
% 3.57/1.00  prep_unflattend:                        3
% 3.57/1.00  smt_new_axioms:                         0
% 3.57/1.00  pred_elim_cands:                        2
% 3.57/1.00  pred_elim:                              1
% 3.57/1.00  pred_elim_cl:                           1
% 3.57/1.00  pred_elim_cycles:                       3
% 3.57/1.00  merged_defs:                            8
% 3.57/1.00  merged_defs_ncl:                        0
% 3.57/1.00  bin_hyper_res:                          11
% 3.57/1.00  prep_cycles:                            4
% 3.57/1.00  pred_elim_time:                         0.001
% 3.57/1.00  splitting_time:                         0.
% 3.57/1.00  sem_filter_time:                        0.
% 3.57/1.00  monotx_time:                            0.
% 3.57/1.00  subtype_inf_time:                       0.
% 3.57/1.00  
% 3.57/1.00  ------ Problem properties
% 3.57/1.00  
% 3.57/1.00  clauses:                                10
% 3.57/1.00  conjectures:                            2
% 3.57/1.00  epr:                                    0
% 3.57/1.00  horn:                                   10
% 3.57/1.00  ground:                                 2
% 3.57/1.00  unary:                                  3
% 3.57/1.00  binary:                                 6
% 3.57/1.00  lits:                                   19
% 3.57/1.00  lits_eq:                                2
% 3.57/1.00  fd_pure:                                0
% 3.57/1.00  fd_pseudo:                              0
% 3.57/1.00  fd_cond:                                0
% 3.57/1.00  fd_pseudo_cond:                         0
% 3.57/1.00  ac_symbols:                             0
% 3.57/1.00  
% 3.57/1.00  ------ Propositional Solver
% 3.57/1.00  
% 3.57/1.00  prop_solver_calls:                      30
% 3.57/1.00  prop_fast_solver_calls:                 446
% 3.57/1.00  smt_solver_calls:                       0
% 3.57/1.00  smt_fast_solver_calls:                  0
% 3.57/1.00  prop_num_of_clauses:                    2980
% 3.57/1.00  prop_preprocess_simplified:             5558
% 3.57/1.00  prop_fo_subsumed:                       3
% 3.57/1.00  prop_solver_time:                       0.
% 3.57/1.00  smt_solver_time:                        0.
% 3.57/1.00  smt_fast_solver_time:                   0.
% 3.57/1.00  prop_fast_solver_time:                  0.
% 3.57/1.00  prop_unsat_core_time:                   0.
% 3.57/1.00  
% 3.57/1.00  ------ QBF
% 3.57/1.00  
% 3.57/1.00  qbf_q_res:                              0
% 3.57/1.00  qbf_num_tautologies:                    0
% 3.57/1.00  qbf_prep_cycles:                        0
% 3.57/1.00  
% 3.57/1.00  ------ BMC1
% 3.57/1.00  
% 3.57/1.00  bmc1_current_bound:                     -1
% 3.57/1.00  bmc1_last_solved_bound:                 -1
% 3.57/1.00  bmc1_unsat_core_size:                   -1
% 3.57/1.00  bmc1_unsat_core_parents_size:           -1
% 3.57/1.00  bmc1_merge_next_fun:                    0
% 3.57/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.57/1.00  
% 3.57/1.00  ------ Instantiation
% 3.57/1.00  
% 3.57/1.00  inst_num_of_clauses:                    809
% 3.57/1.00  inst_num_in_passive:                    309
% 3.57/1.00  inst_num_in_active:                     460
% 3.57/1.00  inst_num_in_unprocessed:                39
% 3.57/1.00  inst_num_of_loops:                      502
% 3.57/1.00  inst_num_of_learning_restarts:          0
% 3.57/1.00  inst_num_moves_active_passive:          36
% 3.57/1.00  inst_lit_activity:                      0
% 3.57/1.00  inst_lit_activity_moves:                0
% 3.57/1.00  inst_num_tautologies:                   0
% 3.57/1.00  inst_num_prop_implied:                  0
% 3.57/1.00  inst_num_existing_simplified:           0
% 3.57/1.00  inst_num_eq_res_simplified:             0
% 3.57/1.00  inst_num_child_elim:                    0
% 3.57/1.00  inst_num_of_dismatching_blockings:      785
% 3.57/1.00  inst_num_of_non_proper_insts:           1047
% 3.57/1.00  inst_num_of_duplicates:                 0
% 3.57/1.00  inst_inst_num_from_inst_to_res:         0
% 3.57/1.00  inst_dismatching_checking_time:         0.
% 3.57/1.00  
% 3.57/1.00  ------ Resolution
% 3.57/1.00  
% 3.57/1.00  res_num_of_clauses:                     0
% 3.57/1.00  res_num_in_passive:                     0
% 3.57/1.00  res_num_in_active:                      0
% 3.57/1.00  res_num_of_loops:                       68
% 3.57/1.00  res_forward_subset_subsumed:            52
% 3.57/1.00  res_backward_subset_subsumed:           0
% 3.57/1.00  res_forward_subsumed:                   0
% 3.57/1.00  res_backward_subsumed:                  0
% 3.57/1.00  res_forward_subsumption_resolution:     0
% 3.57/1.00  res_backward_subsumption_resolution:    0
% 3.57/1.00  res_clause_to_clause_subsumption:       781
% 3.57/1.00  res_orphan_elimination:                 0
% 3.57/1.00  res_tautology_del:                      254
% 3.57/1.00  res_num_eq_res_simplified:              0
% 3.57/1.00  res_num_sel_changes:                    0
% 3.57/1.00  res_moves_from_active_to_pass:          0
% 3.57/1.00  
% 3.57/1.00  ------ Superposition
% 3.57/1.00  
% 3.57/1.00  sup_time_total:                         0.
% 3.57/1.00  sup_time_generating:                    0.
% 3.57/1.00  sup_time_sim_full:                      0.
% 3.57/1.00  sup_time_sim_immed:                     0.
% 3.57/1.00  
% 3.57/1.00  sup_num_of_clauses:                     357
% 3.57/1.00  sup_num_in_active:                      100
% 3.57/1.00  sup_num_in_passive:                     257
% 3.57/1.00  sup_num_of_loops:                       100
% 3.57/1.00  sup_fw_superposition:                   214
% 3.57/1.00  sup_bw_superposition:                   283
% 3.57/1.00  sup_immediate_simplified:               114
% 3.57/1.00  sup_given_eliminated:                   0
% 3.57/1.00  comparisons_done:                       0
% 3.57/1.00  comparisons_avoided:                    0
% 3.57/1.00  
% 3.57/1.00  ------ Simplifications
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  sim_fw_subset_subsumed:                 0
% 3.57/1.00  sim_bw_subset_subsumed:                 0
% 3.57/1.00  sim_fw_subsumed:                        0
% 3.57/1.00  sim_bw_subsumed:                        0
% 3.57/1.00  sim_fw_subsumption_res:                 0
% 3.57/1.00  sim_bw_subsumption_res:                 0
% 3.57/1.00  sim_tautology_del:                      11
% 3.57/1.00  sim_eq_tautology_del:                   0
% 3.57/1.00  sim_eq_res_simp:                        0
% 3.57/1.00  sim_fw_demodulated:                     8
% 3.57/1.00  sim_bw_demodulated:                     0
% 3.57/1.00  sim_light_normalised:                   107
% 3.57/1.00  sim_joinable_taut:                      0
% 3.57/1.00  sim_joinable_simp:                      0
% 3.57/1.00  sim_ac_normalised:                      0
% 3.57/1.00  sim_smt_subsumption:                    0
% 3.57/1.00  
%------------------------------------------------------------------------------
