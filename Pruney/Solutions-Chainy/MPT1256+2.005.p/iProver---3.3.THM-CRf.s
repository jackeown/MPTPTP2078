%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:12 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 229 expanded)
%              Number of clauses        :   55 (  86 expanded)
%              Number of leaves         :   11 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :  213 ( 613 expanded)
%              Number of equality atoms :   81 ( 106 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,sK1)),k2_tops_1(X0,sK1))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_108,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_331,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_108])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_117,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
    | m1_subset_1(k3_subset_1(X0_43,X0_41),k1_zfmisc_1(X0_43)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_322,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top
    | m1_subset_1(k3_subset_1(X0_43,X0_41),k1_zfmisc_1(X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_117])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_114,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40)))
    | ~ l1_pre_topc(X0_40)
    | k3_subset_1(u1_struct_0(X0_40),k2_pre_topc(X0_40,k3_subset_1(u1_struct_0(X0_40),X0_41))) = k1_tops_1(X0_40,X0_41) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_325,plain,
    ( k3_subset_1(u1_struct_0(X0_40),k2_pre_topc(X0_40,k3_subset_1(u1_struct_0(X0_40),X0_41))) = k1_tops_1(X0_40,X0_41)
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40))) != iProver_top
    | l1_pre_topc(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_114])).

cnf(c_2005,plain,
    ( k3_subset_1(u1_struct_0(X0_40),k2_pre_topc(X0_40,k3_subset_1(u1_struct_0(X0_40),k3_subset_1(u1_struct_0(X0_40),X0_41)))) = k1_tops_1(X0_40,k3_subset_1(u1_struct_0(X0_40),X0_41))
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40))) != iProver_top
    | l1_pre_topc(X0_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_322,c_325])).

cnf(c_21765,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_331,c_2005])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_115,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
    | k3_subset_1(X0_43,k3_subset_1(X0_43,X0_41)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_324,plain,
    ( k3_subset_1(X0_43,k3_subset_1(X0_43,X0_41)) = X0_41
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_115])).

cnf(c_485,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_331,c_324])).

cnf(c_21846,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21765,c_485])).

cnf(c_10,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_22903,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21846,c_11])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_112,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40)))
    | ~ l1_pre_topc(X0_40)
    | k2_tops_1(X0_40,k3_subset_1(u1_struct_0(X0_40),X0_41)) = k2_tops_1(X0_40,X0_41) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_327,plain,
    ( k2_tops_1(X0_40,k3_subset_1(u1_struct_0(X0_40),X0_41)) = k2_tops_1(X0_40,X0_41)
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40))) != iProver_top
    | l1_pre_topc(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_112])).

cnf(c_1114,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_331,c_327])).

cnf(c_151,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_112])).

cnf(c_1350,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1114,c_10,c_9,c_151])).

cnf(c_7,plain,
    ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_110,plain,
    ( r1_tarski(k2_tops_1(X0_40,k1_tops_1(X0_40,X0_41)),k2_tops_1(X0_40,X0_41))
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40)))
    | ~ l1_pre_topc(X0_40) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_329,plain,
    ( r1_tarski(k2_tops_1(X0_40,k1_tops_1(X0_40,X0_41)),k2_tops_1(X0_40,X0_41)) = iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40))) != iProver_top
    | l1_pre_topc(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_110])).

cnf(c_1353,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,sK1)) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1350,c_329])).

cnf(c_12,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_419,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_420,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_1667,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1353,c_11,c_12,c_420])).

cnf(c_22906,plain,
    ( r1_tarski(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_22903,c_1667])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_111,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40)))
    | ~ l1_pre_topc(X0_40)
    | k4_subset_1(u1_struct_0(X0_40),X0_41,k2_tops_1(X0_40,X0_41)) = k2_pre_topc(X0_40,X0_41) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_328,plain,
    ( k4_subset_1(u1_struct_0(X0_40),X0_41,k2_tops_1(X0_40,X0_41)) = k2_pre_topc(X0_40,X0_41)
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40))) != iProver_top
    | l1_pre_topc(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_111])).

cnf(c_1156,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_331,c_328])).

cnf(c_154,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_111])).

cnf(c_1537,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1156,c_10,c_9,c_154])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_116,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_43))
    | m1_subset_1(k4_subset_1(X0_43,X0_41,X1_41),k1_zfmisc_1(X0_43)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_323,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top
    | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top
    | m1_subset_1(k4_subset_1(X0_43,X1_41,X0_41),k1_zfmisc_1(X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_116])).

cnf(c_1540,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1537,c_323])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_113,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40)))
    | m1_subset_1(k2_tops_1(X0_40,X0_41),k1_zfmisc_1(u1_struct_0(X0_40)))
    | ~ l1_pre_topc(X0_40) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_147,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40))) != iProver_top
    | m1_subset_1(k2_tops_1(X0_40,X0_41),k1_zfmisc_1(u1_struct_0(X0_40))) = iProver_top
    | l1_pre_topc(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_113])).

cnf(c_149,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_1642,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1540,c_11,c_12,c_149])).

cnf(c_1648,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1642,c_327])).

cnf(c_2216,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1648,c_11])).

cnf(c_22907,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22906,c_2216])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22907,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:04:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.78/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.78/1.48  
% 7.78/1.48  ------  iProver source info
% 7.78/1.48  
% 7.78/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.78/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.78/1.48  git: non_committed_changes: false
% 7.78/1.48  git: last_make_outside_of_git: false
% 7.78/1.48  
% 7.78/1.48  ------ 
% 7.78/1.48  ------ Parsing...
% 7.78/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.48  ------ Proving...
% 7.78/1.48  ------ Problem Properties 
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  clauses                                 11
% 7.78/1.48  conjectures                             3
% 7.78/1.48  EPR                                     1
% 7.78/1.48  Horn                                    11
% 7.78/1.48  unary                                   3
% 7.78/1.48  binary                                  2
% 7.78/1.48  lits                                    25
% 7.78/1.48  lits eq                                 4
% 7.78/1.48  fd_pure                                 0
% 7.78/1.48  fd_pseudo                               0
% 7.78/1.48  fd_cond                                 0
% 7.78/1.48  fd_pseudo_cond                          0
% 7.78/1.48  AC symbols                              0
% 7.78/1.48  
% 7.78/1.48  ------ Input Options Time Limit: Unbounded
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  ------ 
% 7.78/1.48  Current options:
% 7.78/1.48  ------ 
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  ------ Proving...
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  % SZS status Theorem for theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  fof(f9,conjecture,(
% 7.78/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f10,negated_conjecture,(
% 7.78/1.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 7.78/1.48    inference(negated_conjecture,[],[f9])).
% 7.78/1.48  
% 7.78/1.48  fof(f21,plain,(
% 7.78/1.48    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.78/1.48    inference(ennf_transformation,[],[f10])).
% 7.78/1.48  
% 7.78/1.48  fof(f23,plain,(
% 7.78/1.48    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,sK1)),k2_tops_1(X0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.78/1.48    introduced(choice_axiom,[])).
% 7.78/1.48  
% 7.78/1.48  fof(f22,plain,(
% 7.78/1.48    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 7.78/1.48    introduced(choice_axiom,[])).
% 7.78/1.48  
% 7.78/1.48  fof(f24,plain,(
% 7.78/1.48    (~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 7.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).
% 7.78/1.48  
% 7.78/1.48  fof(f34,plain,(
% 7.78/1.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.78/1.48    inference(cnf_transformation,[],[f24])).
% 7.78/1.48  
% 7.78/1.48  fof(f1,axiom,(
% 7.78/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f11,plain,(
% 7.78/1.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.78/1.48    inference(ennf_transformation,[],[f1])).
% 7.78/1.48  
% 7.78/1.48  fof(f25,plain,(
% 7.78/1.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.78/1.48    inference(cnf_transformation,[],[f11])).
% 7.78/1.48  
% 7.78/1.48  fof(f4,axiom,(
% 7.78/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f15,plain,(
% 7.78/1.48    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.78/1.48    inference(ennf_transformation,[],[f4])).
% 7.78/1.48  
% 7.78/1.48  fof(f28,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f15])).
% 7.78/1.48  
% 7.78/1.48  fof(f3,axiom,(
% 7.78/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f14,plain,(
% 7.78/1.48    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.78/1.48    inference(ennf_transformation,[],[f3])).
% 7.78/1.48  
% 7.78/1.48  fof(f27,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.78/1.48    inference(cnf_transformation,[],[f14])).
% 7.78/1.48  
% 7.78/1.48  fof(f33,plain,(
% 7.78/1.48    l1_pre_topc(sK0)),
% 7.78/1.48    inference(cnf_transformation,[],[f24])).
% 7.78/1.48  
% 7.78/1.48  fof(f6,axiom,(
% 7.78/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f18,plain,(
% 7.78/1.48    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.78/1.48    inference(ennf_transformation,[],[f6])).
% 7.78/1.48  
% 7.78/1.48  fof(f30,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f18])).
% 7.78/1.48  
% 7.78/1.48  fof(f8,axiom,(
% 7.78/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f20,plain,(
% 7.78/1.48    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.78/1.48    inference(ennf_transformation,[],[f8])).
% 7.78/1.48  
% 7.78/1.48  fof(f32,plain,(
% 7.78/1.48    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f20])).
% 7.78/1.48  
% 7.78/1.48  fof(f7,axiom,(
% 7.78/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f19,plain,(
% 7.78/1.48    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.78/1.48    inference(ennf_transformation,[],[f7])).
% 7.78/1.48  
% 7.78/1.48  fof(f31,plain,(
% 7.78/1.48    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f19])).
% 7.78/1.48  
% 7.78/1.48  fof(f2,axiom,(
% 7.78/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f12,plain,(
% 7.78/1.48    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.78/1.48    inference(ennf_transformation,[],[f2])).
% 7.78/1.48  
% 7.78/1.48  fof(f13,plain,(
% 7.78/1.48    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.78/1.48    inference(flattening,[],[f12])).
% 7.78/1.48  
% 7.78/1.48  fof(f26,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.78/1.48    inference(cnf_transformation,[],[f13])).
% 7.78/1.48  
% 7.78/1.48  fof(f5,axiom,(
% 7.78/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f16,plain,(
% 7.78/1.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.78/1.48    inference(ennf_transformation,[],[f5])).
% 7.78/1.48  
% 7.78/1.48  fof(f17,plain,(
% 7.78/1.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.78/1.48    inference(flattening,[],[f16])).
% 7.78/1.48  
% 7.78/1.48  fof(f29,plain,(
% 7.78/1.48    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f17])).
% 7.78/1.48  
% 7.78/1.48  fof(f35,plain,(
% 7.78/1.48    ~r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 7.78/1.48    inference(cnf_transformation,[],[f24])).
% 7.78/1.48  
% 7.78/1.48  cnf(c_9,negated_conjecture,
% 7.78/1.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.78/1.48      inference(cnf_transformation,[],[f34]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_108,negated_conjecture,
% 7.78/1.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.78/1.48      inference(subtyping,[status(esa)],[c_9]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_331,plain,
% 7.78/1.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_108]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_0,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.78/1.48      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.78/1.48      inference(cnf_transformation,[],[f25]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_117,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 7.78/1.48      | m1_subset_1(k3_subset_1(X0_43,X0_41),k1_zfmisc_1(X0_43)) ),
% 7.78/1.48      inference(subtyping,[status(esa)],[c_0]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_322,plain,
% 7.78/1.48      ( m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top
% 7.78/1.48      | m1_subset_1(k3_subset_1(X0_43,X0_41),k1_zfmisc_1(X0_43)) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_117]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_3,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.48      | ~ l1_pre_topc(X1)
% 7.78/1.48      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 7.78/1.48      inference(cnf_transformation,[],[f28]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_114,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40)))
% 7.78/1.48      | ~ l1_pre_topc(X0_40)
% 7.78/1.48      | k3_subset_1(u1_struct_0(X0_40),k2_pre_topc(X0_40,k3_subset_1(u1_struct_0(X0_40),X0_41))) = k1_tops_1(X0_40,X0_41) ),
% 7.78/1.48      inference(subtyping,[status(esa)],[c_3]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_325,plain,
% 7.78/1.48      ( k3_subset_1(u1_struct_0(X0_40),k2_pre_topc(X0_40,k3_subset_1(u1_struct_0(X0_40),X0_41))) = k1_tops_1(X0_40,X0_41)
% 7.78/1.48      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40))) != iProver_top
% 7.78/1.48      | l1_pre_topc(X0_40) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_114]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2005,plain,
% 7.78/1.48      ( k3_subset_1(u1_struct_0(X0_40),k2_pre_topc(X0_40,k3_subset_1(u1_struct_0(X0_40),k3_subset_1(u1_struct_0(X0_40),X0_41)))) = k1_tops_1(X0_40,k3_subset_1(u1_struct_0(X0_40),X0_41))
% 7.78/1.48      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40))) != iProver_top
% 7.78/1.48      | l1_pre_topc(X0_40) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_322,c_325]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_21765,plain,
% 7.78/1.48      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
% 7.78/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_331,c_2005]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.78/1.48      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.78/1.48      inference(cnf_transformation,[],[f27]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_115,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 7.78/1.48      | k3_subset_1(X0_43,k3_subset_1(X0_43,X0_41)) = X0_41 ),
% 7.78/1.48      inference(subtyping,[status(esa)],[c_2]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_324,plain,
% 7.78/1.48      ( k3_subset_1(X0_43,k3_subset_1(X0_43,X0_41)) = X0_41
% 7.78/1.48      | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_115]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_485,plain,
% 7.78/1.48      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_331,c_324]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_21846,plain,
% 7.78/1.48      ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
% 7.78/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.78/1.48      inference(light_normalisation,[status(thm)],[c_21765,c_485]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_10,negated_conjecture,
% 7.78/1.48      ( l1_pre_topc(sK0) ),
% 7.78/1.48      inference(cnf_transformation,[],[f33]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_11,plain,
% 7.78/1.48      ( l1_pre_topc(sK0) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_22903,plain,
% 7.78/1.48      ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_21846,c_11]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_5,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.48      | ~ l1_pre_topc(X1)
% 7.78/1.48      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
% 7.78/1.48      inference(cnf_transformation,[],[f30]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_112,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40)))
% 7.78/1.48      | ~ l1_pre_topc(X0_40)
% 7.78/1.48      | k2_tops_1(X0_40,k3_subset_1(u1_struct_0(X0_40),X0_41)) = k2_tops_1(X0_40,X0_41) ),
% 7.78/1.48      inference(subtyping,[status(esa)],[c_5]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_327,plain,
% 7.78/1.48      ( k2_tops_1(X0_40,k3_subset_1(u1_struct_0(X0_40),X0_41)) = k2_tops_1(X0_40,X0_41)
% 7.78/1.48      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40))) != iProver_top
% 7.78/1.48      | l1_pre_topc(X0_40) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_112]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1114,plain,
% 7.78/1.48      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1)
% 7.78/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_331,c_327]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_151,plain,
% 7.78/1.48      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.78/1.48      | ~ l1_pre_topc(sK0)
% 7.78/1.48      | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_112]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1350,plain,
% 7.78/1.48      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_1114,c_10,c_9,c_151]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_7,plain,
% 7.78/1.48      ( r1_tarski(k2_tops_1(X0,k1_tops_1(X0,X1)),k2_tops_1(X0,X1))
% 7.78/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.78/1.48      | ~ l1_pre_topc(X0) ),
% 7.78/1.48      inference(cnf_transformation,[],[f32]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_110,plain,
% 7.78/1.48      ( r1_tarski(k2_tops_1(X0_40,k1_tops_1(X0_40,X0_41)),k2_tops_1(X0_40,X0_41))
% 7.78/1.48      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40)))
% 7.78/1.48      | ~ l1_pre_topc(X0_40) ),
% 7.78/1.48      inference(subtyping,[status(esa)],[c_7]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_329,plain,
% 7.78/1.48      ( r1_tarski(k2_tops_1(X0_40,k1_tops_1(X0_40,X0_41)),k2_tops_1(X0_40,X0_41)) = iProver_top
% 7.78/1.48      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40))) != iProver_top
% 7.78/1.48      | l1_pre_topc(X0_40) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_110]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1353,plain,
% 7.78/1.48      ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,sK1)) = iProver_top
% 7.78/1.48      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.78/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_1350,c_329]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_12,plain,
% 7.78/1.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_419,plain,
% 7.78/1.48      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.78/1.48      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_117]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_420,plain,
% 7.78/1.48      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.78/1.48      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1667,plain,
% 7.78/1.48      ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k2_tops_1(sK0,sK1)) = iProver_top ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_1353,c_11,c_12,c_420]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_22906,plain,
% 7.78/1.48      ( r1_tarski(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_tops_1(sK0,sK1)) = iProver_top ),
% 7.78/1.48      inference(demodulation,[status(thm)],[c_22903,c_1667]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_6,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.48      | ~ l1_pre_topc(X1)
% 7.78/1.48      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.78/1.48      inference(cnf_transformation,[],[f31]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_111,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40)))
% 7.78/1.48      | ~ l1_pre_topc(X0_40)
% 7.78/1.48      | k4_subset_1(u1_struct_0(X0_40),X0_41,k2_tops_1(X0_40,X0_41)) = k2_pre_topc(X0_40,X0_41) ),
% 7.78/1.48      inference(subtyping,[status(esa)],[c_6]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_328,plain,
% 7.78/1.48      ( k4_subset_1(u1_struct_0(X0_40),X0_41,k2_tops_1(X0_40,X0_41)) = k2_pre_topc(X0_40,X0_41)
% 7.78/1.48      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40))) != iProver_top
% 7.78/1.48      | l1_pre_topc(X0_40) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_111]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1156,plain,
% 7.78/1.48      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 7.78/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_331,c_328]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_154,plain,
% 7.78/1.48      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.78/1.48      | ~ l1_pre_topc(sK0)
% 7.78/1.48      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_111]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1537,plain,
% 7.78/1.48      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_1156,c_10,c_9,c_154]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.78/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.78/1.48      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 7.78/1.48      inference(cnf_transformation,[],[f26]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_116,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 7.78/1.48      | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_43))
% 7.78/1.48      | m1_subset_1(k4_subset_1(X0_43,X0_41,X1_41),k1_zfmisc_1(X0_43)) ),
% 7.78/1.48      inference(subtyping,[status(esa)],[c_1]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_323,plain,
% 7.78/1.48      ( m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top
% 7.78/1.48      | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top
% 7.78/1.48      | m1_subset_1(k4_subset_1(X0_43,X1_41,X0_41),k1_zfmisc_1(X0_43)) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_116]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1540,plain,
% 7.78/1.48      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.78/1.48      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.78/1.48      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_1537,c_323]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_4,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.48      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.78/1.48      | ~ l1_pre_topc(X1) ),
% 7.78/1.48      inference(cnf_transformation,[],[f29]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_113,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40)))
% 7.78/1.48      | m1_subset_1(k2_tops_1(X0_40,X0_41),k1_zfmisc_1(u1_struct_0(X0_40)))
% 7.78/1.48      | ~ l1_pre_topc(X0_40) ),
% 7.78/1.48      inference(subtyping,[status(esa)],[c_4]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_147,plain,
% 7.78/1.48      ( m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_40))) != iProver_top
% 7.78/1.48      | m1_subset_1(k2_tops_1(X0_40,X0_41),k1_zfmisc_1(u1_struct_0(X0_40))) = iProver_top
% 7.78/1.48      | l1_pre_topc(X0_40) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_113]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_149,plain,
% 7.78/1.48      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.78/1.48      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.78/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_147]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1642,plain,
% 7.78/1.48      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_1540,c_11,c_12,c_149]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1648,plain,
% 7.78/1.48      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1))
% 7.78/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_1642,c_327]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2216,plain,
% 7.78/1.48      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_1648,c_11]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_22907,plain,
% 7.78/1.48      ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
% 7.78/1.48      inference(light_normalisation,[status(thm)],[c_22906,c_2216]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_8,negated_conjecture,
% 7.78/1.48      ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
% 7.78/1.48      inference(cnf_transformation,[],[f35]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_13,plain,
% 7.78/1.48      ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(contradiction,plain,
% 7.78/1.48      ( $false ),
% 7.78/1.48      inference(minisat,[status(thm)],[c_22907,c_13]) ).
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  ------                               Statistics
% 7.78/1.48  
% 7.78/1.48  ------ Selected
% 7.78/1.48  
% 7.78/1.48  total_time:                             0.788
% 7.78/1.48  
%------------------------------------------------------------------------------
