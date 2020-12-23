%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1861+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:42 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 192 expanded)
%              Number of clauses        :   57 (  80 expanded)
%              Number of leaves         :   12 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  239 ( 824 expanded)
%              Number of equality atoms :   57 (  78 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & ( v2_tex_2(X2,X0)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & ( v2_tex_2(sK2,X0)
          | v2_tex_2(X1,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & ( v2_tex_2(X2,X0)
              | v2_tex_2(sK1,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & ( v2_tex_2(X2,sK0)
                | v2_tex_2(X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16,f15,f14])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f27,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f26,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_212,plain,
    ( k3_xboole_0(X0_39,X1_39) = k3_xboole_0(X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1151,plain,
    ( k3_xboole_0(X0_39,sK2) = k3_xboole_0(sK2,X0_39) ),
    inference(instantiation,[status(thm)],[c_212])).

cnf(c_1156,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1151])).

cnf(c_218,plain,
    ( ~ v2_tex_2(X0_39,X0_40)
    | v2_tex_2(X1_39,X0_40)
    | X1_39 != X0_39 ),
    theory(equality)).

cnf(c_483,plain,
    ( v2_tex_2(X0_39,sK0)
    | ~ v2_tex_2(k3_xboole_0(sK2,X1_39),sK0)
    | X0_39 != k3_xboole_0(sK2,X1_39) ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_1150,plain,
    ( v2_tex_2(k3_xboole_0(X0_39,sK2),sK0)
    | ~ v2_tex_2(k3_xboole_0(sK2,X0_39),sK0)
    | k3_xboole_0(X0_39,sK2) != k3_xboole_0(sK2,X0_39) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_1153,plain,
    ( ~ v2_tex_2(k3_xboole_0(sK2,sK1),sK0)
    | v2_tex_2(k3_xboole_0(sK1,sK2),sK0)
    | k3_xboole_0(sK1,sK2) != k3_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_207,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_365,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_210,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X0_42))
    | k9_subset_1(X0_42,X1_39,X0_39) = k3_xboole_0(X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_362,plain,
    ( k9_subset_1(X0_42,X0_39,X1_39) = k3_xboole_0(X0_39,X1_39)
    | m1_subset_1(X1_39,k1_zfmisc_1(X0_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_584,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_39,sK2) = k3_xboole_0(X0_39,sK2) ),
    inference(superposition,[status(thm)],[c_365,c_362])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_211,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X0_42))
    | m1_subset_1(k9_subset_1(X0_42,X1_39,X0_39),k1_zfmisc_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_361,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(X0_42)) != iProver_top
    | m1_subset_1(k9_subset_1(X0_42,X1_39,X0_39),k1_zfmisc_1(X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

cnf(c_642,plain,
    ( m1_subset_1(k3_xboole_0(X0_39,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_584,c_361])).

cnf(c_12,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_795,plain,
    ( m1_subset_1(k3_xboole_0(X0_39,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_642,c_12])).

cnf(c_3,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_4,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_102,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | X0 != X3
    | k3_xboole_0(X3,X4) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_103,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(k3_xboole_0(X0,X2),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k3_xboole_0(X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_102])).

cnf(c_9,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_129,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(k3_xboole_0(X0,X2),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k3_xboole_0(X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_103,c_9])).

cnf(c_130,plain,
    ( ~ v2_tex_2(X0,sK0)
    | v2_tex_2(k3_xboole_0(X0,X1),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_129])).

cnf(c_205,plain,
    ( ~ v2_tex_2(X0_39,sK0)
    | v2_tex_2(k3_xboole_0(X0_39,X1_39),sK0)
    | ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_xboole_0(X0_39,X1_39),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_130])).

cnf(c_367,plain,
    ( v2_tex_2(X0_39,sK0) != iProver_top
    | v2_tex_2(k3_xboole_0(X0_39,X1_39),sK0) = iProver_top
    | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_xboole_0(X0_39,X1_39),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_205])).

cnf(c_804,plain,
    ( v2_tex_2(X0_39,sK0) != iProver_top
    | v2_tex_2(k3_xboole_0(X0_39,sK2),sK0) = iProver_top
    | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_367])).

cnf(c_826,plain,
    ( ~ v2_tex_2(X0_39,sK0)
    | v2_tex_2(k3_xboole_0(X0_39,sK2),sK0)
    | ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_804])).

cnf(c_828,plain,
    ( v2_tex_2(k3_xboole_0(sK1,sK2),sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_5,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_209,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_363,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_640,plain,
    ( v2_tex_2(k3_xboole_0(sK1,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_584,c_363])).

cnf(c_641,plain,
    ( ~ v2_tex_2(k3_xboole_0(sK1,sK2),sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_640])).

cnf(c_215,plain,
    ( X0_39 != X1_39
    | X2_39 != X1_39
    | X2_39 = X0_39 ),
    theory(equality)).

cnf(c_572,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_39,sK2) != X1_39
    | k3_xboole_0(sK2,X2_39) != X1_39
    | k3_xboole_0(sK2,X2_39) = k9_subset_1(u1_struct_0(sK0),X0_39,sK2) ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_625,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_39,sK2) != k3_xboole_0(X1_39,sK2)
    | k3_xboole_0(sK2,X1_39) = k9_subset_1(u1_struct_0(sK0),X0_39,sK2)
    | k3_xboole_0(sK2,X1_39) != k3_xboole_0(X1_39,sK2) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_628,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_xboole_0(sK1,sK2)
    | k3_xboole_0(sK2,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k3_xboole_0(sK2,sK1) != k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_593,plain,
    ( k3_xboole_0(sK2,X0_39) = k3_xboole_0(X0_39,sK2) ),
    inference(instantiation,[status(thm)],[c_212])).

cnf(c_598,plain,
    ( k3_xboole_0(sK2,sK1) = k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_593])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0_39,X0_41)
    | m1_subset_1(X1_39,X0_41)
    | X1_39 != X0_39 ),
    theory(equality)).

cnf(c_462,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1_39,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | X0_39 != k9_subset_1(u1_struct_0(sK0),X1_39,sK2) ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_529,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_39,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_xboole_0(sK2,X1_39),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_xboole_0(sK2,X1_39) != k9_subset_1(u1_struct_0(sK0),X0_39,sK2) ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_541,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_xboole_0(sK2,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_438,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),X0_39,sK2) = k3_xboole_0(X0_39,sK2) ),
    inference(instantiation,[status(thm)],[c_210])).

cnf(c_440,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(c_417,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_39,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_211])).

cnf(c_419,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_417])).

cnf(c_412,plain,
    ( v2_tex_2(k3_xboole_0(sK2,X0_39),sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ m1_subset_1(k3_xboole_0(sK2,X0_39),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_205])).

cnf(c_414,plain,
    ( v2_tex_2(k3_xboole_0(sK2,sK1),sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_412])).

cnf(c_6,negated_conjecture,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1156,c_1153,c_828,c_641,c_628,c_598,c_541,c_440,c_419,c_414,c_6,c_7,c_8])).


%------------------------------------------------------------------------------
