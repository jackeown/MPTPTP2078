%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:43 EST 2020

% Result     : CounterSatisfiable 11.38s
% Output     : Saturation 11.38s
% Verified   : 
% Statistics : Number of formulae       :  108 (1382 expanded)
%              Number of clauses        :   81 ( 557 expanded)
%              Number of leaves         :    9 ( 245 expanded)
%              Depth                    :   14
%              Number of atoms          :  248 (3128 expanded)
%              Number of equality atoms :  194 (1532 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f10,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) != k2_struct_0(X0)
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) != k2_struct_0(X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
   => ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_59,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_18900,plain,
    ( ~ iProver_ARSWP_52
    | k2_xboole_0(X0,arAF0_k4_xboole_0_0_1(X1)) = k2_xboole_0(X0,X1) ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_19001,plain,
    ( k2_xboole_0(X0,arAF0_k4_xboole_0_0_1(X1)) = k2_xboole_0(X0,X1)
    | iProver_ARSWP_52 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18900])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_19003,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_18901,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ iProver_ARSWP_53
    | arAF0_k3_subset_1_0_1(X1) = arAF0_k4_xboole_0_0_1(X1) ),
    inference(arg_filter_abstr,[status(unp)],[c_2])).

cnf(c_19000,plain,
    ( arAF0_k3_subset_1_0_1(X0) = arAF0_k4_xboole_0_0_1(X0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18901])).

cnf(c_19276,plain,
    ( arAF0_k3_subset_1_0_1(u1_struct_0(sK0)) = arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19003,c_19000])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_18902,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(arAF0_k3_subset_1_0_1(X1),k1_zfmisc_1(X1))
    | ~ iProver_ARSWP_54 ),
    inference(arg_filter_abstr,[status(unp)],[c_3])).

cnf(c_18999,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0_1(X1),k1_zfmisc_1(X1)) = iProver_top
    | iProver_ARSWP_54 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18902])).

cnf(c_19372,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | iProver_ARSWP_54 != iProver_top ),
    inference(superposition,[status(thm)],[c_19003,c_18999])).

cnf(c_19506,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19276,c_19372])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_19005,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_19507,plain,
    ( k4_subset_1(u1_struct_0(sK0),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),X0) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_54 != iProver_top ),
    inference(superposition,[status(thm)],[c_19372,c_19005])).

cnf(c_20237,plain,
    ( k4_subset_1(u1_struct_0(sK0),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19506,c_19507])).

cnf(c_21271,plain,
    ( k4_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19276,c_20237])).

cnf(c_20064,plain,
    ( k4_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),X0) = k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19506,c_19005])).

cnf(c_20509,plain,
    ( k4_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19506,c_20064])).

cnf(c_21912,plain,
    ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_21271,c_20509])).

cnf(c_22472,plain,
    ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),u1_struct_0(sK0))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top
    | iProver_ARSWP_52 != iProver_top ),
    inference(superposition,[status(thm)],[c_21912,c_19001])).

cnf(c_22655,plain,
    ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),u1_struct_0(sK0)) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),u1_struct_0(sK0))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top
    | iProver_ARSWP_52 != iProver_top ),
    inference(superposition,[status(thm)],[c_19001,c_22472])).

cnf(c_20508,plain,
    ( k4_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19372,c_20064])).

cnf(c_21100,plain,
    ( k4_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19276,c_20508])).

cnf(c_21911,plain,
    ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_21271,c_21100])).

cnf(c_22253,plain,
    ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),u1_struct_0(sK0))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top
    | iProver_ARSWP_52 != iProver_top ),
    inference(superposition,[status(thm)],[c_21911,c_19001])).

cnf(c_20236,plain,
    ( k4_subset_1(u1_struct_0(sK0),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top ),
    inference(superposition,[status(thm)],[c_19372,c_19507])).

cnf(c_20660,plain,
    ( k4_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19276,c_20236])).

cnf(c_21913,plain,
    ( k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_21271,c_20660])).

cnf(c_21558,plain,
    ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_21100,c_20660])).

cnf(c_21557,plain,
    ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_21100,c_20509])).

cnf(c_21548,plain,
    ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_20660,c_20509])).

cnf(c_20507,plain,
    ( k4_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),sK1) = k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),sK1)
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19003,c_20064])).

cnf(c_20235,plain,
    ( k4_subset_1(u1_struct_0(sK0),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),sK1) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),sK1)
    | iProver_ARSWP_54 != iProver_top ),
    inference(superposition,[status(thm)],[c_19003,c_19507])).

cnf(c_20381,plain,
    ( k4_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),sK1) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),sK1)
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19276,c_20235])).

cnf(c_20861,plain,
    ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),sK1) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),sK1)
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_20507,c_20381])).

cnf(c_19378,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19003,c_19005])).

cnf(c_19664,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) = k2_xboole_0(sK1,arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top ),
    inference(superposition,[status(thm)],[c_19372,c_19378])).

cnf(c_19904,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(sK1,arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19276,c_19664])).

cnf(c_20068,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(sK1,arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19506,c_19378])).

cnf(c_20847,plain,
    ( k2_xboole_0(sK1,arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(sK1,arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19904,c_20068])).

cnf(c_6,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_18903,negated_conjecture,
    ( ~ iProver_ARSWP_55
    | k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) != k2_struct_0(sK0) ),
    inference(arg_filter_abstr,[status(unp)],[c_6])).

cnf(c_18998,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) != k2_struct_0(sK0)
    | iProver_ARSWP_55 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18903])).

cnf(c_19905,plain,
    ( k2_xboole_0(sK1,arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) != k2_struct_0(sK0)
    | iProver_ARSWP_55 != iProver_top
    | iProver_ARSWP_54 != iProver_top ),
    inference(superposition,[status(thm)],[c_19664,c_18998])).

cnf(c_20058,plain,
    ( k2_xboole_0(sK1,arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) != k2_struct_0(sK0)
    | iProver_ARSWP_55 != iProver_top
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19276,c_19905])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_19004,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_19510,plain,
    ( r1_tarski(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),u1_struct_0(sK0)) = iProver_top
    | iProver_ARSWP_54 != iProver_top ),
    inference(superposition,[status(thm)],[c_19372,c_19004])).

cnf(c_19646,plain,
    ( r1_tarski(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),u1_struct_0(sK0)) = iProver_top
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19276,c_19510])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_19006,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_19899,plain,
    ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),u1_struct_0(sK0)) = u1_struct_0(sK0)
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19646,c_19006])).

cnf(c_19647,plain,
    ( k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),u1_struct_0(sK0)) = u1_struct_0(sK0)
    | iProver_ARSWP_54 != iProver_top ),
    inference(superposition,[status(thm)],[c_19510,c_19006])).

cnf(c_19501,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) != k2_struct_0(sK0)
    | iProver_ARSWP_55 != iProver_top
    | iProver_ARSWP_53 != iProver_top ),
    inference(superposition,[status(thm)],[c_19276,c_18998])).

cnf(c_20969,plain,
    ( k2_xboole_0(sK1,u1_struct_0(sK0)) != k2_struct_0(sK0)
    | iProver_ARSWP_55 != iProver_top
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top
    | iProver_ARSWP_52 != iProver_top ),
    inference(superposition,[status(thm)],[c_19001,c_20058])).

cnf(c_19214,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19003,c_19004])).

cnf(c_19218,plain,
    ( k2_xboole_0(sK1,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_19214,c_19006])).

cnf(c_20970,plain,
    ( k2_struct_0(sK0) != u1_struct_0(sK0)
    | iProver_ARSWP_55 != iProver_top
    | iProver_ARSWP_54 != iProver_top
    | iProver_ARSWP_53 != iProver_top
    | iProver_ARSWP_52 != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20969,c_19218])).

cnf(c_3481,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3485,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3811,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_3481,c_3485])).

cnf(c_3484,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4008,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3811,c_3484])).

cnf(c_8,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4336,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4008,c_8])).

cnf(c_3483,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3918,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3481,c_3483])).

cnf(c_4344,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) = k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_4336,c_3918])).

cnf(c_3482,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3719,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3481,c_3482])).

cnf(c_3486,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3723,plain,
    ( k2_xboole_0(sK1,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_3719,c_3486])).

cnf(c_4346,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_4344,c_1,c_3723])).

cnf(c_4007,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3811,c_6])).

cnf(c_4500,plain,
    ( k2_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_4346,c_4007])).

cnf(c_21274,plain,
    ( k2_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20970,c_4500])).

cnf(c_19663,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_19003,c_19378])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:23:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.38/1.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.38/1.93  
% 11.38/1.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.38/1.93  
% 11.38/1.93  ------  iProver source info
% 11.38/1.93  
% 11.38/1.93  git: date: 2020-06-30 10:37:57 +0100
% 11.38/1.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.38/1.93  git: non_committed_changes: false
% 11.38/1.93  git: last_make_outside_of_git: false
% 11.38/1.93  
% 11.38/1.93  ------ 
% 11.38/1.93  ------ Parsing...
% 11.38/1.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.38/1.93  
% 11.38/1.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.38/1.93  
% 11.38/1.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.38/1.93  
% 11.38/1.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.38/1.93  ------ Proving...
% 11.38/1.93  ------ Problem Properties 
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  clauses                                 8
% 11.38/1.93  conjectures                             2
% 11.38/1.93  EPR                                     0
% 11.38/1.93  Horn                                    8
% 11.38/1.93  unary                                   3
% 11.38/1.93  binary                                  4
% 11.38/1.93  lits                                    14
% 11.38/1.93  lits eq                                 5
% 11.38/1.93  fd_pure                                 0
% 11.38/1.93  fd_pseudo                               0
% 11.38/1.93  fd_cond                                 0
% 11.38/1.93  fd_pseudo_cond                          0
% 11.38/1.93  AC symbols                              0
% 11.38/1.93  
% 11.38/1.93  ------ Input Options Time Limit: Unbounded
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 11.38/1.93  Current options:
% 11.38/1.93  ------ 
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  ------ Proving...
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.38/1.93  
% 11.38/1.93  ------ Proving...
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.38/1.93  
% 11.38/1.93  ------ Proving...
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.38/1.93  
% 11.38/1.93  ------ Proving...
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.38/1.93  
% 11.38/1.93  ------ Proving...
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.38/1.93  
% 11.38/1.93  ------ Proving...
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.38/1.93  
% 11.38/1.93  ------ Proving...
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.38/1.93  
% 11.38/1.93  ------ Proving...
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.38/1.93  
% 11.38/1.93  ------ Proving...
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.38/1.93  
% 11.38/1.93  ------ Proving...
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  % SZS status CounterSatisfiable for theBenchmark.p
% 11.38/1.93  
% 11.38/1.93  % SZS output start Saturation for theBenchmark.p
% 11.38/1.93  
% 11.38/1.93  fof(f2,axiom,(
% 11.38/1.93    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.38/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.93  
% 11.38/1.93  fof(f21,plain,(
% 11.38/1.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.38/1.93    inference(cnf_transformation,[],[f2])).
% 11.38/1.93  
% 11.38/1.93  fof(f7,conjecture,(
% 11.38/1.93    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)))),
% 11.38/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.93  
% 11.38/1.93  fof(f8,negated_conjecture,(
% 11.38/1.93    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)))),
% 11.38/1.93    inference(negated_conjecture,[],[f7])).
% 11.38/1.93  
% 11.38/1.93  fof(f10,plain,(
% 11.38/1.93    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0))),
% 11.38/1.93    inference(pure_predicate_removal,[],[f8])).
% 11.38/1.93  
% 11.38/1.93  fof(f17,plain,(
% 11.38/1.93    ? [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) != k2_struct_0(X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 11.38/1.93    inference(ennf_transformation,[],[f10])).
% 11.38/1.93  
% 11.38/1.93  fof(f18,plain,(
% 11.38/1.93    ? [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) != k2_struct_0(X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 11.38/1.93    introduced(choice_axiom,[])).
% 11.38/1.93  
% 11.38/1.93  fof(f19,plain,(
% 11.38/1.93    k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.38/1.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 11.38/1.93  
% 11.38/1.93  fof(f26,plain,(
% 11.38/1.93    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.38/1.93    inference(cnf_transformation,[],[f19])).
% 11.38/1.93  
% 11.38/1.93  fof(f3,axiom,(
% 11.38/1.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.38/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.93  
% 11.38/1.93  fof(f12,plain,(
% 11.38/1.93    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.38/1.93    inference(ennf_transformation,[],[f3])).
% 11.38/1.93  
% 11.38/1.93  fof(f22,plain,(
% 11.38/1.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.38/1.93    inference(cnf_transformation,[],[f12])).
% 11.38/1.93  
% 11.38/1.93  fof(f4,axiom,(
% 11.38/1.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 11.38/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.93  
% 11.38/1.93  fof(f13,plain,(
% 11.38/1.93    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.38/1.93    inference(ennf_transformation,[],[f4])).
% 11.38/1.93  
% 11.38/1.93  fof(f23,plain,(
% 11.38/1.93    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.38/1.93    inference(cnf_transformation,[],[f13])).
% 11.38/1.93  
% 11.38/1.93  fof(f5,axiom,(
% 11.38/1.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.38/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.93  
% 11.38/1.93  fof(f14,plain,(
% 11.38/1.93    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.38/1.93    inference(ennf_transformation,[],[f5])).
% 11.38/1.93  
% 11.38/1.93  fof(f15,plain,(
% 11.38/1.93    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.38/1.93    inference(flattening,[],[f14])).
% 11.38/1.93  
% 11.38/1.93  fof(f24,plain,(
% 11.38/1.93    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.38/1.93    inference(cnf_transformation,[],[f15])).
% 11.38/1.93  
% 11.38/1.93  fof(f27,plain,(
% 11.38/1.93    k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0)),
% 11.38/1.93    inference(cnf_transformation,[],[f19])).
% 11.38/1.93  
% 11.38/1.93  fof(f6,axiom,(
% 11.38/1.93    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.38/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.93  
% 11.38/1.93  fof(f9,plain,(
% 11.38/1.93    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 11.38/1.93    inference(unused_predicate_definition_removal,[],[f6])).
% 11.38/1.93  
% 11.38/1.93  fof(f16,plain,(
% 11.38/1.93    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 11.38/1.93    inference(ennf_transformation,[],[f9])).
% 11.38/1.93  
% 11.38/1.93  fof(f25,plain,(
% 11.38/1.93    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.38/1.93    inference(cnf_transformation,[],[f16])).
% 11.38/1.93  
% 11.38/1.93  fof(f1,axiom,(
% 11.38/1.93    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.38/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.93  
% 11.38/1.93  fof(f11,plain,(
% 11.38/1.93    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.38/1.93    inference(ennf_transformation,[],[f1])).
% 11.38/1.93  
% 11.38/1.93  fof(f20,plain,(
% 11.38/1.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.38/1.93    inference(cnf_transformation,[],[f11])).
% 11.38/1.93  
% 11.38/1.93  cnf(c_59,plain,( X0_2 = X0_2 ),theory(equality) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_1,plain,
% 11.38/1.93      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.38/1.93      inference(cnf_transformation,[],[f21]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_18900,plain,
% 11.38/1.93      ( ~ iProver_ARSWP_52
% 11.38/1.93      | k2_xboole_0(X0,arAF0_k4_xboole_0_0_1(X1)) = k2_xboole_0(X0,X1) ),
% 11.38/1.93      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19001,plain,
% 11.38/1.93      ( k2_xboole_0(X0,arAF0_k4_xboole_0_0_1(X1)) = k2_xboole_0(X0,X1)
% 11.38/1.93      | iProver_ARSWP_52 != iProver_top ),
% 11.38/1.93      inference(predicate_to_equality,[status(thm)],[c_18900]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_7,negated_conjecture,
% 11.38/1.93      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.38/1.93      inference(cnf_transformation,[],[f26]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19003,plain,
% 11.38/1.93      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.38/1.93      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_2,plain,
% 11.38/1.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.38/1.93      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.38/1.93      inference(cnf_transformation,[],[f22]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_18901,plain,
% 11.38/1.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.38/1.93      | ~ iProver_ARSWP_53
% 11.38/1.93      | arAF0_k3_subset_1_0_1(X1) = arAF0_k4_xboole_0_0_1(X1) ),
% 11.38/1.93      inference(arg_filter_abstr,[status(unp)],[c_2]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19000,plain,
% 11.38/1.93      ( arAF0_k3_subset_1_0_1(X0) = arAF0_k4_xboole_0_0_1(X0)
% 11.38/1.93      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(predicate_to_equality,[status(thm)],[c_18901]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19276,plain,
% 11.38/1.93      ( arAF0_k3_subset_1_0_1(u1_struct_0(sK0)) = arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19003,c_19000]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_3,plain,
% 11.38/1.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.38/1.93      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 11.38/1.93      inference(cnf_transformation,[],[f23]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_18902,plain,
% 11.38/1.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.38/1.93      | m1_subset_1(arAF0_k3_subset_1_0_1(X1),k1_zfmisc_1(X1))
% 11.38/1.93      | ~ iProver_ARSWP_54 ),
% 11.38/1.93      inference(arg_filter_abstr,[status(unp)],[c_3]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_18999,plain,
% 11.38/1.93      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.38/1.93      | m1_subset_1(arAF0_k3_subset_1_0_1(X1),k1_zfmisc_1(X1)) = iProver_top
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top ),
% 11.38/1.93      inference(predicate_to_equality,[status(thm)],[c_18902]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19372,plain,
% 11.38/1.93      ( m1_subset_1(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19003,c_18999]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19506,plain,
% 11.38/1.93      ( m1_subset_1(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19276,c_19372]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_4,plain,
% 11.38/1.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.38/1.93      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.38/1.93      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 11.38/1.93      inference(cnf_transformation,[],[f24]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19005,plain,
% 11.38/1.93      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 11.38/1.93      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 11.38/1.93      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 11.38/1.93      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19507,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),X0) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),X0)
% 11.38/1.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19372,c_19005]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_20237,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19506,c_19507]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_21271,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19276,c_20237]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_20064,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),X0) = k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),X0)
% 11.38/1.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19506,c_19005]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_20509,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19506,c_20064]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_21912,plain,
% 11.38/1.93      ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_21271,c_20509]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_22472,plain,
% 11.38/1.93      ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),u1_struct_0(sK0))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top
% 11.38/1.93      | iProver_ARSWP_52 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_21912,c_19001]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_22655,plain,
% 11.38/1.93      ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),u1_struct_0(sK0)) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),u1_struct_0(sK0))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top
% 11.38/1.93      | iProver_ARSWP_52 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19001,c_22472]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_20508,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19372,c_20064]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_21100,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19276,c_20508]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_21911,plain,
% 11.38/1.93      ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_21271,c_21100]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_22253,plain,
% 11.38/1.93      ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),u1_struct_0(sK0))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top
% 11.38/1.93      | iProver_ARSWP_52 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_21911,c_19001]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_20236,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19372,c_19507]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_20660,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19276,c_20236]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_21913,plain,
% 11.38/1.93      ( k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_21271,c_20660]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_21558,plain,
% 11.38/1.93      ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_21100,c_20660]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_21557,plain,
% 11.38/1.93      ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_21100,c_20509]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_21548,plain,
% 11.38/1.93      ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_20660,c_20509]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_20507,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),sK1) = k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),sK1)
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19003,c_20064]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_20235,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),sK1) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),sK1)
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19003,c_19507]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_20381,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),sK1) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),sK1)
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19276,c_20235]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_20861,plain,
% 11.38/1.93      ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),sK1) = k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),sK1)
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_20507,c_20381]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19378,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 11.38/1.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19003,c_19005]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19664,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) = k2_xboole_0(sK1,arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19372,c_19378]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19904,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(sK1,arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19276,c_19664]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_20068,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(sK1,arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19506,c_19378]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_20847,plain,
% 11.38/1.93      ( k2_xboole_0(sK1,arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) = k2_xboole_0(sK1,arAF0_k3_subset_1_0_1(u1_struct_0(sK0)))
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19904,c_20068]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_6,negated_conjecture,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
% 11.38/1.93      inference(cnf_transformation,[],[f27]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_18903,negated_conjecture,
% 11.38/1.93      ( ~ iProver_ARSWP_55
% 11.38/1.93      | k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) != k2_struct_0(sK0) ),
% 11.38/1.93      inference(arg_filter_abstr,[status(unp)],[c_6]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_18998,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) != k2_struct_0(sK0)
% 11.38/1.93      | iProver_ARSWP_55 != iProver_top ),
% 11.38/1.93      inference(predicate_to_equality,[status(thm)],[c_18903]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19905,plain,
% 11.38/1.93      ( k2_xboole_0(sK1,arAF0_k3_subset_1_0_1(u1_struct_0(sK0))) != k2_struct_0(sK0)
% 11.38/1.93      | iProver_ARSWP_55 != iProver_top
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19664,c_18998]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_20058,plain,
% 11.38/1.93      ( k2_xboole_0(sK1,arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) != k2_struct_0(sK0)
% 11.38/1.93      | iProver_ARSWP_55 != iProver_top
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19276,c_19905]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_5,plain,
% 11.38/1.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.38/1.93      inference(cnf_transformation,[],[f25]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19004,plain,
% 11.38/1.93      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.38/1.93      | r1_tarski(X0,X1) = iProver_top ),
% 11.38/1.93      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19510,plain,
% 11.38/1.93      ( r1_tarski(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),u1_struct_0(sK0)) = iProver_top
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19372,c_19004]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19646,plain,
% 11.38/1.93      ( r1_tarski(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),u1_struct_0(sK0)) = iProver_top
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19276,c_19510]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_0,plain,
% 11.38/1.93      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.38/1.93      inference(cnf_transformation,[],[f20]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19006,plain,
% 11.38/1.93      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.38/1.93      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19899,plain,
% 11.38/1.93      ( k2_xboole_0(arAF0_k4_xboole_0_0_1(u1_struct_0(sK0)),u1_struct_0(sK0)) = u1_struct_0(sK0)
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19646,c_19006]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19647,plain,
% 11.38/1.93      ( k2_xboole_0(arAF0_k3_subset_1_0_1(u1_struct_0(sK0)),u1_struct_0(sK0)) = u1_struct_0(sK0)
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19510,c_19006]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19501,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),sK1,arAF0_k4_xboole_0_0_1(u1_struct_0(sK0))) != k2_struct_0(sK0)
% 11.38/1.93      | iProver_ARSWP_55 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19276,c_18998]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_20969,plain,
% 11.38/1.93      ( k2_xboole_0(sK1,u1_struct_0(sK0)) != k2_struct_0(sK0)
% 11.38/1.93      | iProver_ARSWP_55 != iProver_top
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top
% 11.38/1.93      | iProver_ARSWP_52 != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19001,c_20058]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19214,plain,
% 11.38/1.93      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19003,c_19004]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19218,plain,
% 11.38/1.93      ( k2_xboole_0(sK1,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19214,c_19006]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_20970,plain,
% 11.38/1.93      ( k2_struct_0(sK0) != u1_struct_0(sK0)
% 11.38/1.93      | iProver_ARSWP_55 != iProver_top
% 11.38/1.93      | iProver_ARSWP_54 != iProver_top
% 11.38/1.93      | iProver_ARSWP_53 != iProver_top
% 11.38/1.93      | iProver_ARSWP_52 != iProver_top ),
% 11.38/1.93      inference(light_normalisation,[status(thm)],[c_20969,c_19218]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_3481,plain,
% 11.38/1.93      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.38/1.93      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_3485,plain,
% 11.38/1.93      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.38/1.93      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.38/1.93      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_3811,plain,
% 11.38/1.93      ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_3481,c_3485]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_3484,plain,
% 11.38/1.93      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.38/1.93      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 11.38/1.93      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_4008,plain,
% 11.38/1.93      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.38/1.93      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_3811,c_3484]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_8,plain,
% 11.38/1.93      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.38/1.93      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_4336,plain,
% 11.38/1.93      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.38/1.93      inference(global_propositional_subsumption,[status(thm)],[c_4008,c_8]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_3483,plain,
% 11.38/1.93      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 11.38/1.93      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 11.38/1.93      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 11.38/1.93      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_3918,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 11.38/1.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_3481,c_3483]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_4344,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) = k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_4336,c_3918]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_3482,plain,
% 11.38/1.93      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.38/1.93      | r1_tarski(X0,X1) = iProver_top ),
% 11.38/1.93      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_3719,plain,
% 11.38/1.93      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_3481,c_3482]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_3486,plain,
% 11.38/1.93      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.38/1.93      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_3723,plain,
% 11.38/1.93      ( k2_xboole_0(sK1,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_3719,c_3486]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_4346,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) = u1_struct_0(sK0) ),
% 11.38/1.93      inference(demodulation,[status(thm)],[c_4344,c_1,c_3723]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_4007,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
% 11.38/1.93      inference(demodulation,[status(thm)],[c_3811,c_6]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_4500,plain,
% 11.38/1.93      ( k2_struct_0(sK0) != u1_struct_0(sK0) ),
% 11.38/1.93      inference(demodulation,[status(thm)],[c_4346,c_4007]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_21274,plain,
% 11.38/1.93      ( k2_struct_0(sK0) != u1_struct_0(sK0) ),
% 11.38/1.93      inference(global_propositional_subsumption,
% 11.38/1.93                [status(thm)],
% 11.38/1.93                [c_20970,c_4500]) ).
% 11.38/1.93  
% 11.38/1.93  cnf(c_19663,plain,
% 11.38/1.93      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) ),
% 11.38/1.93      inference(superposition,[status(thm)],[c_19003,c_19378]) ).
% 11.38/1.93  
% 11.38/1.93  
% 11.38/1.93  % SZS output end Saturation for theBenchmark.p
% 11.38/1.93  
% 11.38/1.93  ------                               Statistics
% 11.38/1.93  
% 11.38/1.93  ------ Selected
% 11.38/1.93  
% 11.38/1.93  total_time:                             1.325
% 11.38/1.93  
%------------------------------------------------------------------------------
