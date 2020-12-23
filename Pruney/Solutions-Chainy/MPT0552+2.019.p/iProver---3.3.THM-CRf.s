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
% DateTime   : Thu Dec  3 11:46:38 EST 2020

% Result     : Theorem 31.87s
% Output     : CNFRefutation 31.87s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 284 expanded)
%              Number of clauses        :   32 (  81 expanded)
%              Number of leaves         :   12 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :  143 ( 494 expanded)
%              Number of equality atoms :   61 ( 200 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f49,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f33,f45,f45])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f45])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_enumset1(k7_relat_1(X2,X0),k7_relat_1(X2,X0),k7_relat_1(X2,X0),k7_relat_1(X2,X1))) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f39,f46,f46])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f31,f46])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f46])).

fof(f44,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f44,f46,f46])).

cnf(c_5,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4608,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_enumset1(k7_relat_1(X0,X1),k7_relat_1(X0,X1),k7_relat_1(X0,X1),k7_relat_1(X0,X2))) = k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4612,plain,
    ( k1_setfam_1(k2_enumset1(k7_relat_1(X0,X1),k7_relat_1(X0,X1),k7_relat_1(X0,X1),k7_relat_1(X0,X2))) = k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6439,plain,
    ( k1_setfam_1(k2_enumset1(k7_relat_1(sK2,X0),k7_relat_1(sK2,X0),k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) = k7_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_4608,c_4612])).

cnf(c_3,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_4616,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6912,plain,
    ( r1_tarski(k7_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k7_relat_1(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6439,c_4616])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_4611,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5067,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_4608,c_4611])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4610,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5572,plain,
    ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) = iProver_top
    | r1_tarski(k7_relat_1(sK2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5067,c_4610])).

cnf(c_14,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_4709,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4710,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4709])).

cnf(c_5833,plain,
    ( v1_relat_1(X1) != iProver_top
    | r1_tarski(k7_relat_1(sK2,X0),X1) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5572,c_14,c_4710])).

cnf(c_5834,plain,
    ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) = iProver_top
    | r1_tarski(k7_relat_1(sK2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5833])).

cnf(c_5842,plain,
    ( r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = iProver_top
    | r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5067,c_5834])).

cnf(c_7226,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k9_relat_1(sK2,X0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6912,c_5842])).

cnf(c_96057,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k9_relat_1(sK2,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7226,c_14,c_4710])).

cnf(c_96092,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k9_relat_1(sK2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_96057])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4615,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4609,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5554,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4615,c_4609])).

cnf(c_96972,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_96092,c_5554])).

cnf(c_97084,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_96972,c_96057])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.87/4.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.87/4.49  
% 31.87/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.87/4.49  
% 31.87/4.49  ------  iProver source info
% 31.87/4.49  
% 31.87/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.87/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.87/4.49  git: non_committed_changes: false
% 31.87/4.49  git: last_make_outside_of_git: false
% 31.87/4.49  
% 31.87/4.49  ------ 
% 31.87/4.49  ------ Parsing...
% 31.87/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.87/4.49  ------ Proving...
% 31.87/4.49  ------ Problem Properties 
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  clauses                                 13
% 31.87/4.49  conjectures                             2
% 31.87/4.49  EPR                                     3
% 31.87/4.49  Horn                                    13
% 31.87/4.49  unary                                   5
% 31.87/4.49  binary                                  4
% 31.87/4.49  lits                                    27
% 31.87/4.49  lits eq                                 4
% 31.87/4.49  fd_pure                                 0
% 31.87/4.49  fd_pseudo                               0
% 31.87/4.49  fd_cond                                 0
% 31.87/4.49  fd_pseudo_cond                          1
% 31.87/4.49  AC symbols                              0
% 31.87/4.49  
% 31.87/4.49  ------ Input Options Time Limit: Unbounded
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing...
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 31.87/4.49  Current options:
% 31.87/4.49  ------ 
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  ------ Proving...
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.87/4.49  
% 31.87/4.49  ------ Proving...
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.87/4.49  
% 31.87/4.49  ------ Proving...
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.87/4.49  
% 31.87/4.49  ------ Proving...
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.87/4.49  
% 31.87/4.49  ------ Proving...
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.87/4.49  
% 31.87/4.49  ------ Proving...
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.87/4.49  
% 31.87/4.49  ------ Proving...
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.87/4.49  
% 31.87/4.49  ------ Proving...
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.87/4.49  
% 31.87/4.49  ------ Proving...
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.87/4.49  
% 31.87/4.49  ------ Proving...
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.87/4.49  
% 31.87/4.49  ------ Proving...
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.87/4.49  
% 31.87/4.49  ------ Proving...
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.87/4.49  
% 31.87/4.49  ------ Proving...
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  % SZS status Theorem for theBenchmark.p
% 31.87/4.49  
% 31.87/4.49   Resolution empty clause
% 31.87/4.49  
% 31.87/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.87/4.49  
% 31.87/4.49  fof(f4,axiom,(
% 31.87/4.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 31.87/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f33,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f4])).
% 31.87/4.49  
% 31.87/4.49  fof(f5,axiom,(
% 31.87/4.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 31.87/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f34,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f5])).
% 31.87/4.49  
% 31.87/4.49  fof(f6,axiom,(
% 31.87/4.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 31.87/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f35,plain,(
% 31.87/4.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f6])).
% 31.87/4.49  
% 31.87/4.49  fof(f45,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 31.87/4.49    inference(definition_unfolding,[],[f34,f35])).
% 31.87/4.49  
% 31.87/4.49  fof(f49,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 31.87/4.49    inference(definition_unfolding,[],[f33,f45,f45])).
% 31.87/4.49  
% 31.87/4.49  fof(f13,conjecture,(
% 31.87/4.49    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 31.87/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f14,negated_conjecture,(
% 31.87/4.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 31.87/4.49    inference(negated_conjecture,[],[f13])).
% 31.87/4.49  
% 31.87/4.49  fof(f23,plain,(
% 31.87/4.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 31.87/4.49    inference(ennf_transformation,[],[f14])).
% 31.87/4.49  
% 31.87/4.49  fof(f26,plain,(
% 31.87/4.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 31.87/4.49    introduced(choice_axiom,[])).
% 31.87/4.49  
% 31.87/4.49  fof(f27,plain,(
% 31.87/4.49    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 31.87/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26])).
% 31.87/4.49  
% 31.87/4.49  fof(f43,plain,(
% 31.87/4.49    v1_relat_1(sK2)),
% 31.87/4.49    inference(cnf_transformation,[],[f27])).
% 31.87/4.49  
% 31.87/4.49  fof(f10,axiom,(
% 31.87/4.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 31.87/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f19,plain,(
% 31.87/4.49    ! [X0,X1,X2] : (k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 31.87/4.49    inference(ennf_transformation,[],[f10])).
% 31.87/4.49  
% 31.87/4.49  fof(f39,plain,(
% 31.87/4.49    ( ! [X2,X0,X1] : (k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f19])).
% 31.87/4.49  
% 31.87/4.49  fof(f7,axiom,(
% 31.87/4.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 31.87/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f36,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 31.87/4.49    inference(cnf_transformation,[],[f7])).
% 31.87/4.49  
% 31.87/4.49  fof(f46,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 31.87/4.49    inference(definition_unfolding,[],[f36,f45])).
% 31.87/4.49  
% 31.87/4.49  fof(f51,plain,(
% 31.87/4.49    ( ! [X2,X0,X1] : (k1_setfam_1(k2_enumset1(k7_relat_1(X2,X0),k7_relat_1(X2,X0),k7_relat_1(X2,X0),k7_relat_1(X2,X1))) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 31.87/4.49    inference(definition_unfolding,[],[f39,f46,f46])).
% 31.87/4.49  
% 31.87/4.49  fof(f2,axiom,(
% 31.87/4.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 31.87/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f31,plain,(
% 31.87/4.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f2])).
% 31.87/4.49  
% 31.87/4.49  fof(f47,plain,(
% 31.87/4.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 31.87/4.49    inference(definition_unfolding,[],[f31,f46])).
% 31.87/4.49  
% 31.87/4.49  fof(f11,axiom,(
% 31.87/4.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 31.87/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f20,plain,(
% 31.87/4.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.87/4.49    inference(ennf_transformation,[],[f11])).
% 31.87/4.49  
% 31.87/4.49  fof(f40,plain,(
% 31.87/4.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f20])).
% 31.87/4.49  
% 31.87/4.49  fof(f12,axiom,(
% 31.87/4.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 31.87/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f21,plain,(
% 31.87/4.49    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.87/4.49    inference(ennf_transformation,[],[f12])).
% 31.87/4.49  
% 31.87/4.49  fof(f22,plain,(
% 31.87/4.49    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.87/4.49    inference(flattening,[],[f21])).
% 31.87/4.49  
% 31.87/4.49  fof(f42,plain,(
% 31.87/4.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f22])).
% 31.87/4.49  
% 31.87/4.49  fof(f8,axiom,(
% 31.87/4.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 31.87/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f17,plain,(
% 31.87/4.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 31.87/4.49    inference(ennf_transformation,[],[f8])).
% 31.87/4.49  
% 31.87/4.49  fof(f37,plain,(
% 31.87/4.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f17])).
% 31.87/4.49  
% 31.87/4.49  fof(f3,axiom,(
% 31.87/4.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 31.87/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.87/4.49  
% 31.87/4.49  fof(f15,plain,(
% 31.87/4.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 31.87/4.49    inference(ennf_transformation,[],[f3])).
% 31.87/4.49  
% 31.87/4.49  fof(f16,plain,(
% 31.87/4.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 31.87/4.49    inference(flattening,[],[f15])).
% 31.87/4.49  
% 31.87/4.49  fof(f32,plain,(
% 31.87/4.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 31.87/4.49    inference(cnf_transformation,[],[f16])).
% 31.87/4.49  
% 31.87/4.49  fof(f48,plain,(
% 31.87/4.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 31.87/4.49    inference(definition_unfolding,[],[f32,f46])).
% 31.87/4.49  
% 31.87/4.49  fof(f44,plain,(
% 31.87/4.49    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 31.87/4.49    inference(cnf_transformation,[],[f27])).
% 31.87/4.49  
% 31.87/4.49  fof(f52,plain,(
% 31.87/4.49    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 31.87/4.49    inference(definition_unfolding,[],[f44,f46,f46])).
% 31.87/4.49  
% 31.87/4.49  cnf(c_5,plain,
% 31.87/4.49      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 31.87/4.49      inference(cnf_transformation,[],[f49]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_13,negated_conjecture,
% 31.87/4.49      ( v1_relat_1(sK2) ),
% 31.87/4.49      inference(cnf_transformation,[],[f43]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_4608,plain,
% 31.87/4.49      ( v1_relat_1(sK2) = iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_8,plain,
% 31.87/4.49      ( ~ v1_relat_1(X0)
% 31.87/4.49      | k1_setfam_1(k2_enumset1(k7_relat_1(X0,X1),k7_relat_1(X0,X1),k7_relat_1(X0,X1),k7_relat_1(X0,X2))) = k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
% 31.87/4.49      inference(cnf_transformation,[],[f51]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_4612,plain,
% 31.87/4.49      ( k1_setfam_1(k2_enumset1(k7_relat_1(X0,X1),k7_relat_1(X0,X1),k7_relat_1(X0,X1),k7_relat_1(X0,X2))) = k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
% 31.87/4.49      | v1_relat_1(X0) != iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_6439,plain,
% 31.87/4.49      ( k1_setfam_1(k2_enumset1(k7_relat_1(sK2,X0),k7_relat_1(sK2,X0),k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) = k7_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_4608,c_4612]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_3,plain,
% 31.87/4.49      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
% 31.87/4.49      inference(cnf_transformation,[],[f47]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_4616,plain,
% 31.87/4.49      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_6912,plain,
% 31.87/4.49      ( r1_tarski(k7_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k7_relat_1(sK2,X0)) = iProver_top ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_6439,c_4616]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_9,plain,
% 31.87/4.49      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 31.87/4.49      inference(cnf_transformation,[],[f40]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_4611,plain,
% 31.87/4.49      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 31.87/4.49      | v1_relat_1(X0) != iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_5067,plain,
% 31.87/4.49      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_4608,c_4611]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_10,plain,
% 31.87/4.49      ( ~ r1_tarski(X0,X1)
% 31.87/4.49      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 31.87/4.49      | ~ v1_relat_1(X0)
% 31.87/4.49      | ~ v1_relat_1(X1) ),
% 31.87/4.49      inference(cnf_transformation,[],[f42]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_4610,plain,
% 31.87/4.49      ( r1_tarski(X0,X1) != iProver_top
% 31.87/4.49      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 31.87/4.49      | v1_relat_1(X0) != iProver_top
% 31.87/4.49      | v1_relat_1(X1) != iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_5572,plain,
% 31.87/4.49      ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) = iProver_top
% 31.87/4.49      | r1_tarski(k7_relat_1(sK2,X0),X1) != iProver_top
% 31.87/4.49      | v1_relat_1(X1) != iProver_top
% 31.87/4.49      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_5067,c_4610]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_14,plain,
% 31.87/4.49      ( v1_relat_1(sK2) = iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_6,plain,
% 31.87/4.49      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 31.87/4.49      inference(cnf_transformation,[],[f37]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_4709,plain,
% 31.87/4.49      ( v1_relat_1(k7_relat_1(sK2,X0)) | ~ v1_relat_1(sK2) ),
% 31.87/4.49      inference(instantiation,[status(thm)],[c_6]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_4710,plain,
% 31.87/4.49      ( v1_relat_1(k7_relat_1(sK2,X0)) = iProver_top
% 31.87/4.49      | v1_relat_1(sK2) != iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_4709]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_5833,plain,
% 31.87/4.49      ( v1_relat_1(X1) != iProver_top
% 31.87/4.49      | r1_tarski(k7_relat_1(sK2,X0),X1) != iProver_top
% 31.87/4.49      | r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) = iProver_top ),
% 31.87/4.49      inference(global_propositional_subsumption,
% 31.87/4.49                [status(thm)],
% 31.87/4.49                [c_5572,c_14,c_4710]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_5834,plain,
% 31.87/4.49      ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(X1)) = iProver_top
% 31.87/4.49      | r1_tarski(k7_relat_1(sK2,X0),X1) != iProver_top
% 31.87/4.49      | v1_relat_1(X1) != iProver_top ),
% 31.87/4.49      inference(renaming,[status(thm)],[c_5833]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_5842,plain,
% 31.87/4.49      ( r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = iProver_top
% 31.87/4.49      | r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) != iProver_top
% 31.87/4.49      | v1_relat_1(k7_relat_1(sK2,X1)) != iProver_top ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_5067,c_5834]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_7226,plain,
% 31.87/4.49      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k9_relat_1(sK2,X0)) = iProver_top
% 31.87/4.49      | v1_relat_1(k7_relat_1(sK2,X0)) != iProver_top ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_6912,c_5842]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_96057,plain,
% 31.87/4.49      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k9_relat_1(sK2,X0)) = iProver_top ),
% 31.87/4.49      inference(global_propositional_subsumption,
% 31.87/4.49                [status(thm)],
% 31.87/4.49                [c_7226,c_14,c_4710]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_96092,plain,
% 31.87/4.49      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k9_relat_1(sK2,X1)) = iProver_top ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_5,c_96057]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_4,plain,
% 31.87/4.49      ( ~ r1_tarski(X0,X1)
% 31.87/4.49      | ~ r1_tarski(X0,X2)
% 31.87/4.49      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
% 31.87/4.49      inference(cnf_transformation,[],[f48]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_4615,plain,
% 31.87/4.49      ( r1_tarski(X0,X1) != iProver_top
% 31.87/4.49      | r1_tarski(X0,X2) != iProver_top
% 31.87/4.49      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_12,negated_conjecture,
% 31.87/4.49      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
% 31.87/4.49      inference(cnf_transformation,[],[f52]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_4609,plain,
% 31.87/4.49      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) != iProver_top ),
% 31.87/4.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_5554,plain,
% 31.87/4.49      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK1)) != iProver_top
% 31.87/4.49      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) != iProver_top ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_4615,c_4609]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_96972,plain,
% 31.87/4.49      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k9_relat_1(sK2,sK0)) != iProver_top ),
% 31.87/4.49      inference(superposition,[status(thm)],[c_96092,c_5554]) ).
% 31.87/4.49  
% 31.87/4.49  cnf(c_97084,plain,
% 31.87/4.49      ( $false ),
% 31.87/4.49      inference(forward_subsumption_resolution,[status(thm)],[c_96972,c_96057]) ).
% 31.87/4.49  
% 31.87/4.49  
% 31.87/4.49  % SZS output end CNFRefutation for theBenchmark.p
% 31.87/4.49  
% 31.87/4.49  ------                               Statistics
% 31.87/4.49  
% 31.87/4.49  ------ Selected
% 31.87/4.49  
% 31.87/4.49  total_time:                             3.802
% 31.87/4.49  
%------------------------------------------------------------------------------
