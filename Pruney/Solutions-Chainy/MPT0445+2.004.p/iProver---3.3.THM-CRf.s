%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:06 EST 2020

% Result     : Theorem 19.33s
% Output     : CNFRefutation 19.33s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 144 expanded)
%              Number of clauses        :   54 (  63 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  172 ( 312 expanded)
%              Number of equality atoms :   83 ( 119 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) ),
    inference(definition_unfolding,[],[f18,f22,f22,f23])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(X0,sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16,f15])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f25,f22,f22])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f19,f23,f22])).

fof(f28,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_103,plain,
    ( ~ r1_tarski(X0_36,X1_36)
    | r1_tarski(X2_36,X3_36)
    | X2_36 != X0_36
    | X3_36 != X1_36 ),
    theory(equality)).

cnf(c_266,plain,
    ( ~ r1_tarski(X0_36,X1_36)
    | r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
    | k2_relat_1(sK0) != X0_36
    | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != X1_36 ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_294,plain,
    ( ~ r1_tarski(k2_relat_1(X0_36),X1_36)
    | r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
    | k2_relat_1(sK0) != k2_relat_1(X0_36)
    | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != X1_36 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_62875,plain,
    ( ~ r1_tarski(k2_relat_1(X0_36),k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))))
    | r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
    | k2_relat_1(sK0) != k2_relat_1(X0_36)
    | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_62877,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))))
    | r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
    | k2_relat_1(sK0) != k2_relat_1(sK0)
    | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_62875])).

cnf(c_98,plain,
    ( X0_36 != X1_36
    | X2_36 != X1_36
    | X2_36 = X0_36 ),
    theory(equality)).

cnf(c_431,plain,
    ( X0_36 != X1_36
    | X0_36 = k2_relat_1(X2_36)
    | k2_relat_1(X2_36) != X1_36 ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_756,plain,
    ( X0_36 != k2_relat_1(X1_36)
    | X0_36 = k2_relat_1(X2_36)
    | k2_relat_1(X2_36) != k2_relat_1(X1_36) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_1013,plain,
    ( k2_relat_1(X0_36) != k2_relat_1(k3_tarski(k2_tarski(X1_36,X2_36)))
    | k3_tarski(k2_tarski(k2_relat_1(X1_36),k2_relat_1(X2_36))) = k2_relat_1(X0_36)
    | k3_tarski(k2_tarski(k2_relat_1(X1_36),k2_relat_1(X2_36))) != k2_relat_1(k3_tarski(k2_tarski(X1_36,X2_36))) ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_26408,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) != k2_relat_1(k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36))))
    | k3_tarski(k2_tarski(k2_relat_1(X0_36),k2_relat_1(k6_subset_1(X1_36,X0_36)))) = k2_relat_1(k3_tarski(k2_tarski(X0_36,X1_36)))
    | k3_tarski(k2_tarski(k2_relat_1(X0_36),k2_relat_1(k6_subset_1(X1_36,X0_36)))) != k2_relat_1(k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36)))) ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_62869,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) != k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
    | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
    | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) = k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_26408])).

cnf(c_96,plain,
    ( X0_36 = X0_36 ),
    theory(equality)).

cnf(c_4624,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) = k2_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_20478,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) = k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_4624])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_94,plain,
    ( k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36))) = k3_tarski(k2_tarski(X0_36,X1_36)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_11842,plain,
    ( k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))) = k3_tarski(k2_tarski(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_1014,plain,
    ( k2_relat_1(X0_36) != k2_relat_1(X0_36)
    | k2_relat_1(X1_36) != k2_relat_1(X0_36)
    | k2_relat_1(X0_36) = k2_relat_1(X1_36) ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_1885,plain,
    ( k2_relat_1(X0_36) != k2_relat_1(X0_36)
    | k2_relat_1(X0_36) = k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
    | k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) != k2_relat_1(X0_36) ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_10454,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k2_tarski(sK1,sK0)))
    | k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) = k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
    | k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) != k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_1885])).

cnf(c_105,plain,
    ( X0_36 != X1_36
    | k2_relat_1(X0_36) = k2_relat_1(X1_36) ),
    theory(equality)).

cnf(c_1353,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) = k2_relat_1(X2_36)
    | k3_tarski(k2_tarski(X0_36,X1_36)) != X2_36 ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_3507,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36)))) = k2_relat_1(k3_tarski(k2_tarski(X0_36,X1_36)))
    | k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36))) != k3_tarski(k2_tarski(X0_36,X1_36)) ),
    inference(instantiation,[status(thm)],[c_1353])).

cnf(c_10453,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) = k2_relat_1(k3_tarski(k2_tarski(sK1,sK0)))
    | k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))) != k3_tarski(k2_tarski(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_3507])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_86,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_247,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_86])).

cnf(c_7,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_87,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_246,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_87])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_89,plain,
    ( ~ v1_relat_1(X0_36)
    | ~ v1_relat_1(X1_36)
    | k3_tarski(k2_tarski(k2_relat_1(X0_36),k2_relat_1(X1_36))) = k2_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_244,plain,
    ( k3_tarski(k2_tarski(k2_relat_1(X0_36),k2_relat_1(X1_36))) = k2_relat_1(k3_tarski(k2_tarski(X0_36,X1_36)))
    | v1_relat_1(X0_36) != iProver_top
    | v1_relat_1(X1_36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_89])).

cnf(c_996,plain,
    ( k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(X0_36))) = k2_relat_1(k3_tarski(k2_tarski(sK1,X0_36)))
    | v1_relat_1(X0_36) != iProver_top ),
    inference(superposition,[status(thm)],[c_246,c_244])).

cnf(c_1296,plain,
    ( k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(sK0))) = k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_247,c_996])).

cnf(c_3,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_91,plain,
    ( k2_tarski(X0_36,X1_36) = k2_tarski(X1_36,X0_36) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_92,plain,
    ( r1_tarski(X0_36,k3_tarski(k2_tarski(X0_36,X1_36))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_242,plain,
    ( r1_tarski(X0_36,k3_tarski(k2_tarski(X0_36,X1_36))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_92])).

cnf(c_434,plain,
    ( r1_tarski(X0_36,k3_tarski(k2_tarski(X1_36,X0_36))) = iProver_top ),
    inference(superposition,[status(thm)],[c_91,c_242])).

cnf(c_1387,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK1,sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1296,c_434])).

cnf(c_1400,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK1,sK0)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1387])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_90,plain,
    ( ~ v1_relat_1(X0_36)
    | v1_relat_1(k6_subset_1(X0_36,X1_36)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_593,plain,
    ( v1_relat_1(k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_440,plain,
    ( ~ v1_relat_1(k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) = k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_93,plain,
    ( ~ r1_tarski(X0_36,k3_tarski(k2_tarski(X1_36,X2_36)))
    | r1_tarski(k6_subset_1(X0_36,X1_36),X2_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_258,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
    | ~ r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))) ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_113,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_111,plain,
    ( k2_relat_1(sK0) = k2_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_62877,c_62869,c_20478,c_11842,c_10454,c_10453,c_1400,c_593,c_440,c_258,c_113,c_111,c_6,c_7,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:15:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 19.33/2.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.33/2.97  
% 19.33/2.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.33/2.97  
% 19.33/2.97  ------  iProver source info
% 19.33/2.97  
% 19.33/2.97  git: date: 2020-06-30 10:37:57 +0100
% 19.33/2.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.33/2.97  git: non_committed_changes: false
% 19.33/2.97  git: last_make_outside_of_git: false
% 19.33/2.97  
% 19.33/2.97  ------ 
% 19.33/2.97  
% 19.33/2.97  ------ Input Options
% 19.33/2.97  
% 19.33/2.97  --out_options                           all
% 19.33/2.97  --tptp_safe_out                         true
% 19.33/2.97  --problem_path                          ""
% 19.33/2.97  --include_path                          ""
% 19.33/2.97  --clausifier                            res/vclausify_rel
% 19.33/2.97  --clausifier_options                    ""
% 19.33/2.97  --stdin                                 false
% 19.33/2.97  --stats_out                             all
% 19.33/2.97  
% 19.33/2.97  ------ General Options
% 19.33/2.97  
% 19.33/2.97  --fof                                   false
% 19.33/2.97  --time_out_real                         305.
% 19.33/2.97  --time_out_virtual                      -1.
% 19.33/2.97  --symbol_type_check                     false
% 19.33/2.97  --clausify_out                          false
% 19.33/2.97  --sig_cnt_out                           false
% 19.33/2.97  --trig_cnt_out                          false
% 19.33/2.97  --trig_cnt_out_tolerance                1.
% 19.33/2.97  --trig_cnt_out_sk_spl                   false
% 19.33/2.97  --abstr_cl_out                          false
% 19.33/2.97  
% 19.33/2.97  ------ Global Options
% 19.33/2.97  
% 19.33/2.97  --schedule                              default
% 19.33/2.97  --add_important_lit                     false
% 19.33/2.97  --prop_solver_per_cl                    1000
% 19.33/2.97  --min_unsat_core                        false
% 19.33/2.97  --soft_assumptions                      false
% 19.33/2.97  --soft_lemma_size                       3
% 19.33/2.97  --prop_impl_unit_size                   0
% 19.33/2.97  --prop_impl_unit                        []
% 19.33/2.97  --share_sel_clauses                     true
% 19.33/2.97  --reset_solvers                         false
% 19.33/2.97  --bc_imp_inh                            [conj_cone]
% 19.33/2.97  --conj_cone_tolerance                   3.
% 19.33/2.97  --extra_neg_conj                        none
% 19.33/2.97  --large_theory_mode                     true
% 19.33/2.97  --prolific_symb_bound                   200
% 19.33/2.97  --lt_threshold                          2000
% 19.33/2.97  --clause_weak_htbl                      true
% 19.33/2.97  --gc_record_bc_elim                     false
% 19.33/2.97  
% 19.33/2.97  ------ Preprocessing Options
% 19.33/2.97  
% 19.33/2.97  --preprocessing_flag                    true
% 19.33/2.97  --time_out_prep_mult                    0.1
% 19.33/2.97  --splitting_mode                        input
% 19.33/2.97  --splitting_grd                         true
% 19.33/2.97  --splitting_cvd                         false
% 19.33/2.97  --splitting_cvd_svl                     false
% 19.33/2.97  --splitting_nvd                         32
% 19.33/2.97  --sub_typing                            true
% 19.33/2.97  --prep_gs_sim                           true
% 19.33/2.97  --prep_unflatten                        true
% 19.33/2.97  --prep_res_sim                          true
% 19.33/2.97  --prep_upred                            true
% 19.33/2.97  --prep_sem_filter                       exhaustive
% 19.33/2.97  --prep_sem_filter_out                   false
% 19.33/2.97  --pred_elim                             true
% 19.33/2.97  --res_sim_input                         true
% 19.33/2.97  --eq_ax_congr_red                       true
% 19.33/2.97  --pure_diseq_elim                       true
% 19.33/2.97  --brand_transform                       false
% 19.33/2.97  --non_eq_to_eq                          false
% 19.33/2.97  --prep_def_merge                        true
% 19.33/2.97  --prep_def_merge_prop_impl              false
% 19.33/2.97  --prep_def_merge_mbd                    true
% 19.33/2.97  --prep_def_merge_tr_red                 false
% 19.33/2.97  --prep_def_merge_tr_cl                  false
% 19.33/2.97  --smt_preprocessing                     true
% 19.33/2.97  --smt_ac_axioms                         fast
% 19.33/2.97  --preprocessed_out                      false
% 19.33/2.97  --preprocessed_stats                    false
% 19.33/2.97  
% 19.33/2.97  ------ Abstraction refinement Options
% 19.33/2.97  
% 19.33/2.97  --abstr_ref                             []
% 19.33/2.97  --abstr_ref_prep                        false
% 19.33/2.97  --abstr_ref_until_sat                   false
% 19.33/2.97  --abstr_ref_sig_restrict                funpre
% 19.33/2.97  --abstr_ref_af_restrict_to_split_sk     false
% 19.33/2.97  --abstr_ref_under                       []
% 19.33/2.97  
% 19.33/2.97  ------ SAT Options
% 19.33/2.97  
% 19.33/2.97  --sat_mode                              false
% 19.33/2.97  --sat_fm_restart_options                ""
% 19.33/2.97  --sat_gr_def                            false
% 19.33/2.97  --sat_epr_types                         true
% 19.33/2.97  --sat_non_cyclic_types                  false
% 19.33/2.97  --sat_finite_models                     false
% 19.33/2.97  --sat_fm_lemmas                         false
% 19.33/2.97  --sat_fm_prep                           false
% 19.33/2.97  --sat_fm_uc_incr                        true
% 19.33/2.97  --sat_out_model                         small
% 19.33/2.97  --sat_out_clauses                       false
% 19.33/2.97  
% 19.33/2.97  ------ QBF Options
% 19.33/2.97  
% 19.33/2.97  --qbf_mode                              false
% 19.33/2.97  --qbf_elim_univ                         false
% 19.33/2.97  --qbf_dom_inst                          none
% 19.33/2.97  --qbf_dom_pre_inst                      false
% 19.33/2.97  --qbf_sk_in                             false
% 19.33/2.97  --qbf_pred_elim                         true
% 19.33/2.97  --qbf_split                             512
% 19.33/2.97  
% 19.33/2.97  ------ BMC1 Options
% 19.33/2.97  
% 19.33/2.97  --bmc1_incremental                      false
% 19.33/2.97  --bmc1_axioms                           reachable_all
% 19.33/2.97  --bmc1_min_bound                        0
% 19.33/2.97  --bmc1_max_bound                        -1
% 19.33/2.97  --bmc1_max_bound_default                -1
% 19.33/2.97  --bmc1_symbol_reachability              true
% 19.33/2.97  --bmc1_property_lemmas                  false
% 19.33/2.97  --bmc1_k_induction                      false
% 19.33/2.97  --bmc1_non_equiv_states                 false
% 19.33/2.97  --bmc1_deadlock                         false
% 19.33/2.97  --bmc1_ucm                              false
% 19.33/2.97  --bmc1_add_unsat_core                   none
% 19.33/2.97  --bmc1_unsat_core_children              false
% 19.33/2.97  --bmc1_unsat_core_extrapolate_axioms    false
% 19.33/2.97  --bmc1_out_stat                         full
% 19.33/2.97  --bmc1_ground_init                      false
% 19.33/2.97  --bmc1_pre_inst_next_state              false
% 19.33/2.97  --bmc1_pre_inst_state                   false
% 19.33/2.97  --bmc1_pre_inst_reach_state             false
% 19.33/2.97  --bmc1_out_unsat_core                   false
% 19.33/2.97  --bmc1_aig_witness_out                  false
% 19.33/2.97  --bmc1_verbose                          false
% 19.33/2.97  --bmc1_dump_clauses_tptp                false
% 19.33/2.97  --bmc1_dump_unsat_core_tptp             false
% 19.33/2.97  --bmc1_dump_file                        -
% 19.33/2.97  --bmc1_ucm_expand_uc_limit              128
% 19.33/2.97  --bmc1_ucm_n_expand_iterations          6
% 19.33/2.97  --bmc1_ucm_extend_mode                  1
% 19.33/2.97  --bmc1_ucm_init_mode                    2
% 19.33/2.97  --bmc1_ucm_cone_mode                    none
% 19.33/2.97  --bmc1_ucm_reduced_relation_type        0
% 19.33/2.97  --bmc1_ucm_relax_model                  4
% 19.33/2.97  --bmc1_ucm_full_tr_after_sat            true
% 19.33/2.97  --bmc1_ucm_expand_neg_assumptions       false
% 19.33/2.97  --bmc1_ucm_layered_model                none
% 19.33/2.97  --bmc1_ucm_max_lemma_size               10
% 19.33/2.97  
% 19.33/2.97  ------ AIG Options
% 19.33/2.97  
% 19.33/2.97  --aig_mode                              false
% 19.33/2.97  
% 19.33/2.97  ------ Instantiation Options
% 19.33/2.97  
% 19.33/2.97  --instantiation_flag                    true
% 19.33/2.97  --inst_sos_flag                         true
% 19.33/2.97  --inst_sos_phase                        true
% 19.33/2.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.33/2.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.33/2.97  --inst_lit_sel_side                     num_symb
% 19.33/2.97  --inst_solver_per_active                1400
% 19.33/2.97  --inst_solver_calls_frac                1.
% 19.33/2.97  --inst_passive_queue_type               priority_queues
% 19.33/2.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.33/2.97  --inst_passive_queues_freq              [25;2]
% 19.33/2.97  --inst_dismatching                      true
% 19.33/2.97  --inst_eager_unprocessed_to_passive     true
% 19.33/2.97  --inst_prop_sim_given                   true
% 19.33/2.97  --inst_prop_sim_new                     false
% 19.33/2.97  --inst_subs_new                         false
% 19.33/2.97  --inst_eq_res_simp                      false
% 19.33/2.97  --inst_subs_given                       false
% 19.33/2.97  --inst_orphan_elimination               true
% 19.33/2.97  --inst_learning_loop_flag               true
% 19.33/2.97  --inst_learning_start                   3000
% 19.33/2.97  --inst_learning_factor                  2
% 19.33/2.97  --inst_start_prop_sim_after_learn       3
% 19.33/2.97  --inst_sel_renew                        solver
% 19.33/2.97  --inst_lit_activity_flag                true
% 19.33/2.97  --inst_restr_to_given                   false
% 19.33/2.97  --inst_activity_threshold               500
% 19.33/2.97  --inst_out_proof                        true
% 19.33/2.97  
% 19.33/2.97  ------ Resolution Options
% 19.33/2.97  
% 19.33/2.97  --resolution_flag                       true
% 19.33/2.97  --res_lit_sel                           adaptive
% 19.33/2.97  --res_lit_sel_side                      none
% 19.33/2.97  --res_ordering                          kbo
% 19.33/2.97  --res_to_prop_solver                    active
% 19.33/2.97  --res_prop_simpl_new                    false
% 19.33/2.97  --res_prop_simpl_given                  true
% 19.33/2.97  --res_passive_queue_type                priority_queues
% 19.33/2.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.33/2.97  --res_passive_queues_freq               [15;5]
% 19.33/2.97  --res_forward_subs                      full
% 19.33/2.97  --res_backward_subs                     full
% 19.33/2.97  --res_forward_subs_resolution           true
% 19.33/2.97  --res_backward_subs_resolution          true
% 19.33/2.97  --res_orphan_elimination                true
% 19.33/2.97  --res_time_limit                        2.
% 19.33/2.97  --res_out_proof                         true
% 19.33/2.97  
% 19.33/2.97  ------ Superposition Options
% 19.33/2.97  
% 19.33/2.97  --superposition_flag                    true
% 19.33/2.97  --sup_passive_queue_type                priority_queues
% 19.33/2.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.33/2.97  --sup_passive_queues_freq               [8;1;4]
% 19.33/2.97  --demod_completeness_check              fast
% 19.33/2.97  --demod_use_ground                      true
% 19.33/2.97  --sup_to_prop_solver                    passive
% 19.33/2.97  --sup_prop_simpl_new                    true
% 19.33/2.97  --sup_prop_simpl_given                  true
% 19.33/2.97  --sup_fun_splitting                     true
% 19.33/2.97  --sup_smt_interval                      50000
% 19.33/2.97  
% 19.33/2.97  ------ Superposition Simplification Setup
% 19.33/2.97  
% 19.33/2.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.33/2.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.33/2.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.33/2.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.33/2.97  --sup_full_triv                         [TrivRules;PropSubs]
% 19.33/2.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.33/2.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.33/2.97  --sup_immed_triv                        [TrivRules]
% 19.33/2.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.33/2.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.33/2.97  --sup_immed_bw_main                     []
% 19.33/2.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.33/2.97  --sup_input_triv                        [Unflattening;TrivRules]
% 19.33/2.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.33/2.98  --sup_input_bw                          []
% 19.33/2.98  
% 19.33/2.98  ------ Combination Options
% 19.33/2.98  
% 19.33/2.98  --comb_res_mult                         3
% 19.33/2.98  --comb_sup_mult                         2
% 19.33/2.98  --comb_inst_mult                        10
% 19.33/2.98  
% 19.33/2.98  ------ Debug Options
% 19.33/2.98  
% 19.33/2.98  --dbg_backtrace                         false
% 19.33/2.98  --dbg_dump_prop_clauses                 false
% 19.33/2.98  --dbg_dump_prop_clauses_file            -
% 19.33/2.98  --dbg_out_stat                          false
% 19.33/2.98  ------ Parsing...
% 19.33/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.33/2.98  
% 19.33/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.33/2.98  
% 19.33/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.33/2.98  
% 19.33/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.33/2.98  ------ Proving...
% 19.33/2.98  ------ Problem Properties 
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  clauses                                 9
% 19.33/2.98  conjectures                             3
% 19.33/2.98  EPR                                     2
% 19.33/2.98  Horn                                    9
% 19.33/2.98  unary                                   6
% 19.33/2.98  binary                                  2
% 19.33/2.98  lits                                    13
% 19.33/2.98  lits eq                                 3
% 19.33/2.98  fd_pure                                 0
% 19.33/2.98  fd_pseudo                               0
% 19.33/2.98  fd_cond                                 0
% 19.33/2.98  fd_pseudo_cond                          0
% 19.33/2.98  AC symbols                              0
% 19.33/2.98  
% 19.33/2.98  ------ Schedule dynamic 5 is on 
% 19.33/2.98  
% 19.33/2.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  ------ 
% 19.33/2.98  Current options:
% 19.33/2.98  ------ 
% 19.33/2.98  
% 19.33/2.98  ------ Input Options
% 19.33/2.98  
% 19.33/2.98  --out_options                           all
% 19.33/2.98  --tptp_safe_out                         true
% 19.33/2.98  --problem_path                          ""
% 19.33/2.98  --include_path                          ""
% 19.33/2.98  --clausifier                            res/vclausify_rel
% 19.33/2.98  --clausifier_options                    ""
% 19.33/2.98  --stdin                                 false
% 19.33/2.98  --stats_out                             all
% 19.33/2.98  
% 19.33/2.98  ------ General Options
% 19.33/2.98  
% 19.33/2.98  --fof                                   false
% 19.33/2.98  --time_out_real                         305.
% 19.33/2.98  --time_out_virtual                      -1.
% 19.33/2.98  --symbol_type_check                     false
% 19.33/2.98  --clausify_out                          false
% 19.33/2.98  --sig_cnt_out                           false
% 19.33/2.98  --trig_cnt_out                          false
% 19.33/2.98  --trig_cnt_out_tolerance                1.
% 19.33/2.98  --trig_cnt_out_sk_spl                   false
% 19.33/2.98  --abstr_cl_out                          false
% 19.33/2.98  
% 19.33/2.98  ------ Global Options
% 19.33/2.98  
% 19.33/2.98  --schedule                              default
% 19.33/2.98  --add_important_lit                     false
% 19.33/2.98  --prop_solver_per_cl                    1000
% 19.33/2.98  --min_unsat_core                        false
% 19.33/2.98  --soft_assumptions                      false
% 19.33/2.98  --soft_lemma_size                       3
% 19.33/2.98  --prop_impl_unit_size                   0
% 19.33/2.98  --prop_impl_unit                        []
% 19.33/2.98  --share_sel_clauses                     true
% 19.33/2.98  --reset_solvers                         false
% 19.33/2.98  --bc_imp_inh                            [conj_cone]
% 19.33/2.98  --conj_cone_tolerance                   3.
% 19.33/2.98  --extra_neg_conj                        none
% 19.33/2.98  --large_theory_mode                     true
% 19.33/2.98  --prolific_symb_bound                   200
% 19.33/2.98  --lt_threshold                          2000
% 19.33/2.98  --clause_weak_htbl                      true
% 19.33/2.98  --gc_record_bc_elim                     false
% 19.33/2.98  
% 19.33/2.98  ------ Preprocessing Options
% 19.33/2.98  
% 19.33/2.98  --preprocessing_flag                    true
% 19.33/2.98  --time_out_prep_mult                    0.1
% 19.33/2.98  --splitting_mode                        input
% 19.33/2.98  --splitting_grd                         true
% 19.33/2.98  --splitting_cvd                         false
% 19.33/2.98  --splitting_cvd_svl                     false
% 19.33/2.98  --splitting_nvd                         32
% 19.33/2.98  --sub_typing                            true
% 19.33/2.98  --prep_gs_sim                           true
% 19.33/2.98  --prep_unflatten                        true
% 19.33/2.98  --prep_res_sim                          true
% 19.33/2.98  --prep_upred                            true
% 19.33/2.98  --prep_sem_filter                       exhaustive
% 19.33/2.98  --prep_sem_filter_out                   false
% 19.33/2.98  --pred_elim                             true
% 19.33/2.98  --res_sim_input                         true
% 19.33/2.98  --eq_ax_congr_red                       true
% 19.33/2.98  --pure_diseq_elim                       true
% 19.33/2.98  --brand_transform                       false
% 19.33/2.98  --non_eq_to_eq                          false
% 19.33/2.98  --prep_def_merge                        true
% 19.33/2.98  --prep_def_merge_prop_impl              false
% 19.33/2.98  --prep_def_merge_mbd                    true
% 19.33/2.98  --prep_def_merge_tr_red                 false
% 19.33/2.98  --prep_def_merge_tr_cl                  false
% 19.33/2.98  --smt_preprocessing                     true
% 19.33/2.98  --smt_ac_axioms                         fast
% 19.33/2.98  --preprocessed_out                      false
% 19.33/2.98  --preprocessed_stats                    false
% 19.33/2.98  
% 19.33/2.98  ------ Abstraction refinement Options
% 19.33/2.98  
% 19.33/2.98  --abstr_ref                             []
% 19.33/2.98  --abstr_ref_prep                        false
% 19.33/2.98  --abstr_ref_until_sat                   false
% 19.33/2.98  --abstr_ref_sig_restrict                funpre
% 19.33/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.33/2.98  --abstr_ref_under                       []
% 19.33/2.98  
% 19.33/2.98  ------ SAT Options
% 19.33/2.98  
% 19.33/2.98  --sat_mode                              false
% 19.33/2.98  --sat_fm_restart_options                ""
% 19.33/2.98  --sat_gr_def                            false
% 19.33/2.98  --sat_epr_types                         true
% 19.33/2.98  --sat_non_cyclic_types                  false
% 19.33/2.98  --sat_finite_models                     false
% 19.33/2.98  --sat_fm_lemmas                         false
% 19.33/2.98  --sat_fm_prep                           false
% 19.33/2.98  --sat_fm_uc_incr                        true
% 19.33/2.98  --sat_out_model                         small
% 19.33/2.98  --sat_out_clauses                       false
% 19.33/2.98  
% 19.33/2.98  ------ QBF Options
% 19.33/2.98  
% 19.33/2.98  --qbf_mode                              false
% 19.33/2.98  --qbf_elim_univ                         false
% 19.33/2.98  --qbf_dom_inst                          none
% 19.33/2.98  --qbf_dom_pre_inst                      false
% 19.33/2.98  --qbf_sk_in                             false
% 19.33/2.98  --qbf_pred_elim                         true
% 19.33/2.98  --qbf_split                             512
% 19.33/2.98  
% 19.33/2.98  ------ BMC1 Options
% 19.33/2.98  
% 19.33/2.98  --bmc1_incremental                      false
% 19.33/2.98  --bmc1_axioms                           reachable_all
% 19.33/2.98  --bmc1_min_bound                        0
% 19.33/2.98  --bmc1_max_bound                        -1
% 19.33/2.98  --bmc1_max_bound_default                -1
% 19.33/2.98  --bmc1_symbol_reachability              true
% 19.33/2.98  --bmc1_property_lemmas                  false
% 19.33/2.98  --bmc1_k_induction                      false
% 19.33/2.98  --bmc1_non_equiv_states                 false
% 19.33/2.98  --bmc1_deadlock                         false
% 19.33/2.98  --bmc1_ucm                              false
% 19.33/2.98  --bmc1_add_unsat_core                   none
% 19.33/2.98  --bmc1_unsat_core_children              false
% 19.33/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.33/2.98  --bmc1_out_stat                         full
% 19.33/2.98  --bmc1_ground_init                      false
% 19.33/2.98  --bmc1_pre_inst_next_state              false
% 19.33/2.98  --bmc1_pre_inst_state                   false
% 19.33/2.98  --bmc1_pre_inst_reach_state             false
% 19.33/2.98  --bmc1_out_unsat_core                   false
% 19.33/2.98  --bmc1_aig_witness_out                  false
% 19.33/2.98  --bmc1_verbose                          false
% 19.33/2.98  --bmc1_dump_clauses_tptp                false
% 19.33/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.33/2.98  --bmc1_dump_file                        -
% 19.33/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.33/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.33/2.98  --bmc1_ucm_extend_mode                  1
% 19.33/2.98  --bmc1_ucm_init_mode                    2
% 19.33/2.98  --bmc1_ucm_cone_mode                    none
% 19.33/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.33/2.98  --bmc1_ucm_relax_model                  4
% 19.33/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.33/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.33/2.98  --bmc1_ucm_layered_model                none
% 19.33/2.98  --bmc1_ucm_max_lemma_size               10
% 19.33/2.98  
% 19.33/2.98  ------ AIG Options
% 19.33/2.98  
% 19.33/2.98  --aig_mode                              false
% 19.33/2.98  
% 19.33/2.98  ------ Instantiation Options
% 19.33/2.98  
% 19.33/2.98  --instantiation_flag                    true
% 19.33/2.98  --inst_sos_flag                         true
% 19.33/2.98  --inst_sos_phase                        true
% 19.33/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.33/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.33/2.98  --inst_lit_sel_side                     none
% 19.33/2.98  --inst_solver_per_active                1400
% 19.33/2.98  --inst_solver_calls_frac                1.
% 19.33/2.98  --inst_passive_queue_type               priority_queues
% 19.33/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.33/2.98  --inst_passive_queues_freq              [25;2]
% 19.33/2.98  --inst_dismatching                      true
% 19.33/2.98  --inst_eager_unprocessed_to_passive     true
% 19.33/2.98  --inst_prop_sim_given                   true
% 19.33/2.98  --inst_prop_sim_new                     false
% 19.33/2.98  --inst_subs_new                         false
% 19.33/2.98  --inst_eq_res_simp                      false
% 19.33/2.98  --inst_subs_given                       false
% 19.33/2.98  --inst_orphan_elimination               true
% 19.33/2.98  --inst_learning_loop_flag               true
% 19.33/2.98  --inst_learning_start                   3000
% 19.33/2.98  --inst_learning_factor                  2
% 19.33/2.98  --inst_start_prop_sim_after_learn       3
% 19.33/2.98  --inst_sel_renew                        solver
% 19.33/2.98  --inst_lit_activity_flag                true
% 19.33/2.98  --inst_restr_to_given                   false
% 19.33/2.98  --inst_activity_threshold               500
% 19.33/2.98  --inst_out_proof                        true
% 19.33/2.98  
% 19.33/2.98  ------ Resolution Options
% 19.33/2.98  
% 19.33/2.98  --resolution_flag                       false
% 19.33/2.98  --res_lit_sel                           adaptive
% 19.33/2.98  --res_lit_sel_side                      none
% 19.33/2.98  --res_ordering                          kbo
% 19.33/2.98  --res_to_prop_solver                    active
% 19.33/2.98  --res_prop_simpl_new                    false
% 19.33/2.98  --res_prop_simpl_given                  true
% 19.33/2.98  --res_passive_queue_type                priority_queues
% 19.33/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.33/2.98  --res_passive_queues_freq               [15;5]
% 19.33/2.98  --res_forward_subs                      full
% 19.33/2.98  --res_backward_subs                     full
% 19.33/2.98  --res_forward_subs_resolution           true
% 19.33/2.98  --res_backward_subs_resolution          true
% 19.33/2.98  --res_orphan_elimination                true
% 19.33/2.98  --res_time_limit                        2.
% 19.33/2.98  --res_out_proof                         true
% 19.33/2.98  
% 19.33/2.98  ------ Superposition Options
% 19.33/2.98  
% 19.33/2.98  --superposition_flag                    true
% 19.33/2.98  --sup_passive_queue_type                priority_queues
% 19.33/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.33/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.33/2.98  --demod_completeness_check              fast
% 19.33/2.98  --demod_use_ground                      true
% 19.33/2.98  --sup_to_prop_solver                    passive
% 19.33/2.98  --sup_prop_simpl_new                    true
% 19.33/2.98  --sup_prop_simpl_given                  true
% 19.33/2.98  --sup_fun_splitting                     true
% 19.33/2.98  --sup_smt_interval                      50000
% 19.33/2.98  
% 19.33/2.98  ------ Superposition Simplification Setup
% 19.33/2.98  
% 19.33/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.33/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.33/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.33/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.33/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.33/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.33/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.33/2.98  --sup_immed_triv                        [TrivRules]
% 19.33/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.33/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.33/2.98  --sup_immed_bw_main                     []
% 19.33/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.33/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.33/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.33/2.98  --sup_input_bw                          []
% 19.33/2.98  
% 19.33/2.98  ------ Combination Options
% 19.33/2.98  
% 19.33/2.98  --comb_res_mult                         3
% 19.33/2.98  --comb_sup_mult                         2
% 19.33/2.98  --comb_inst_mult                        10
% 19.33/2.98  
% 19.33/2.98  ------ Debug Options
% 19.33/2.98  
% 19.33/2.98  --dbg_backtrace                         false
% 19.33/2.98  --dbg_dump_prop_clauses                 false
% 19.33/2.98  --dbg_dump_prop_clauses_file            -
% 19.33/2.98  --dbg_out_stat                          false
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  ------ Proving...
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  % SZS status Theorem for theBenchmark.p
% 19.33/2.98  
% 19.33/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.33/2.98  
% 19.33/2.98  fof(f1,axiom,(
% 19.33/2.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f18,plain,(
% 19.33/2.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 19.33/2.98    inference(cnf_transformation,[],[f1])).
% 19.33/2.98  
% 19.33/2.98  fof(f5,axiom,(
% 19.33/2.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f22,plain,(
% 19.33/2.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 19.33/2.98    inference(cnf_transformation,[],[f5])).
% 19.33/2.98  
% 19.33/2.98  fof(f6,axiom,(
% 19.33/2.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f23,plain,(
% 19.33/2.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f6])).
% 19.33/2.98  
% 19.33/2.98  fof(f29,plain,(
% 19.33/2.98    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0)))) )),
% 19.33/2.98    inference(definition_unfolding,[],[f18,f22,f22,f23])).
% 19.33/2.98  
% 19.33/2.98  fof(f9,conjecture,(
% 19.33/2.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f10,negated_conjecture,(
% 19.33/2.98    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 19.33/2.98    inference(negated_conjecture,[],[f9])).
% 19.33/2.98  
% 19.33/2.98  fof(f14,plain,(
% 19.33/2.98    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 19.33/2.98    inference(ennf_transformation,[],[f10])).
% 19.33/2.98  
% 19.33/2.98  fof(f16,plain,(
% 19.33/2.98    ( ! [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(X0,sK1))) & v1_relat_1(sK1))) )),
% 19.33/2.98    introduced(choice_axiom,[])).
% 19.33/2.98  
% 19.33/2.98  fof(f15,plain,(
% 19.33/2.98    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 19.33/2.98    introduced(choice_axiom,[])).
% 19.33/2.98  
% 19.33/2.98  fof(f17,plain,(
% 19.33/2.98    (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 19.33/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16,f15])).
% 19.33/2.98  
% 19.33/2.98  fof(f26,plain,(
% 19.33/2.98    v1_relat_1(sK0)),
% 19.33/2.98    inference(cnf_transformation,[],[f17])).
% 19.33/2.98  
% 19.33/2.98  fof(f27,plain,(
% 19.33/2.98    v1_relat_1(sK1)),
% 19.33/2.98    inference(cnf_transformation,[],[f17])).
% 19.33/2.98  
% 19.33/2.98  fof(f8,axiom,(
% 19.33/2.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))))),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f13,plain,(
% 19.33/2.98    ! [X0] : (! [X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.33/2.98    inference(ennf_transformation,[],[f8])).
% 19.33/2.98  
% 19.33/2.98  fof(f25,plain,(
% 19.33/2.98    ( ! [X0,X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f13])).
% 19.33/2.98  
% 19.33/2.98  fof(f33,plain,(
% 19.33/2.98    ( ! [X0,X1] : (k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k2_tarski(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.33/2.98    inference(definition_unfolding,[],[f25,f22,f22])).
% 19.33/2.98  
% 19.33/2.98  fof(f4,axiom,(
% 19.33/2.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f21,plain,(
% 19.33/2.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f4])).
% 19.33/2.98  
% 19.33/2.98  fof(f3,axiom,(
% 19.33/2.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f20,plain,(
% 19.33/2.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 19.33/2.98    inference(cnf_transformation,[],[f3])).
% 19.33/2.98  
% 19.33/2.98  fof(f31,plain,(
% 19.33/2.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 19.33/2.98    inference(definition_unfolding,[],[f20,f22])).
% 19.33/2.98  
% 19.33/2.98  fof(f7,axiom,(
% 19.33/2.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f12,plain,(
% 19.33/2.98    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 19.33/2.98    inference(ennf_transformation,[],[f7])).
% 19.33/2.98  
% 19.33/2.98  fof(f24,plain,(
% 19.33/2.98    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 19.33/2.98    inference(cnf_transformation,[],[f12])).
% 19.33/2.98  
% 19.33/2.98  fof(f32,plain,(
% 19.33/2.98    ( ! [X0,X1] : (v1_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 19.33/2.98    inference(definition_unfolding,[],[f24,f23])).
% 19.33/2.98  
% 19.33/2.98  fof(f2,axiom,(
% 19.33/2.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 19.33/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.33/2.98  
% 19.33/2.98  fof(f11,plain,(
% 19.33/2.98    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 19.33/2.98    inference(ennf_transformation,[],[f2])).
% 19.33/2.98  
% 19.33/2.98  fof(f19,plain,(
% 19.33/2.98    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 19.33/2.98    inference(cnf_transformation,[],[f11])).
% 19.33/2.98  
% 19.33/2.98  fof(f30,plain,(
% 19.33/2.98    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 19.33/2.98    inference(definition_unfolding,[],[f19,f23,f22])).
% 19.33/2.98  
% 19.33/2.98  fof(f28,plain,(
% 19.33/2.98    ~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 19.33/2.98    inference(cnf_transformation,[],[f17])).
% 19.33/2.98  
% 19.33/2.98  cnf(c_103,plain,
% 19.33/2.98      ( ~ r1_tarski(X0_36,X1_36)
% 19.33/2.98      | r1_tarski(X2_36,X3_36)
% 19.33/2.98      | X2_36 != X0_36
% 19.33/2.98      | X3_36 != X1_36 ),
% 19.33/2.98      theory(equality) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_266,plain,
% 19.33/2.98      ( ~ r1_tarski(X0_36,X1_36)
% 19.33/2.98      | r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
% 19.33/2.98      | k2_relat_1(sK0) != X0_36
% 19.33/2.98      | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != X1_36 ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_103]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_294,plain,
% 19.33/2.98      ( ~ r1_tarski(k2_relat_1(X0_36),X1_36)
% 19.33/2.98      | r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
% 19.33/2.98      | k2_relat_1(sK0) != k2_relat_1(X0_36)
% 19.33/2.98      | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != X1_36 ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_266]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_62875,plain,
% 19.33/2.98      ( ~ r1_tarski(k2_relat_1(X0_36),k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))))
% 19.33/2.98      | r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
% 19.33/2.98      | k2_relat_1(sK0) != k2_relat_1(X0_36)
% 19.33/2.98      | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_294]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_62877,plain,
% 19.33/2.98      ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))))
% 19.33/2.98      | r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
% 19.33/2.98      | k2_relat_1(sK0) != k2_relat_1(sK0)
% 19.33/2.98      | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_62875]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_98,plain,
% 19.33/2.98      ( X0_36 != X1_36 | X2_36 != X1_36 | X2_36 = X0_36 ),
% 19.33/2.98      theory(equality) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_431,plain,
% 19.33/2.98      ( X0_36 != X1_36
% 19.33/2.98      | X0_36 = k2_relat_1(X2_36)
% 19.33/2.98      | k2_relat_1(X2_36) != X1_36 ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_98]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_756,plain,
% 19.33/2.98      ( X0_36 != k2_relat_1(X1_36)
% 19.33/2.98      | X0_36 = k2_relat_1(X2_36)
% 19.33/2.98      | k2_relat_1(X2_36) != k2_relat_1(X1_36) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_431]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1013,plain,
% 19.33/2.98      ( k2_relat_1(X0_36) != k2_relat_1(k3_tarski(k2_tarski(X1_36,X2_36)))
% 19.33/2.98      | k3_tarski(k2_tarski(k2_relat_1(X1_36),k2_relat_1(X2_36))) = k2_relat_1(X0_36)
% 19.33/2.98      | k3_tarski(k2_tarski(k2_relat_1(X1_36),k2_relat_1(X2_36))) != k2_relat_1(k3_tarski(k2_tarski(X1_36,X2_36))) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_756]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_26408,plain,
% 19.33/2.98      ( k2_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) != k2_relat_1(k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36))))
% 19.33/2.98      | k3_tarski(k2_tarski(k2_relat_1(X0_36),k2_relat_1(k6_subset_1(X1_36,X0_36)))) = k2_relat_1(k3_tarski(k2_tarski(X0_36,X1_36)))
% 19.33/2.98      | k3_tarski(k2_tarski(k2_relat_1(X0_36),k2_relat_1(k6_subset_1(X1_36,X0_36)))) != k2_relat_1(k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36)))) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_1013]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_62869,plain,
% 19.33/2.98      ( k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) != k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
% 19.33/2.98      | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
% 19.33/2.98      | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) = k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_26408]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_96,plain,( X0_36 = X0_36 ),theory(equality) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4624,plain,
% 19.33/2.98      ( k2_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) = k2_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_96]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_20478,plain,
% 19.33/2.98      ( k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) = k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_4624]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_0,plain,
% 19.33/2.98      ( k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 19.33/2.98      inference(cnf_transformation,[],[f29]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_94,plain,
% 19.33/2.98      ( k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36))) = k3_tarski(k2_tarski(X0_36,X1_36)) ),
% 19.33/2.98      inference(subtyping,[status(esa)],[c_0]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_11842,plain,
% 19.33/2.98      ( k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))) = k3_tarski(k2_tarski(sK1,sK0)) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_94]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1014,plain,
% 19.33/2.98      ( k2_relat_1(X0_36) != k2_relat_1(X0_36)
% 19.33/2.98      | k2_relat_1(X1_36) != k2_relat_1(X0_36)
% 19.33/2.98      | k2_relat_1(X0_36) = k2_relat_1(X1_36) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_756]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1885,plain,
% 19.33/2.98      ( k2_relat_1(X0_36) != k2_relat_1(X0_36)
% 19.33/2.98      | k2_relat_1(X0_36) = k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
% 19.33/2.98      | k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) != k2_relat_1(X0_36) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_1014]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_10454,plain,
% 19.33/2.98      ( k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k2_tarski(sK1,sK0)))
% 19.33/2.98      | k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) = k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
% 19.33/2.98      | k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) != k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_1885]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_105,plain,
% 19.33/2.98      ( X0_36 != X1_36 | k2_relat_1(X0_36) = k2_relat_1(X1_36) ),
% 19.33/2.98      theory(equality) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1353,plain,
% 19.33/2.98      ( k2_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) = k2_relat_1(X2_36)
% 19.33/2.98      | k3_tarski(k2_tarski(X0_36,X1_36)) != X2_36 ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_105]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_3507,plain,
% 19.33/2.98      ( k2_relat_1(k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36)))) = k2_relat_1(k3_tarski(k2_tarski(X0_36,X1_36)))
% 19.33/2.98      | k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36))) != k3_tarski(k2_tarski(X0_36,X1_36)) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_1353]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_10453,plain,
% 19.33/2.98      ( k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) = k2_relat_1(k3_tarski(k2_tarski(sK1,sK0)))
% 19.33/2.98      | k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))) != k3_tarski(k2_tarski(sK1,sK0)) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_3507]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_8,negated_conjecture,
% 19.33/2.98      ( v1_relat_1(sK0) ),
% 19.33/2.98      inference(cnf_transformation,[],[f26]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_86,negated_conjecture,
% 19.33/2.98      ( v1_relat_1(sK0) ),
% 19.33/2.98      inference(subtyping,[status(esa)],[c_8]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_247,plain,
% 19.33/2.98      ( v1_relat_1(sK0) = iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_86]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_7,negated_conjecture,
% 19.33/2.98      ( v1_relat_1(sK1) ),
% 19.33/2.98      inference(cnf_transformation,[],[f27]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_87,negated_conjecture,
% 19.33/2.98      ( v1_relat_1(sK1) ),
% 19.33/2.98      inference(subtyping,[status(esa)],[c_7]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_246,plain,
% 19.33/2.98      ( v1_relat_1(sK1) = iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_87]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_5,plain,
% 19.33/2.98      ( ~ v1_relat_1(X0)
% 19.33/2.98      | ~ v1_relat_1(X1)
% 19.33/2.98      | k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k2_tarski(X0,X1))) ),
% 19.33/2.98      inference(cnf_transformation,[],[f33]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_89,plain,
% 19.33/2.98      ( ~ v1_relat_1(X0_36)
% 19.33/2.98      | ~ v1_relat_1(X1_36)
% 19.33/2.98      | k3_tarski(k2_tarski(k2_relat_1(X0_36),k2_relat_1(X1_36))) = k2_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) ),
% 19.33/2.98      inference(subtyping,[status(esa)],[c_5]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_244,plain,
% 19.33/2.98      ( k3_tarski(k2_tarski(k2_relat_1(X0_36),k2_relat_1(X1_36))) = k2_relat_1(k3_tarski(k2_tarski(X0_36,X1_36)))
% 19.33/2.98      | v1_relat_1(X0_36) != iProver_top
% 19.33/2.98      | v1_relat_1(X1_36) != iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_89]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_996,plain,
% 19.33/2.98      ( k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(X0_36))) = k2_relat_1(k3_tarski(k2_tarski(sK1,X0_36)))
% 19.33/2.98      | v1_relat_1(X0_36) != iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_246,c_244]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1296,plain,
% 19.33/2.98      ( k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(sK0))) = k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_247,c_996]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_3,plain,
% 19.33/2.98      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 19.33/2.98      inference(cnf_transformation,[],[f21]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_91,plain,
% 19.33/2.98      ( k2_tarski(X0_36,X1_36) = k2_tarski(X1_36,X0_36) ),
% 19.33/2.98      inference(subtyping,[status(esa)],[c_3]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_2,plain,
% 19.33/2.98      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 19.33/2.98      inference(cnf_transformation,[],[f31]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_92,plain,
% 19.33/2.98      ( r1_tarski(X0_36,k3_tarski(k2_tarski(X0_36,X1_36))) ),
% 19.33/2.98      inference(subtyping,[status(esa)],[c_2]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_242,plain,
% 19.33/2.98      ( r1_tarski(X0_36,k3_tarski(k2_tarski(X0_36,X1_36))) = iProver_top ),
% 19.33/2.98      inference(predicate_to_equality,[status(thm)],[c_92]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_434,plain,
% 19.33/2.98      ( r1_tarski(X0_36,k3_tarski(k2_tarski(X1_36,X0_36))) = iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_91,c_242]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1387,plain,
% 19.33/2.98      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK1,sK0)))) = iProver_top ),
% 19.33/2.98      inference(superposition,[status(thm)],[c_1296,c_434]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1400,plain,
% 19.33/2.98      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK1,sK0)))) ),
% 19.33/2.98      inference(predicate_to_equality_rev,[status(thm)],[c_1387]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_4,plain,
% 19.33/2.98      ( ~ v1_relat_1(X0) | v1_relat_1(k6_subset_1(X0,X1)) ),
% 19.33/2.98      inference(cnf_transformation,[],[f32]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_90,plain,
% 19.33/2.98      ( ~ v1_relat_1(X0_36) | v1_relat_1(k6_subset_1(X0_36,X1_36)) ),
% 19.33/2.98      inference(subtyping,[status(esa)],[c_4]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_593,plain,
% 19.33/2.98      ( v1_relat_1(k6_subset_1(sK0,sK1)) | ~ v1_relat_1(sK0) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_90]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_440,plain,
% 19.33/2.98      ( ~ v1_relat_1(k6_subset_1(sK0,sK1))
% 19.33/2.98      | ~ v1_relat_1(sK1)
% 19.33/2.98      | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) = k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_89]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_1,plain,
% 19.33/2.98      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
% 19.33/2.98      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 19.33/2.98      inference(cnf_transformation,[],[f30]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_93,plain,
% 19.33/2.98      ( ~ r1_tarski(X0_36,k3_tarski(k2_tarski(X1_36,X2_36)))
% 19.33/2.98      | r1_tarski(k6_subset_1(X0_36,X1_36),X2_36) ),
% 19.33/2.98      inference(subtyping,[status(esa)],[c_1]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_258,plain,
% 19.33/2.98      ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
% 19.33/2.98      | ~ r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))) ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_93]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_113,plain,
% 19.33/2.98      ( sK0 = sK0 ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_96]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_111,plain,
% 19.33/2.98      ( k2_relat_1(sK0) = k2_relat_1(sK0) | sK0 != sK0 ),
% 19.33/2.98      inference(instantiation,[status(thm)],[c_105]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(c_6,negated_conjecture,
% 19.33/2.98      ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
% 19.33/2.98      inference(cnf_transformation,[],[f28]) ).
% 19.33/2.98  
% 19.33/2.98  cnf(contradiction,plain,
% 19.33/2.98      ( $false ),
% 19.33/2.98      inference(minisat,
% 19.33/2.98                [status(thm)],
% 19.33/2.98                [c_62877,c_62869,c_20478,c_11842,c_10454,c_10453,c_1400,
% 19.33/2.98                 c_593,c_440,c_258,c_113,c_111,c_6,c_7,c_8]) ).
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  % SZS output end CNFRefutation for theBenchmark.p
% 19.33/2.98  
% 19.33/2.98  ------                               Statistics
% 19.33/2.98  
% 19.33/2.98  ------ General
% 19.33/2.98  
% 19.33/2.98  abstr_ref_over_cycles:                  0
% 19.33/2.98  abstr_ref_under_cycles:                 0
% 19.33/2.98  gc_basic_clause_elim:                   0
% 19.33/2.98  forced_gc_time:                         0
% 19.33/2.98  parsing_time:                           0.019
% 19.33/2.98  unif_index_cands_time:                  0.
% 19.33/2.98  unif_index_add_time:                    0.
% 19.33/2.98  orderings_time:                         0.
% 19.33/2.98  out_proof_time:                         0.008
% 19.33/2.98  total_time:                             2.103
% 19.33/2.98  num_of_symbols:                         41
% 19.33/2.98  num_of_terms:                           50936
% 19.33/2.98  
% 19.33/2.98  ------ Preprocessing
% 19.33/2.98  
% 19.33/2.98  num_of_splits:                          0
% 19.33/2.98  num_of_split_atoms:                     0
% 19.33/2.98  num_of_reused_defs:                     0
% 19.33/2.98  num_eq_ax_congr_red:                    0
% 19.33/2.98  num_of_sem_filtered_clauses:            1
% 19.33/2.98  num_of_subtypes:                        2
% 19.33/2.98  monotx_restored_types:                  0
% 19.33/2.98  sat_num_of_epr_types:                   0
% 19.33/2.98  sat_num_of_non_cyclic_types:            0
% 19.33/2.98  sat_guarded_non_collapsed_types:        0
% 19.33/2.98  num_pure_diseq_elim:                    0
% 19.33/2.98  simp_replaced_by:                       0
% 19.33/2.98  res_preprocessed:                       48
% 19.33/2.98  prep_upred:                             0
% 19.33/2.98  prep_unflattend:                        0
% 19.33/2.98  smt_new_axioms:                         0
% 19.33/2.98  pred_elim_cands:                        2
% 19.33/2.98  pred_elim:                              0
% 19.33/2.98  pred_elim_cl:                           0
% 19.33/2.98  pred_elim_cycles:                       1
% 19.33/2.98  merged_defs:                            0
% 19.33/2.98  merged_defs_ncl:                        0
% 19.33/2.98  bin_hyper_res:                          0
% 19.33/2.98  prep_cycles:                            3
% 19.33/2.98  pred_elim_time:                         0.
% 19.33/2.98  splitting_time:                         0.
% 19.33/2.98  sem_filter_time:                        0.
% 19.33/2.98  monotx_time:                            0.
% 19.33/2.98  subtype_inf_time:                       0.
% 19.33/2.98  
% 19.33/2.98  ------ Problem properties
% 19.33/2.98  
% 19.33/2.98  clauses:                                9
% 19.33/2.98  conjectures:                            3
% 19.33/2.98  epr:                                    2
% 19.33/2.98  horn:                                   9
% 19.33/2.98  ground:                                 3
% 19.33/2.98  unary:                                  6
% 19.33/2.98  binary:                                 2
% 19.33/2.98  lits:                                   13
% 19.33/2.98  lits_eq:                                3
% 19.33/2.98  fd_pure:                                0
% 19.33/2.98  fd_pseudo:                              0
% 19.33/2.98  fd_cond:                                0
% 19.33/2.98  fd_pseudo_cond:                         0
% 19.33/2.98  ac_symbols:                             0
% 19.33/2.98  
% 19.33/2.98  ------ Propositional Solver
% 19.33/2.98  
% 19.33/2.98  prop_solver_calls:                      34
% 19.33/2.98  prop_fast_solver_calls:                 727
% 19.33/2.98  smt_solver_calls:                       0
% 19.33/2.98  smt_fast_solver_calls:                  0
% 19.33/2.98  prop_num_of_clauses:                    19455
% 19.33/2.98  prop_preprocess_simplified:             29826
% 19.33/2.98  prop_fo_subsumed:                       0
% 19.33/2.98  prop_solver_time:                       0.
% 19.33/2.98  smt_solver_time:                        0.
% 19.33/2.98  smt_fast_solver_time:                   0.
% 19.33/2.98  prop_fast_solver_time:                  0.
% 19.33/2.98  prop_unsat_core_time:                   0.002
% 19.33/2.98  
% 19.33/2.98  ------ QBF
% 19.33/2.98  
% 19.33/2.98  qbf_q_res:                              0
% 19.33/2.98  qbf_num_tautologies:                    0
% 19.33/2.98  qbf_prep_cycles:                        0
% 19.33/2.98  
% 19.33/2.98  ------ BMC1
% 19.33/2.98  
% 19.33/2.98  bmc1_current_bound:                     -1
% 19.33/2.98  bmc1_last_solved_bound:                 -1
% 19.33/2.98  bmc1_unsat_core_size:                   -1
% 19.33/2.98  bmc1_unsat_core_parents_size:           -1
% 19.33/2.98  bmc1_merge_next_fun:                    0
% 19.33/2.98  bmc1_unsat_core_clauses_time:           0.
% 19.33/2.98  
% 19.33/2.98  ------ Instantiation
% 19.33/2.98  
% 19.33/2.98  inst_num_of_clauses:                    5080
% 19.33/2.98  inst_num_in_passive:                    652
% 19.33/2.98  inst_num_in_active:                     2283
% 19.33/2.98  inst_num_in_unprocessed:                2144
% 19.33/2.98  inst_num_of_loops:                      2387
% 19.33/2.98  inst_num_of_learning_restarts:          0
% 19.33/2.98  inst_num_moves_active_passive:          90
% 19.33/2.98  inst_lit_activity:                      0
% 19.33/2.98  inst_lit_activity_moves:                0
% 19.33/2.98  inst_num_tautologies:                   0
% 19.33/2.98  inst_num_prop_implied:                  0
% 19.33/2.98  inst_num_existing_simplified:           0
% 19.33/2.98  inst_num_eq_res_simplified:             0
% 19.33/2.98  inst_num_child_elim:                    0
% 19.33/2.98  inst_num_of_dismatching_blockings:      13166
% 19.33/2.98  inst_num_of_non_proper_insts:           13213
% 19.33/2.98  inst_num_of_duplicates:                 0
% 19.33/2.98  inst_inst_num_from_inst_to_res:         0
% 19.33/2.98  inst_dismatching_checking_time:         0.
% 19.33/2.98  
% 19.33/2.98  ------ Resolution
% 19.33/2.98  
% 19.33/2.98  res_num_of_clauses:                     0
% 19.33/2.98  res_num_in_passive:                     0
% 19.33/2.98  res_num_in_active:                      0
% 19.33/2.98  res_num_of_loops:                       51
% 19.33/2.98  res_forward_subset_subsumed:            2037
% 19.33/2.98  res_backward_subset_subsumed:           14
% 19.33/2.98  res_forward_subsumed:                   0
% 19.33/2.98  res_backward_subsumed:                  0
% 19.33/2.98  res_forward_subsumption_resolution:     0
% 19.33/2.98  res_backward_subsumption_resolution:    0
% 19.33/2.98  res_clause_to_clause_subsumption:       47882
% 19.33/2.98  res_orphan_elimination:                 0
% 19.33/2.98  res_tautology_del:                      1334
% 19.33/2.98  res_num_eq_res_simplified:              0
% 19.33/2.98  res_num_sel_changes:                    0
% 19.33/2.98  res_moves_from_active_to_pass:          0
% 19.33/2.98  
% 19.33/2.98  ------ Superposition
% 19.33/2.98  
% 19.33/2.98  sup_time_total:                         0.
% 19.33/2.98  sup_time_generating:                    0.
% 19.33/2.98  sup_time_sim_full:                      0.
% 19.33/2.98  sup_time_sim_immed:                     0.
% 19.33/2.98  
% 19.33/2.98  sup_num_of_clauses:                     1991
% 19.33/2.98  sup_num_in_active:                      450
% 19.33/2.98  sup_num_in_passive:                     1541
% 19.33/2.98  sup_num_of_loops:                       476
% 19.33/2.98  sup_fw_superposition:                   2093
% 19.33/2.98  sup_bw_superposition:                   1291
% 19.33/2.98  sup_immediate_simplified:               287
% 19.33/2.98  sup_given_eliminated:                   2
% 19.33/2.98  comparisons_done:                       0
% 19.33/2.98  comparisons_avoided:                    0
% 19.33/2.98  
% 19.33/2.98  ------ Simplifications
% 19.33/2.98  
% 19.33/2.98  
% 19.33/2.98  sim_fw_subset_subsumed:                 0
% 19.33/2.98  sim_bw_subset_subsumed:                 0
% 19.33/2.98  sim_fw_subsumed:                        158
% 19.33/2.98  sim_bw_subsumed:                        3
% 19.33/2.98  sim_fw_subsumption_res:                 0
% 19.33/2.98  sim_bw_subsumption_res:                 0
% 19.33/2.98  sim_tautology_del:                      0
% 19.33/2.98  sim_eq_tautology_del:                   2
% 19.33/2.98  sim_eq_res_simp:                        0
% 19.33/2.98  sim_fw_demodulated:                     26
% 19.33/2.98  sim_bw_demodulated:                     124
% 19.33/2.98  sim_light_normalised:                   141
% 19.33/2.98  sim_joinable_taut:                      0
% 19.33/2.98  sim_joinable_simp:                      0
% 19.33/2.98  sim_ac_normalised:                      0
% 19.33/2.98  sim_smt_subsumption:                    0
% 19.33/2.98  
%------------------------------------------------------------------------------
