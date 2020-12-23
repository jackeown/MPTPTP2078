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
% DateTime   : Thu Dec  3 11:42:54 EST 2020

% Result     : Theorem 15.93s
% Output     : CNFRefutation 15.93s
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
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(X0,sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
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
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_tarski(X0,X1)))
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
    ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_103,plain,
    ( ~ r1_tarski(X0_36,X1_36)
    | r1_tarski(X2_36,X3_36)
    | X2_36 != X0_36
    | X3_36 != X1_36 ),
    theory(equality)).

cnf(c_266,plain,
    ( ~ r1_tarski(X0_36,X1_36)
    | r1_tarski(k1_relat_1(sK0),k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))))
    | k1_relat_1(sK0) != X0_36
    | k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) != X1_36 ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_294,plain,
    ( ~ r1_tarski(k1_relat_1(X0_36),X1_36)
    | r1_tarski(k1_relat_1(sK0),k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))))
    | k1_relat_1(sK0) != k1_relat_1(X0_36)
    | k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) != X1_36 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_62875,plain,
    ( ~ r1_tarski(k1_relat_1(X0_36),k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))))
    | r1_tarski(k1_relat_1(sK0),k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))))
    | k1_relat_1(sK0) != k1_relat_1(X0_36)
    | k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) != k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_62877,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))))
    | r1_tarski(k1_relat_1(sK0),k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))))
    | k1_relat_1(sK0) != k1_relat_1(sK0)
    | k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) != k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_62875])).

cnf(c_98,plain,
    ( X0_36 != X1_36
    | X2_36 != X1_36
    | X2_36 = X0_36 ),
    theory(equality)).

cnf(c_431,plain,
    ( X0_36 != X1_36
    | X0_36 = k1_relat_1(X2_36)
    | k1_relat_1(X2_36) != X1_36 ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_756,plain,
    ( X0_36 != k1_relat_1(X1_36)
    | X0_36 = k1_relat_1(X2_36)
    | k1_relat_1(X2_36) != k1_relat_1(X1_36) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_1013,plain,
    ( k1_relat_1(X0_36) != k1_relat_1(k3_tarski(k2_tarski(X1_36,X2_36)))
    | k3_tarski(k2_tarski(k1_relat_1(X1_36),k1_relat_1(X2_36))) = k1_relat_1(X0_36)
    | k3_tarski(k2_tarski(k1_relat_1(X1_36),k1_relat_1(X2_36))) != k1_relat_1(k3_tarski(k2_tarski(X1_36,X2_36))) ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_26408,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) != k1_relat_1(k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36))))
    | k3_tarski(k2_tarski(k1_relat_1(X0_36),k1_relat_1(k6_subset_1(X1_36,X0_36)))) = k1_relat_1(k3_tarski(k2_tarski(X0_36,X1_36)))
    | k3_tarski(k2_tarski(k1_relat_1(X0_36),k1_relat_1(k6_subset_1(X1_36,X0_36)))) != k1_relat_1(k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36)))) ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_62869,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) != k1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
    | k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) != k1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
    | k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) = k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_26408])).

cnf(c_96,plain,
    ( X0_36 = X0_36 ),
    theory(equality)).

cnf(c_4624,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) = k1_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_20478,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) = k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
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
    ( k1_relat_1(X0_36) != k1_relat_1(X0_36)
    | k1_relat_1(X1_36) != k1_relat_1(X0_36)
    | k1_relat_1(X0_36) = k1_relat_1(X1_36) ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_1885,plain,
    ( k1_relat_1(X0_36) != k1_relat_1(X0_36)
    | k1_relat_1(X0_36) = k1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
    | k1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) != k1_relat_1(X0_36) ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_10454,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) != k1_relat_1(k3_tarski(k2_tarski(sK1,sK0)))
    | k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) = k1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
    | k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) != k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_1885])).

cnf(c_105,plain,
    ( X0_36 != X1_36
    | k1_relat_1(X0_36) = k1_relat_1(X1_36) ),
    theory(equality)).

cnf(c_1353,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) = k1_relat_1(X2_36)
    | k3_tarski(k2_tarski(X0_36,X1_36)) != X2_36 ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_3507,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36)))) = k1_relat_1(k3_tarski(k2_tarski(X0_36,X1_36)))
    | k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36))) != k3_tarski(k2_tarski(X0_36,X1_36)) ),
    inference(instantiation,[status(thm)],[c_1353])).

cnf(c_10453,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) = k1_relat_1(k3_tarski(k2_tarski(sK1,sK0)))
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
    | k3_tarski(k2_tarski(k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_89,plain,
    ( ~ v1_relat_1(X0_36)
    | ~ v1_relat_1(X1_36)
    | k3_tarski(k2_tarski(k1_relat_1(X0_36),k1_relat_1(X1_36))) = k1_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_244,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(X0_36),k1_relat_1(X1_36))) = k1_relat_1(k3_tarski(k2_tarski(X0_36,X1_36)))
    | v1_relat_1(X0_36) != iProver_top
    | v1_relat_1(X1_36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_89])).

cnf(c_996,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(X0_36))) = k1_relat_1(k3_tarski(k2_tarski(sK1,X0_36)))
    | v1_relat_1(X0_36) != iProver_top ),
    inference(superposition,[status(thm)],[c_246,c_244])).

cnf(c_1296,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(sK0))) = k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
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
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k3_tarski(k2_tarski(sK1,sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1296,c_434])).

cnf(c_1400,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k3_tarski(k2_tarski(sK1,sK0)))) ),
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
    | k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) = k1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) ),
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
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK0),k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))))) ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_113,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_111,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_62877,c_62869,c_20478,c_11842,c_10454,c_10453,c_1400,c_593,c_440,c_258,c_113,c_111,c_6,c_7,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.93/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.93/2.50  
% 15.93/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.93/2.50  
% 15.93/2.50  ------  iProver source info
% 15.93/2.50  
% 15.93/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.93/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.93/2.50  git: non_committed_changes: false
% 15.93/2.50  git: last_make_outside_of_git: false
% 15.93/2.50  
% 15.93/2.50  ------ 
% 15.93/2.50  
% 15.93/2.50  ------ Input Options
% 15.93/2.50  
% 15.93/2.50  --out_options                           all
% 15.93/2.50  --tptp_safe_out                         true
% 15.93/2.50  --problem_path                          ""
% 15.93/2.50  --include_path                          ""
% 15.93/2.50  --clausifier                            res/vclausify_rel
% 15.93/2.50  --clausifier_options                    ""
% 15.93/2.50  --stdin                                 false
% 15.93/2.50  --stats_out                             all
% 15.93/2.50  
% 15.93/2.50  ------ General Options
% 15.93/2.50  
% 15.93/2.50  --fof                                   false
% 15.93/2.50  --time_out_real                         305.
% 15.93/2.50  --time_out_virtual                      -1.
% 15.93/2.50  --symbol_type_check                     false
% 15.93/2.50  --clausify_out                          false
% 15.93/2.50  --sig_cnt_out                           false
% 15.93/2.50  --trig_cnt_out                          false
% 15.93/2.50  --trig_cnt_out_tolerance                1.
% 15.93/2.50  --trig_cnt_out_sk_spl                   false
% 15.93/2.50  --abstr_cl_out                          false
% 15.93/2.50  
% 15.93/2.50  ------ Global Options
% 15.93/2.50  
% 15.93/2.50  --schedule                              default
% 15.93/2.50  --add_important_lit                     false
% 15.93/2.50  --prop_solver_per_cl                    1000
% 15.93/2.50  --min_unsat_core                        false
% 15.93/2.50  --soft_assumptions                      false
% 15.93/2.50  --soft_lemma_size                       3
% 15.93/2.50  --prop_impl_unit_size                   0
% 15.93/2.50  --prop_impl_unit                        []
% 15.93/2.50  --share_sel_clauses                     true
% 15.93/2.50  --reset_solvers                         false
% 15.93/2.50  --bc_imp_inh                            [conj_cone]
% 15.93/2.50  --conj_cone_tolerance                   3.
% 15.93/2.50  --extra_neg_conj                        none
% 15.93/2.50  --large_theory_mode                     true
% 15.93/2.50  --prolific_symb_bound                   200
% 15.93/2.50  --lt_threshold                          2000
% 15.93/2.50  --clause_weak_htbl                      true
% 15.93/2.50  --gc_record_bc_elim                     false
% 15.93/2.50  
% 15.93/2.50  ------ Preprocessing Options
% 15.93/2.50  
% 15.93/2.50  --preprocessing_flag                    true
% 15.93/2.50  --time_out_prep_mult                    0.1
% 15.93/2.50  --splitting_mode                        input
% 15.93/2.50  --splitting_grd                         true
% 15.93/2.50  --splitting_cvd                         false
% 15.93/2.50  --splitting_cvd_svl                     false
% 15.93/2.50  --splitting_nvd                         32
% 15.93/2.50  --sub_typing                            true
% 15.93/2.50  --prep_gs_sim                           true
% 15.93/2.50  --prep_unflatten                        true
% 15.93/2.50  --prep_res_sim                          true
% 15.93/2.50  --prep_upred                            true
% 15.93/2.50  --prep_sem_filter                       exhaustive
% 15.93/2.50  --prep_sem_filter_out                   false
% 15.93/2.50  --pred_elim                             true
% 15.93/2.50  --res_sim_input                         true
% 15.93/2.50  --eq_ax_congr_red                       true
% 15.93/2.50  --pure_diseq_elim                       true
% 15.93/2.50  --brand_transform                       false
% 15.93/2.50  --non_eq_to_eq                          false
% 15.93/2.50  --prep_def_merge                        true
% 15.93/2.50  --prep_def_merge_prop_impl              false
% 15.93/2.50  --prep_def_merge_mbd                    true
% 15.93/2.50  --prep_def_merge_tr_red                 false
% 15.93/2.50  --prep_def_merge_tr_cl                  false
% 15.93/2.50  --smt_preprocessing                     true
% 15.93/2.50  --smt_ac_axioms                         fast
% 15.93/2.50  --preprocessed_out                      false
% 15.93/2.50  --preprocessed_stats                    false
% 15.93/2.50  
% 15.93/2.50  ------ Abstraction refinement Options
% 15.93/2.50  
% 15.93/2.50  --abstr_ref                             []
% 15.93/2.50  --abstr_ref_prep                        false
% 15.93/2.50  --abstr_ref_until_sat                   false
% 15.93/2.50  --abstr_ref_sig_restrict                funpre
% 15.93/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.93/2.50  --abstr_ref_under                       []
% 15.93/2.50  
% 15.93/2.50  ------ SAT Options
% 15.93/2.50  
% 15.93/2.50  --sat_mode                              false
% 15.93/2.50  --sat_fm_restart_options                ""
% 15.93/2.50  --sat_gr_def                            false
% 15.93/2.50  --sat_epr_types                         true
% 15.93/2.50  --sat_non_cyclic_types                  false
% 15.93/2.50  --sat_finite_models                     false
% 15.93/2.50  --sat_fm_lemmas                         false
% 15.93/2.50  --sat_fm_prep                           false
% 15.93/2.50  --sat_fm_uc_incr                        true
% 15.93/2.50  --sat_out_model                         small
% 15.93/2.50  --sat_out_clauses                       false
% 15.93/2.50  
% 15.93/2.50  ------ QBF Options
% 15.93/2.50  
% 15.93/2.50  --qbf_mode                              false
% 15.93/2.50  --qbf_elim_univ                         false
% 15.93/2.50  --qbf_dom_inst                          none
% 15.93/2.50  --qbf_dom_pre_inst                      false
% 15.93/2.50  --qbf_sk_in                             false
% 15.93/2.50  --qbf_pred_elim                         true
% 15.93/2.50  --qbf_split                             512
% 15.93/2.50  
% 15.93/2.50  ------ BMC1 Options
% 15.93/2.50  
% 15.93/2.50  --bmc1_incremental                      false
% 15.93/2.50  --bmc1_axioms                           reachable_all
% 15.93/2.50  --bmc1_min_bound                        0
% 15.93/2.50  --bmc1_max_bound                        -1
% 15.93/2.50  --bmc1_max_bound_default                -1
% 15.93/2.50  --bmc1_symbol_reachability              true
% 15.93/2.50  --bmc1_property_lemmas                  false
% 15.93/2.50  --bmc1_k_induction                      false
% 15.93/2.50  --bmc1_non_equiv_states                 false
% 15.93/2.50  --bmc1_deadlock                         false
% 15.93/2.50  --bmc1_ucm                              false
% 15.93/2.50  --bmc1_add_unsat_core                   none
% 15.93/2.50  --bmc1_unsat_core_children              false
% 15.93/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.93/2.50  --bmc1_out_stat                         full
% 15.93/2.50  --bmc1_ground_init                      false
% 15.93/2.50  --bmc1_pre_inst_next_state              false
% 15.93/2.50  --bmc1_pre_inst_state                   false
% 15.93/2.50  --bmc1_pre_inst_reach_state             false
% 15.93/2.50  --bmc1_out_unsat_core                   false
% 15.93/2.50  --bmc1_aig_witness_out                  false
% 15.93/2.50  --bmc1_verbose                          false
% 15.93/2.50  --bmc1_dump_clauses_tptp                false
% 15.93/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.93/2.50  --bmc1_dump_file                        -
% 15.93/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.93/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.93/2.50  --bmc1_ucm_extend_mode                  1
% 15.93/2.50  --bmc1_ucm_init_mode                    2
% 15.93/2.50  --bmc1_ucm_cone_mode                    none
% 15.93/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.93/2.50  --bmc1_ucm_relax_model                  4
% 15.93/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.93/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.93/2.50  --bmc1_ucm_layered_model                none
% 15.93/2.50  --bmc1_ucm_max_lemma_size               10
% 15.93/2.50  
% 15.93/2.50  ------ AIG Options
% 15.93/2.50  
% 15.93/2.50  --aig_mode                              false
% 15.93/2.50  
% 15.93/2.50  ------ Instantiation Options
% 15.93/2.50  
% 15.93/2.50  --instantiation_flag                    true
% 15.93/2.50  --inst_sos_flag                         true
% 15.93/2.50  --inst_sos_phase                        true
% 15.93/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.93/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.93/2.50  --inst_lit_sel_side                     num_symb
% 15.93/2.50  --inst_solver_per_active                1400
% 15.93/2.50  --inst_solver_calls_frac                1.
% 15.93/2.50  --inst_passive_queue_type               priority_queues
% 15.93/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.93/2.50  --inst_passive_queues_freq              [25;2]
% 15.93/2.50  --inst_dismatching                      true
% 15.93/2.50  --inst_eager_unprocessed_to_passive     true
% 15.93/2.50  --inst_prop_sim_given                   true
% 15.93/2.50  --inst_prop_sim_new                     false
% 15.93/2.50  --inst_subs_new                         false
% 15.93/2.50  --inst_eq_res_simp                      false
% 15.93/2.50  --inst_subs_given                       false
% 15.93/2.50  --inst_orphan_elimination               true
% 15.93/2.50  --inst_learning_loop_flag               true
% 15.93/2.50  --inst_learning_start                   3000
% 15.93/2.50  --inst_learning_factor                  2
% 15.93/2.50  --inst_start_prop_sim_after_learn       3
% 15.93/2.50  --inst_sel_renew                        solver
% 15.93/2.50  --inst_lit_activity_flag                true
% 15.93/2.50  --inst_restr_to_given                   false
% 15.93/2.50  --inst_activity_threshold               500
% 15.93/2.50  --inst_out_proof                        true
% 15.93/2.50  
% 15.93/2.50  ------ Resolution Options
% 15.93/2.50  
% 15.93/2.50  --resolution_flag                       true
% 15.93/2.50  --res_lit_sel                           adaptive
% 15.93/2.50  --res_lit_sel_side                      none
% 15.93/2.50  --res_ordering                          kbo
% 15.93/2.50  --res_to_prop_solver                    active
% 15.93/2.50  --res_prop_simpl_new                    false
% 15.93/2.50  --res_prop_simpl_given                  true
% 15.93/2.50  --res_passive_queue_type                priority_queues
% 15.93/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.93/2.50  --res_passive_queues_freq               [15;5]
% 15.93/2.50  --res_forward_subs                      full
% 15.93/2.50  --res_backward_subs                     full
% 15.93/2.50  --res_forward_subs_resolution           true
% 15.93/2.50  --res_backward_subs_resolution          true
% 15.93/2.50  --res_orphan_elimination                true
% 15.93/2.50  --res_time_limit                        2.
% 15.93/2.50  --res_out_proof                         true
% 15.93/2.50  
% 15.93/2.50  ------ Superposition Options
% 15.93/2.50  
% 15.93/2.50  --superposition_flag                    true
% 15.93/2.50  --sup_passive_queue_type                priority_queues
% 15.93/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.93/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.93/2.50  --demod_completeness_check              fast
% 15.93/2.50  --demod_use_ground                      true
% 15.93/2.50  --sup_to_prop_solver                    passive
% 15.93/2.50  --sup_prop_simpl_new                    true
% 15.93/2.50  --sup_prop_simpl_given                  true
% 15.93/2.50  --sup_fun_splitting                     true
% 15.93/2.50  --sup_smt_interval                      50000
% 15.93/2.50  
% 15.93/2.50  ------ Superposition Simplification Setup
% 15.93/2.50  
% 15.93/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.93/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.93/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.93/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.93/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.93/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.93/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.93/2.50  --sup_immed_triv                        [TrivRules]
% 15.93/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.93/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.93/2.50  --sup_immed_bw_main                     []
% 15.93/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.93/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.93/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.93/2.50  --sup_input_bw                          []
% 15.93/2.50  
% 15.93/2.50  ------ Combination Options
% 15.93/2.50  
% 15.93/2.50  --comb_res_mult                         3
% 15.93/2.50  --comb_sup_mult                         2
% 15.93/2.50  --comb_inst_mult                        10
% 15.93/2.50  
% 15.93/2.50  ------ Debug Options
% 15.93/2.50  
% 15.93/2.50  --dbg_backtrace                         false
% 15.93/2.50  --dbg_dump_prop_clauses                 false
% 15.93/2.50  --dbg_dump_prop_clauses_file            -
% 15.93/2.50  --dbg_out_stat                          false
% 15.93/2.50  ------ Parsing...
% 15.93/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.93/2.50  
% 15.93/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.93/2.50  
% 15.93/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.93/2.50  
% 15.93/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.93/2.50  ------ Proving...
% 15.93/2.50  ------ Problem Properties 
% 15.93/2.50  
% 15.93/2.50  
% 15.93/2.50  clauses                                 9
% 15.93/2.50  conjectures                             3
% 15.93/2.50  EPR                                     2
% 15.93/2.50  Horn                                    9
% 15.93/2.50  unary                                   6
% 15.93/2.50  binary                                  2
% 15.93/2.50  lits                                    13
% 15.93/2.50  lits eq                                 3
% 15.93/2.50  fd_pure                                 0
% 15.93/2.50  fd_pseudo                               0
% 15.93/2.50  fd_cond                                 0
% 15.93/2.50  fd_pseudo_cond                          0
% 15.93/2.50  AC symbols                              0
% 15.93/2.50  
% 15.93/2.50  ------ Schedule dynamic 5 is on 
% 15.93/2.50  
% 15.93/2.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.93/2.50  
% 15.93/2.50  
% 15.93/2.50  ------ 
% 15.93/2.50  Current options:
% 15.93/2.50  ------ 
% 15.93/2.50  
% 15.93/2.50  ------ Input Options
% 15.93/2.50  
% 15.93/2.50  --out_options                           all
% 15.93/2.50  --tptp_safe_out                         true
% 15.93/2.50  --problem_path                          ""
% 15.93/2.50  --include_path                          ""
% 15.93/2.50  --clausifier                            res/vclausify_rel
% 15.93/2.50  --clausifier_options                    ""
% 15.93/2.50  --stdin                                 false
% 15.93/2.50  --stats_out                             all
% 15.93/2.50  
% 15.93/2.50  ------ General Options
% 15.93/2.50  
% 15.93/2.50  --fof                                   false
% 15.93/2.50  --time_out_real                         305.
% 15.93/2.50  --time_out_virtual                      -1.
% 15.93/2.50  --symbol_type_check                     false
% 15.93/2.50  --clausify_out                          false
% 15.93/2.50  --sig_cnt_out                           false
% 15.93/2.50  --trig_cnt_out                          false
% 15.93/2.50  --trig_cnt_out_tolerance                1.
% 15.93/2.50  --trig_cnt_out_sk_spl                   false
% 15.93/2.50  --abstr_cl_out                          false
% 15.93/2.50  
% 15.93/2.50  ------ Global Options
% 15.93/2.50  
% 15.93/2.50  --schedule                              default
% 15.93/2.50  --add_important_lit                     false
% 15.93/2.50  --prop_solver_per_cl                    1000
% 15.93/2.50  --min_unsat_core                        false
% 15.93/2.50  --soft_assumptions                      false
% 15.93/2.50  --soft_lemma_size                       3
% 15.93/2.50  --prop_impl_unit_size                   0
% 15.93/2.50  --prop_impl_unit                        []
% 15.93/2.50  --share_sel_clauses                     true
% 15.93/2.50  --reset_solvers                         false
% 15.93/2.50  --bc_imp_inh                            [conj_cone]
% 15.93/2.50  --conj_cone_tolerance                   3.
% 15.93/2.50  --extra_neg_conj                        none
% 15.93/2.50  --large_theory_mode                     true
% 15.93/2.50  --prolific_symb_bound                   200
% 15.93/2.50  --lt_threshold                          2000
% 15.93/2.50  --clause_weak_htbl                      true
% 15.93/2.50  --gc_record_bc_elim                     false
% 15.93/2.50  
% 15.93/2.50  ------ Preprocessing Options
% 15.93/2.50  
% 15.93/2.50  --preprocessing_flag                    true
% 15.93/2.50  --time_out_prep_mult                    0.1
% 15.93/2.50  --splitting_mode                        input
% 15.93/2.50  --splitting_grd                         true
% 15.93/2.50  --splitting_cvd                         false
% 15.93/2.50  --splitting_cvd_svl                     false
% 15.93/2.50  --splitting_nvd                         32
% 15.93/2.50  --sub_typing                            true
% 15.93/2.50  --prep_gs_sim                           true
% 15.93/2.50  --prep_unflatten                        true
% 15.93/2.50  --prep_res_sim                          true
% 15.93/2.50  --prep_upred                            true
% 15.93/2.50  --prep_sem_filter                       exhaustive
% 15.93/2.50  --prep_sem_filter_out                   false
% 15.93/2.50  --pred_elim                             true
% 15.93/2.50  --res_sim_input                         true
% 15.93/2.50  --eq_ax_congr_red                       true
% 15.93/2.50  --pure_diseq_elim                       true
% 15.93/2.50  --brand_transform                       false
% 15.93/2.50  --non_eq_to_eq                          false
% 15.93/2.50  --prep_def_merge                        true
% 15.93/2.50  --prep_def_merge_prop_impl              false
% 15.93/2.50  --prep_def_merge_mbd                    true
% 15.93/2.50  --prep_def_merge_tr_red                 false
% 15.93/2.50  --prep_def_merge_tr_cl                  false
% 15.93/2.50  --smt_preprocessing                     true
% 15.93/2.50  --smt_ac_axioms                         fast
% 15.93/2.50  --preprocessed_out                      false
% 15.93/2.50  --preprocessed_stats                    false
% 15.93/2.50  
% 15.93/2.50  ------ Abstraction refinement Options
% 15.93/2.50  
% 15.93/2.50  --abstr_ref                             []
% 15.93/2.50  --abstr_ref_prep                        false
% 15.93/2.50  --abstr_ref_until_sat                   false
% 15.93/2.50  --abstr_ref_sig_restrict                funpre
% 15.93/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.93/2.50  --abstr_ref_under                       []
% 15.93/2.50  
% 15.93/2.50  ------ SAT Options
% 15.93/2.50  
% 15.93/2.50  --sat_mode                              false
% 15.93/2.50  --sat_fm_restart_options                ""
% 15.93/2.50  --sat_gr_def                            false
% 15.93/2.50  --sat_epr_types                         true
% 15.93/2.50  --sat_non_cyclic_types                  false
% 15.93/2.50  --sat_finite_models                     false
% 15.93/2.50  --sat_fm_lemmas                         false
% 15.93/2.50  --sat_fm_prep                           false
% 15.93/2.50  --sat_fm_uc_incr                        true
% 15.93/2.50  --sat_out_model                         small
% 15.93/2.50  --sat_out_clauses                       false
% 15.93/2.50  
% 15.93/2.50  ------ QBF Options
% 15.93/2.50  
% 15.93/2.50  --qbf_mode                              false
% 15.93/2.50  --qbf_elim_univ                         false
% 15.93/2.50  --qbf_dom_inst                          none
% 15.93/2.50  --qbf_dom_pre_inst                      false
% 15.93/2.50  --qbf_sk_in                             false
% 15.93/2.50  --qbf_pred_elim                         true
% 15.93/2.50  --qbf_split                             512
% 15.93/2.50  
% 15.93/2.50  ------ BMC1 Options
% 15.93/2.50  
% 15.93/2.50  --bmc1_incremental                      false
% 15.93/2.50  --bmc1_axioms                           reachable_all
% 15.93/2.50  --bmc1_min_bound                        0
% 15.93/2.50  --bmc1_max_bound                        -1
% 15.93/2.50  --bmc1_max_bound_default                -1
% 15.93/2.50  --bmc1_symbol_reachability              true
% 15.93/2.50  --bmc1_property_lemmas                  false
% 15.93/2.50  --bmc1_k_induction                      false
% 15.93/2.50  --bmc1_non_equiv_states                 false
% 15.93/2.50  --bmc1_deadlock                         false
% 15.93/2.50  --bmc1_ucm                              false
% 15.93/2.50  --bmc1_add_unsat_core                   none
% 15.93/2.50  --bmc1_unsat_core_children              false
% 15.93/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.93/2.50  --bmc1_out_stat                         full
% 15.93/2.50  --bmc1_ground_init                      false
% 15.93/2.50  --bmc1_pre_inst_next_state              false
% 15.93/2.50  --bmc1_pre_inst_state                   false
% 15.93/2.50  --bmc1_pre_inst_reach_state             false
% 15.93/2.50  --bmc1_out_unsat_core                   false
% 15.93/2.50  --bmc1_aig_witness_out                  false
% 15.93/2.50  --bmc1_verbose                          false
% 15.93/2.50  --bmc1_dump_clauses_tptp                false
% 15.93/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.93/2.50  --bmc1_dump_file                        -
% 15.93/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.93/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.93/2.50  --bmc1_ucm_extend_mode                  1
% 15.93/2.50  --bmc1_ucm_init_mode                    2
% 15.93/2.50  --bmc1_ucm_cone_mode                    none
% 15.93/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.93/2.50  --bmc1_ucm_relax_model                  4
% 15.93/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.93/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.93/2.50  --bmc1_ucm_layered_model                none
% 15.93/2.50  --bmc1_ucm_max_lemma_size               10
% 15.93/2.50  
% 15.93/2.50  ------ AIG Options
% 15.93/2.50  
% 15.93/2.50  --aig_mode                              false
% 15.93/2.50  
% 15.93/2.50  ------ Instantiation Options
% 15.93/2.50  
% 15.93/2.50  --instantiation_flag                    true
% 15.93/2.50  --inst_sos_flag                         true
% 15.93/2.50  --inst_sos_phase                        true
% 15.93/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.93/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.93/2.50  --inst_lit_sel_side                     none
% 15.93/2.50  --inst_solver_per_active                1400
% 15.93/2.50  --inst_solver_calls_frac                1.
% 15.93/2.50  --inst_passive_queue_type               priority_queues
% 15.93/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.93/2.50  --inst_passive_queues_freq              [25;2]
% 15.93/2.50  --inst_dismatching                      true
% 15.93/2.50  --inst_eager_unprocessed_to_passive     true
% 15.93/2.50  --inst_prop_sim_given                   true
% 15.93/2.50  --inst_prop_sim_new                     false
% 15.93/2.50  --inst_subs_new                         false
% 15.93/2.50  --inst_eq_res_simp                      false
% 15.93/2.50  --inst_subs_given                       false
% 15.93/2.50  --inst_orphan_elimination               true
% 15.93/2.50  --inst_learning_loop_flag               true
% 15.93/2.50  --inst_learning_start                   3000
% 15.93/2.50  --inst_learning_factor                  2
% 15.93/2.50  --inst_start_prop_sim_after_learn       3
% 15.93/2.50  --inst_sel_renew                        solver
% 15.93/2.50  --inst_lit_activity_flag                true
% 15.93/2.50  --inst_restr_to_given                   false
% 15.93/2.50  --inst_activity_threshold               500
% 15.93/2.50  --inst_out_proof                        true
% 15.93/2.50  
% 15.93/2.50  ------ Resolution Options
% 15.93/2.50  
% 15.93/2.50  --resolution_flag                       false
% 15.93/2.50  --res_lit_sel                           adaptive
% 15.93/2.50  --res_lit_sel_side                      none
% 15.93/2.50  --res_ordering                          kbo
% 15.93/2.50  --res_to_prop_solver                    active
% 15.93/2.50  --res_prop_simpl_new                    false
% 15.93/2.50  --res_prop_simpl_given                  true
% 15.93/2.50  --res_passive_queue_type                priority_queues
% 15.93/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.93/2.50  --res_passive_queues_freq               [15;5]
% 15.93/2.50  --res_forward_subs                      full
% 15.93/2.50  --res_backward_subs                     full
% 15.93/2.50  --res_forward_subs_resolution           true
% 15.93/2.50  --res_backward_subs_resolution          true
% 15.93/2.50  --res_orphan_elimination                true
% 15.93/2.50  --res_time_limit                        2.
% 15.93/2.50  --res_out_proof                         true
% 15.93/2.50  
% 15.93/2.50  ------ Superposition Options
% 15.93/2.50  
% 15.93/2.50  --superposition_flag                    true
% 15.93/2.50  --sup_passive_queue_type                priority_queues
% 15.93/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.93/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.93/2.50  --demod_completeness_check              fast
% 15.93/2.50  --demod_use_ground                      true
% 15.93/2.50  --sup_to_prop_solver                    passive
% 15.93/2.50  --sup_prop_simpl_new                    true
% 15.93/2.50  --sup_prop_simpl_given                  true
% 15.93/2.50  --sup_fun_splitting                     true
% 15.93/2.50  --sup_smt_interval                      50000
% 15.93/2.50  
% 15.93/2.50  ------ Superposition Simplification Setup
% 15.93/2.50  
% 15.93/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.93/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.93/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.93/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.93/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.93/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.93/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.93/2.50  --sup_immed_triv                        [TrivRules]
% 15.93/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.93/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.93/2.50  --sup_immed_bw_main                     []
% 15.93/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.93/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.93/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.93/2.50  --sup_input_bw                          []
% 15.93/2.50  
% 15.93/2.50  ------ Combination Options
% 15.93/2.50  
% 15.93/2.50  --comb_res_mult                         3
% 15.93/2.50  --comb_sup_mult                         2
% 15.93/2.50  --comb_inst_mult                        10
% 15.93/2.50  
% 15.93/2.50  ------ Debug Options
% 15.93/2.50  
% 15.93/2.50  --dbg_backtrace                         false
% 15.93/2.50  --dbg_dump_prop_clauses                 false
% 15.93/2.50  --dbg_dump_prop_clauses_file            -
% 15.93/2.50  --dbg_out_stat                          false
% 15.93/2.50  
% 15.93/2.50  
% 15.93/2.50  
% 15.93/2.50  
% 15.93/2.50  ------ Proving...
% 15.93/2.50  
% 15.93/2.50  
% 15.93/2.50  % SZS status Theorem for theBenchmark.p
% 15.93/2.50  
% 15.93/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.93/2.50  
% 15.93/2.50  fof(f1,axiom,(
% 15.93/2.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 15.93/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.93/2.50  
% 15.93/2.50  fof(f18,plain,(
% 15.93/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 15.93/2.50    inference(cnf_transformation,[],[f1])).
% 15.93/2.50  
% 15.93/2.50  fof(f5,axiom,(
% 15.93/2.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.93/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.93/2.50  
% 15.93/2.50  fof(f22,plain,(
% 15.93/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.93/2.50    inference(cnf_transformation,[],[f5])).
% 15.93/2.50  
% 15.93/2.50  fof(f6,axiom,(
% 15.93/2.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 15.93/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.93/2.50  
% 15.93/2.50  fof(f23,plain,(
% 15.93/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 15.93/2.50    inference(cnf_transformation,[],[f6])).
% 15.93/2.50  
% 15.93/2.50  fof(f29,plain,(
% 15.93/2.50    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0)))) )),
% 15.93/2.50    inference(definition_unfolding,[],[f18,f22,f22,f23])).
% 15.93/2.50  
% 15.93/2.50  fof(f9,conjecture,(
% 15.93/2.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 15.93/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.93/2.50  
% 15.93/2.50  fof(f10,negated_conjecture,(
% 15.93/2.50    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 15.93/2.50    inference(negated_conjecture,[],[f9])).
% 15.93/2.50  
% 15.93/2.50  fof(f14,plain,(
% 15.93/2.50    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 15.93/2.50    inference(ennf_transformation,[],[f10])).
% 15.93/2.50  
% 15.93/2.50  fof(f16,plain,(
% 15.93/2.50    ( ! [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(X0,sK1))) & v1_relat_1(sK1))) )),
% 15.93/2.50    introduced(choice_axiom,[])).
% 15.93/2.50  
% 15.93/2.50  fof(f15,plain,(
% 15.93/2.50    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 15.93/2.50    introduced(choice_axiom,[])).
% 15.93/2.50  
% 15.93/2.50  fof(f17,plain,(
% 15.93/2.50    (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 15.93/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16,f15])).
% 15.93/2.50  
% 15.93/2.50  fof(f26,plain,(
% 15.93/2.50    v1_relat_1(sK0)),
% 15.93/2.50    inference(cnf_transformation,[],[f17])).
% 15.93/2.50  
% 15.93/2.50  fof(f27,plain,(
% 15.93/2.50    v1_relat_1(sK1)),
% 15.93/2.50    inference(cnf_transformation,[],[f17])).
% 15.93/2.50  
% 15.93/2.50  fof(f8,axiom,(
% 15.93/2.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 15.93/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.93/2.50  
% 15.93/2.50  fof(f13,plain,(
% 15.93/2.50    ! [X0] : (! [X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.93/2.50    inference(ennf_transformation,[],[f8])).
% 15.93/2.50  
% 15.93/2.50  fof(f25,plain,(
% 15.93/2.50    ( ! [X0,X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.93/2.50    inference(cnf_transformation,[],[f13])).
% 15.93/2.50  
% 15.93/2.50  fof(f33,plain,(
% 15.93/2.50    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_tarski(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.93/2.50    inference(definition_unfolding,[],[f25,f22,f22])).
% 15.93/2.50  
% 15.93/2.50  fof(f4,axiom,(
% 15.93/2.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 15.93/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.93/2.50  
% 15.93/2.50  fof(f21,plain,(
% 15.93/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 15.93/2.50    inference(cnf_transformation,[],[f4])).
% 15.93/2.50  
% 15.93/2.50  fof(f3,axiom,(
% 15.93/2.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 15.93/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.93/2.50  
% 15.93/2.50  fof(f20,plain,(
% 15.93/2.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 15.93/2.50    inference(cnf_transformation,[],[f3])).
% 15.93/2.50  
% 15.93/2.50  fof(f31,plain,(
% 15.93/2.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 15.93/2.50    inference(definition_unfolding,[],[f20,f22])).
% 15.93/2.50  
% 15.93/2.50  fof(f7,axiom,(
% 15.93/2.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 15.93/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.93/2.50  
% 15.93/2.50  fof(f12,plain,(
% 15.93/2.50    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 15.93/2.50    inference(ennf_transformation,[],[f7])).
% 15.93/2.50  
% 15.93/2.50  fof(f24,plain,(
% 15.93/2.50    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 15.93/2.50    inference(cnf_transformation,[],[f12])).
% 15.93/2.50  
% 15.93/2.50  fof(f32,plain,(
% 15.93/2.50    ( ! [X0,X1] : (v1_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 15.93/2.50    inference(definition_unfolding,[],[f24,f23])).
% 15.93/2.50  
% 15.93/2.50  fof(f2,axiom,(
% 15.93/2.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 15.93/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.93/2.50  
% 15.93/2.50  fof(f11,plain,(
% 15.93/2.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 15.93/2.50    inference(ennf_transformation,[],[f2])).
% 15.93/2.50  
% 15.93/2.50  fof(f19,plain,(
% 15.93/2.50    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 15.93/2.50    inference(cnf_transformation,[],[f11])).
% 15.93/2.50  
% 15.93/2.50  fof(f30,plain,(
% 15.93/2.50    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 15.93/2.50    inference(definition_unfolding,[],[f19,f23,f22])).
% 15.93/2.50  
% 15.93/2.50  fof(f28,plain,(
% 15.93/2.50    ~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 15.93/2.50    inference(cnf_transformation,[],[f17])).
% 15.93/2.50  
% 15.93/2.50  cnf(c_103,plain,
% 15.93/2.50      ( ~ r1_tarski(X0_36,X1_36)
% 15.93/2.50      | r1_tarski(X2_36,X3_36)
% 15.93/2.50      | X2_36 != X0_36
% 15.93/2.50      | X3_36 != X1_36 ),
% 15.93/2.50      theory(equality) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_266,plain,
% 15.93/2.50      ( ~ r1_tarski(X0_36,X1_36)
% 15.93/2.50      | r1_tarski(k1_relat_1(sK0),k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))))
% 15.93/2.50      | k1_relat_1(sK0) != X0_36
% 15.93/2.50      | k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) != X1_36 ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_103]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_294,plain,
% 15.93/2.50      ( ~ r1_tarski(k1_relat_1(X0_36),X1_36)
% 15.93/2.50      | r1_tarski(k1_relat_1(sK0),k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))))
% 15.93/2.50      | k1_relat_1(sK0) != k1_relat_1(X0_36)
% 15.93/2.50      | k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) != X1_36 ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_266]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_62875,plain,
% 15.93/2.50      ( ~ r1_tarski(k1_relat_1(X0_36),k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))))
% 15.93/2.50      | r1_tarski(k1_relat_1(sK0),k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))))
% 15.93/2.50      | k1_relat_1(sK0) != k1_relat_1(X0_36)
% 15.93/2.50      | k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) != k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_294]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_62877,plain,
% 15.93/2.50      ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))))
% 15.93/2.50      | r1_tarski(k1_relat_1(sK0),k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))))
% 15.93/2.50      | k1_relat_1(sK0) != k1_relat_1(sK0)
% 15.93/2.50      | k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) != k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_62875]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_98,plain,
% 15.93/2.50      ( X0_36 != X1_36 | X2_36 != X1_36 | X2_36 = X0_36 ),
% 15.93/2.50      theory(equality) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_431,plain,
% 15.93/2.50      ( X0_36 != X1_36
% 15.93/2.50      | X0_36 = k1_relat_1(X2_36)
% 15.93/2.50      | k1_relat_1(X2_36) != X1_36 ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_98]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_756,plain,
% 15.93/2.50      ( X0_36 != k1_relat_1(X1_36)
% 15.93/2.50      | X0_36 = k1_relat_1(X2_36)
% 15.93/2.50      | k1_relat_1(X2_36) != k1_relat_1(X1_36) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_431]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_1013,plain,
% 15.93/2.50      ( k1_relat_1(X0_36) != k1_relat_1(k3_tarski(k2_tarski(X1_36,X2_36)))
% 15.93/2.50      | k3_tarski(k2_tarski(k1_relat_1(X1_36),k1_relat_1(X2_36))) = k1_relat_1(X0_36)
% 15.93/2.50      | k3_tarski(k2_tarski(k1_relat_1(X1_36),k1_relat_1(X2_36))) != k1_relat_1(k3_tarski(k2_tarski(X1_36,X2_36))) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_756]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_26408,plain,
% 15.93/2.50      ( k1_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) != k1_relat_1(k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36))))
% 15.93/2.50      | k3_tarski(k2_tarski(k1_relat_1(X0_36),k1_relat_1(k6_subset_1(X1_36,X0_36)))) = k1_relat_1(k3_tarski(k2_tarski(X0_36,X1_36)))
% 15.93/2.50      | k3_tarski(k2_tarski(k1_relat_1(X0_36),k1_relat_1(k6_subset_1(X1_36,X0_36)))) != k1_relat_1(k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36)))) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_1013]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_62869,plain,
% 15.93/2.50      ( k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) != k1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
% 15.93/2.50      | k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) != k1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
% 15.93/2.50      | k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) = k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_26408]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_96,plain,( X0_36 = X0_36 ),theory(equality) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_4624,plain,
% 15.93/2.50      ( k1_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) = k1_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_96]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_20478,plain,
% 15.93/2.50      ( k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) = k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_4624]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_0,plain,
% 15.93/2.50      ( k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 15.93/2.50      inference(cnf_transformation,[],[f29]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_94,plain,
% 15.93/2.50      ( k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36))) = k3_tarski(k2_tarski(X0_36,X1_36)) ),
% 15.93/2.50      inference(subtyping,[status(esa)],[c_0]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_11842,plain,
% 15.93/2.50      ( k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))) = k3_tarski(k2_tarski(sK1,sK0)) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_94]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_1014,plain,
% 15.93/2.50      ( k1_relat_1(X0_36) != k1_relat_1(X0_36)
% 15.93/2.50      | k1_relat_1(X1_36) != k1_relat_1(X0_36)
% 15.93/2.50      | k1_relat_1(X0_36) = k1_relat_1(X1_36) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_756]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_1885,plain,
% 15.93/2.50      ( k1_relat_1(X0_36) != k1_relat_1(X0_36)
% 15.93/2.50      | k1_relat_1(X0_36) = k1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
% 15.93/2.50      | k1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) != k1_relat_1(X0_36) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_1014]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_10454,plain,
% 15.93/2.50      ( k1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) != k1_relat_1(k3_tarski(k2_tarski(sK1,sK0)))
% 15.93/2.50      | k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) = k1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
% 15.93/2.50      | k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) != k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_1885]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_105,plain,
% 15.93/2.50      ( X0_36 != X1_36 | k1_relat_1(X0_36) = k1_relat_1(X1_36) ),
% 15.93/2.50      theory(equality) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_1353,plain,
% 15.93/2.50      ( k1_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) = k1_relat_1(X2_36)
% 15.93/2.50      | k3_tarski(k2_tarski(X0_36,X1_36)) != X2_36 ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_105]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_3507,plain,
% 15.93/2.50      ( k1_relat_1(k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36)))) = k1_relat_1(k3_tarski(k2_tarski(X0_36,X1_36)))
% 15.93/2.50      | k3_tarski(k2_tarski(X0_36,k6_subset_1(X1_36,X0_36))) != k3_tarski(k2_tarski(X0_36,X1_36)) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_1353]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_10453,plain,
% 15.93/2.50      ( k1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) = k1_relat_1(k3_tarski(k2_tarski(sK1,sK0)))
% 15.93/2.50      | k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))) != k3_tarski(k2_tarski(sK1,sK0)) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_3507]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_8,negated_conjecture,
% 15.93/2.50      ( v1_relat_1(sK0) ),
% 15.93/2.50      inference(cnf_transformation,[],[f26]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_86,negated_conjecture,
% 15.93/2.50      ( v1_relat_1(sK0) ),
% 15.93/2.50      inference(subtyping,[status(esa)],[c_8]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_247,plain,
% 15.93/2.50      ( v1_relat_1(sK0) = iProver_top ),
% 15.93/2.50      inference(predicate_to_equality,[status(thm)],[c_86]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_7,negated_conjecture,
% 15.93/2.50      ( v1_relat_1(sK1) ),
% 15.93/2.50      inference(cnf_transformation,[],[f27]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_87,negated_conjecture,
% 15.93/2.50      ( v1_relat_1(sK1) ),
% 15.93/2.50      inference(subtyping,[status(esa)],[c_7]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_246,plain,
% 15.93/2.50      ( v1_relat_1(sK1) = iProver_top ),
% 15.93/2.50      inference(predicate_to_equality,[status(thm)],[c_87]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_5,plain,
% 15.93/2.50      ( ~ v1_relat_1(X0)
% 15.93/2.50      | ~ v1_relat_1(X1)
% 15.93/2.50      | k3_tarski(k2_tarski(k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_tarski(X0,X1))) ),
% 15.93/2.50      inference(cnf_transformation,[],[f33]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_89,plain,
% 15.93/2.50      ( ~ v1_relat_1(X0_36)
% 15.93/2.50      | ~ v1_relat_1(X1_36)
% 15.93/2.50      | k3_tarski(k2_tarski(k1_relat_1(X0_36),k1_relat_1(X1_36))) = k1_relat_1(k3_tarski(k2_tarski(X0_36,X1_36))) ),
% 15.93/2.50      inference(subtyping,[status(esa)],[c_5]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_244,plain,
% 15.93/2.50      ( k3_tarski(k2_tarski(k1_relat_1(X0_36),k1_relat_1(X1_36))) = k1_relat_1(k3_tarski(k2_tarski(X0_36,X1_36)))
% 15.93/2.50      | v1_relat_1(X0_36) != iProver_top
% 15.93/2.50      | v1_relat_1(X1_36) != iProver_top ),
% 15.93/2.50      inference(predicate_to_equality,[status(thm)],[c_89]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_996,plain,
% 15.93/2.50      ( k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(X0_36))) = k1_relat_1(k3_tarski(k2_tarski(sK1,X0_36)))
% 15.93/2.50      | v1_relat_1(X0_36) != iProver_top ),
% 15.93/2.50      inference(superposition,[status(thm)],[c_246,c_244]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_1296,plain,
% 15.93/2.50      ( k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(sK0))) = k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
% 15.93/2.50      inference(superposition,[status(thm)],[c_247,c_996]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_3,plain,
% 15.93/2.50      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 15.93/2.50      inference(cnf_transformation,[],[f21]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_91,plain,
% 15.93/2.50      ( k2_tarski(X0_36,X1_36) = k2_tarski(X1_36,X0_36) ),
% 15.93/2.50      inference(subtyping,[status(esa)],[c_3]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_2,plain,
% 15.93/2.50      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 15.93/2.50      inference(cnf_transformation,[],[f31]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_92,plain,
% 15.93/2.50      ( r1_tarski(X0_36,k3_tarski(k2_tarski(X0_36,X1_36))) ),
% 15.93/2.50      inference(subtyping,[status(esa)],[c_2]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_242,plain,
% 15.93/2.50      ( r1_tarski(X0_36,k3_tarski(k2_tarski(X0_36,X1_36))) = iProver_top ),
% 15.93/2.50      inference(predicate_to_equality,[status(thm)],[c_92]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_434,plain,
% 15.93/2.50      ( r1_tarski(X0_36,k3_tarski(k2_tarski(X1_36,X0_36))) = iProver_top ),
% 15.93/2.50      inference(superposition,[status(thm)],[c_91,c_242]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_1387,plain,
% 15.93/2.50      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k3_tarski(k2_tarski(sK1,sK0)))) = iProver_top ),
% 15.93/2.50      inference(superposition,[status(thm)],[c_1296,c_434]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_1400,plain,
% 15.93/2.50      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k3_tarski(k2_tarski(sK1,sK0)))) ),
% 15.93/2.50      inference(predicate_to_equality_rev,[status(thm)],[c_1387]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_4,plain,
% 15.93/2.50      ( ~ v1_relat_1(X0) | v1_relat_1(k6_subset_1(X0,X1)) ),
% 15.93/2.50      inference(cnf_transformation,[],[f32]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_90,plain,
% 15.93/2.50      ( ~ v1_relat_1(X0_36) | v1_relat_1(k6_subset_1(X0_36,X1_36)) ),
% 15.93/2.50      inference(subtyping,[status(esa)],[c_4]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_593,plain,
% 15.93/2.50      ( v1_relat_1(k6_subset_1(sK0,sK1)) | ~ v1_relat_1(sK0) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_90]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_440,plain,
% 15.93/2.50      ( ~ v1_relat_1(k6_subset_1(sK0,sK1))
% 15.93/2.50      | ~ v1_relat_1(sK1)
% 15.93/2.50      | k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) = k1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_89]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_1,plain,
% 15.93/2.50      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
% 15.93/2.50      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 15.93/2.50      inference(cnf_transformation,[],[f30]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_93,plain,
% 15.93/2.50      ( ~ r1_tarski(X0_36,k3_tarski(k2_tarski(X1_36,X2_36)))
% 15.93/2.50      | r1_tarski(k6_subset_1(X0_36,X1_36),X2_36) ),
% 15.93/2.50      inference(subtyping,[status(esa)],[c_1]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_258,plain,
% 15.93/2.50      ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
% 15.93/2.50      | ~ r1_tarski(k1_relat_1(sK0),k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))))) ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_93]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_113,plain,
% 15.93/2.50      ( sK0 = sK0 ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_96]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_111,plain,
% 15.93/2.50      ( k1_relat_1(sK0) = k1_relat_1(sK0) | sK0 != sK0 ),
% 15.93/2.50      inference(instantiation,[status(thm)],[c_105]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(c_6,negated_conjecture,
% 15.93/2.50      ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
% 15.93/2.50      inference(cnf_transformation,[],[f28]) ).
% 15.93/2.50  
% 15.93/2.50  cnf(contradiction,plain,
% 15.93/2.50      ( $false ),
% 15.93/2.50      inference(minisat,
% 15.93/2.50                [status(thm)],
% 15.93/2.50                [c_62877,c_62869,c_20478,c_11842,c_10454,c_10453,c_1400,
% 15.93/2.50                 c_593,c_440,c_258,c_113,c_111,c_6,c_7,c_8]) ).
% 15.93/2.50  
% 15.93/2.50  
% 15.93/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.93/2.50  
% 15.93/2.50  ------                               Statistics
% 15.93/2.50  
% 15.93/2.50  ------ General
% 15.93/2.50  
% 15.93/2.50  abstr_ref_over_cycles:                  0
% 15.93/2.50  abstr_ref_under_cycles:                 0
% 15.93/2.50  gc_basic_clause_elim:                   0
% 15.93/2.50  forced_gc_time:                         0
% 15.93/2.50  parsing_time:                           0.007
% 15.93/2.50  unif_index_cands_time:                  0.
% 15.93/2.50  unif_index_add_time:                    0.
% 15.93/2.50  orderings_time:                         0.
% 15.93/2.50  out_proof_time:                         0.01
% 15.93/2.50  total_time:                             1.976
% 15.93/2.50  num_of_symbols:                         41
% 15.93/2.50  num_of_terms:                           50936
% 15.93/2.50  
% 15.93/2.50  ------ Preprocessing
% 15.93/2.50  
% 15.93/2.50  num_of_splits:                          0
% 15.93/2.50  num_of_split_atoms:                     0
% 15.93/2.50  num_of_reused_defs:                     0
% 15.93/2.50  num_eq_ax_congr_red:                    0
% 15.93/2.50  num_of_sem_filtered_clauses:            1
% 15.93/2.50  num_of_subtypes:                        2
% 15.93/2.50  monotx_restored_types:                  0
% 15.93/2.50  sat_num_of_epr_types:                   0
% 15.93/2.50  sat_num_of_non_cyclic_types:            0
% 15.93/2.50  sat_guarded_non_collapsed_types:        0
% 15.93/2.50  num_pure_diseq_elim:                    0
% 15.93/2.50  simp_replaced_by:                       0
% 15.93/2.50  res_preprocessed:                       48
% 15.93/2.50  prep_upred:                             0
% 15.93/2.50  prep_unflattend:                        0
% 15.93/2.50  smt_new_axioms:                         0
% 15.93/2.50  pred_elim_cands:                        2
% 15.93/2.50  pred_elim:                              0
% 15.93/2.50  pred_elim_cl:                           0
% 15.93/2.50  pred_elim_cycles:                       1
% 15.93/2.50  merged_defs:                            0
% 15.93/2.50  merged_defs_ncl:                        0
% 15.93/2.50  bin_hyper_res:                          0
% 15.93/2.50  prep_cycles:                            3
% 15.93/2.50  pred_elim_time:                         0.
% 15.93/2.50  splitting_time:                         0.
% 15.93/2.50  sem_filter_time:                        0.
% 15.93/2.50  monotx_time:                            0.
% 15.93/2.50  subtype_inf_time:                       0.
% 15.93/2.50  
% 15.93/2.50  ------ Problem properties
% 15.93/2.50  
% 15.93/2.50  clauses:                                9
% 15.93/2.50  conjectures:                            3
% 15.93/2.50  epr:                                    2
% 15.93/2.50  horn:                                   9
% 15.93/2.50  ground:                                 3
% 15.93/2.50  unary:                                  6
% 15.93/2.50  binary:                                 2
% 15.93/2.50  lits:                                   13
% 15.93/2.50  lits_eq:                                3
% 15.93/2.50  fd_pure:                                0
% 15.93/2.50  fd_pseudo:                              0
% 15.93/2.50  fd_cond:                                0
% 15.93/2.50  fd_pseudo_cond:                         0
% 15.93/2.50  ac_symbols:                             0
% 15.93/2.50  
% 15.93/2.50  ------ Propositional Solver
% 15.93/2.50  
% 15.93/2.50  prop_solver_calls:                      34
% 15.93/2.50  prop_fast_solver_calls:                 727
% 15.93/2.50  smt_solver_calls:                       0
% 15.93/2.50  smt_fast_solver_calls:                  0
% 15.93/2.50  prop_num_of_clauses:                    19455
% 15.93/2.50  prop_preprocess_simplified:             29826
% 15.93/2.50  prop_fo_subsumed:                       0
% 15.93/2.50  prop_solver_time:                       0.
% 15.93/2.50  smt_solver_time:                        0.
% 15.93/2.50  smt_fast_solver_time:                   0.
% 15.93/2.50  prop_fast_solver_time:                  0.
% 15.93/2.50  prop_unsat_core_time:                   0.002
% 15.93/2.50  
% 15.93/2.50  ------ QBF
% 15.93/2.50  
% 15.93/2.50  qbf_q_res:                              0
% 15.93/2.50  qbf_num_tautologies:                    0
% 15.93/2.50  qbf_prep_cycles:                        0
% 15.93/2.50  
% 15.93/2.50  ------ BMC1
% 15.93/2.50  
% 15.93/2.50  bmc1_current_bound:                     -1
% 15.93/2.50  bmc1_last_solved_bound:                 -1
% 15.93/2.50  bmc1_unsat_core_size:                   -1
% 15.93/2.50  bmc1_unsat_core_parents_size:           -1
% 15.93/2.50  bmc1_merge_next_fun:                    0
% 15.93/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.93/2.50  
% 15.93/2.50  ------ Instantiation
% 15.93/2.50  
% 15.93/2.50  inst_num_of_clauses:                    5080
% 15.93/2.50  inst_num_in_passive:                    652
% 15.93/2.50  inst_num_in_active:                     2283
% 15.93/2.50  inst_num_in_unprocessed:                2144
% 15.93/2.50  inst_num_of_loops:                      2387
% 15.93/2.50  inst_num_of_learning_restarts:          0
% 15.93/2.50  inst_num_moves_active_passive:          90
% 15.93/2.50  inst_lit_activity:                      0
% 15.93/2.50  inst_lit_activity_moves:                0
% 15.93/2.50  inst_num_tautologies:                   0
% 15.93/2.50  inst_num_prop_implied:                  0
% 15.93/2.50  inst_num_existing_simplified:           0
% 15.93/2.50  inst_num_eq_res_simplified:             0
% 15.93/2.50  inst_num_child_elim:                    0
% 15.93/2.50  inst_num_of_dismatching_blockings:      13166
% 15.93/2.50  inst_num_of_non_proper_insts:           13213
% 15.93/2.50  inst_num_of_duplicates:                 0
% 15.93/2.50  inst_inst_num_from_inst_to_res:         0
% 15.93/2.50  inst_dismatching_checking_time:         0.
% 15.93/2.50  
% 15.93/2.50  ------ Resolution
% 15.93/2.50  
% 15.93/2.50  res_num_of_clauses:                     0
% 15.93/2.50  res_num_in_passive:                     0
% 15.93/2.50  res_num_in_active:                      0
% 15.93/2.50  res_num_of_loops:                       51
% 15.93/2.50  res_forward_subset_subsumed:            2037
% 15.93/2.50  res_backward_subset_subsumed:           14
% 15.93/2.50  res_forward_subsumed:                   0
% 15.93/2.50  res_backward_subsumed:                  0
% 15.93/2.50  res_forward_subsumption_resolution:     0
% 15.93/2.50  res_backward_subsumption_resolution:    0
% 15.93/2.50  res_clause_to_clause_subsumption:       47882
% 15.93/2.50  res_orphan_elimination:                 0
% 15.93/2.50  res_tautology_del:                      1334
% 15.93/2.50  res_num_eq_res_simplified:              0
% 15.93/2.50  res_num_sel_changes:                    0
% 15.93/2.50  res_moves_from_active_to_pass:          0
% 15.93/2.50  
% 15.93/2.50  ------ Superposition
% 15.93/2.50  
% 15.93/2.50  sup_time_total:                         0.
% 15.93/2.50  sup_time_generating:                    0.
% 15.93/2.50  sup_time_sim_full:                      0.
% 15.93/2.50  sup_time_sim_immed:                     0.
% 15.93/2.50  
% 15.93/2.50  sup_num_of_clauses:                     1991
% 15.93/2.50  sup_num_in_active:                      450
% 15.93/2.50  sup_num_in_passive:                     1541
% 15.93/2.50  sup_num_of_loops:                       476
% 15.93/2.50  sup_fw_superposition:                   2093
% 15.93/2.50  sup_bw_superposition:                   1291
% 15.93/2.50  sup_immediate_simplified:               287
% 15.93/2.50  sup_given_eliminated:                   2
% 15.93/2.50  comparisons_done:                       0
% 15.93/2.50  comparisons_avoided:                    0
% 15.93/2.50  
% 15.93/2.50  ------ Simplifications
% 15.93/2.50  
% 15.93/2.50  
% 15.93/2.50  sim_fw_subset_subsumed:                 0
% 15.93/2.50  sim_bw_subset_subsumed:                 0
% 15.93/2.50  sim_fw_subsumed:                        158
% 15.93/2.50  sim_bw_subsumed:                        3
% 15.93/2.50  sim_fw_subsumption_res:                 0
% 15.93/2.50  sim_bw_subsumption_res:                 0
% 15.93/2.50  sim_tautology_del:                      0
% 15.93/2.50  sim_eq_tautology_del:                   2
% 15.93/2.50  sim_eq_res_simp:                        0
% 15.93/2.50  sim_fw_demodulated:                     26
% 15.93/2.50  sim_bw_demodulated:                     124
% 15.93/2.50  sim_light_normalised:                   141
% 15.93/2.50  sim_joinable_taut:                      0
% 15.93/2.50  sim_joinable_simp:                      0
% 15.93/2.50  sim_ac_normalised:                      0
% 15.93/2.50  sim_smt_subsumption:                    0
% 15.93/2.50  
%------------------------------------------------------------------------------
