%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:01 EST 2020

% Result     : Theorem 1.11s
% Output     : CNFRefutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 342 expanded)
%              Number of clauses        :   62 ( 159 expanded)
%              Number of leaves         :   15 (  63 expanded)
%              Depth                    :   17
%              Number of atoms          :  257 ( 818 expanded)
%              Number of equality atoms :  144 ( 412 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f24,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f29])).

fof(f48,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f47,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_474,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_469,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_471,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1209,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_471])).

cnf(c_9,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_35,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_37,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_51,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1369,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1209,c_37,c_51])).

cnf(c_1370,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1369])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_476,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_478,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1108,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_476,c_478])).

cnf(c_1376,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1370,c_1108])).

cnf(c_2034,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_469,c_1376])).

cnf(c_12,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_472,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1109,plain,
    ( k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)) = X0
    | r1_tarski(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)),X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_472,c_478])).

cnf(c_2155,plain,
    ( k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k5_relat_1(k1_xboole_0,sK0)
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0)) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2034,c_1109])).

cnf(c_2184,plain,
    ( k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k5_relat_1(k1_xboole_0,sK0)
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0)) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2155,c_2034])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2185,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0)) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2184,c_7])).

cnf(c_15,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_14,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_470,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_755,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_470])).

cnf(c_1353,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_755,c_37,c_51])).

cnf(c_1354,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1353])).

cnf(c_1360,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1354,c_1108])).

cnf(c_1574,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_469,c_1360])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_473,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1591,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1574,c_473])).

cnf(c_19,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_591,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_592,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_631,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_632,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_240,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_730,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != X0 ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_731,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_733,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != k1_xboole_0
    | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_1716,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1591,c_19,c_37,c_51,c_592,c_632,c_733,c_1574])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_479,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1722,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1716,c_479])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1795,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1722,c_17])).

cnf(c_1796,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1795])).

cnf(c_2157,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2034,c_472])).

cnf(c_2172,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2157,c_7])).

cnf(c_2247,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2172,c_1108])).

cnf(c_2254,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2185,c_1796,c_2247])).

cnf(c_2259,plain,
    ( v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_474,c_2254])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2259,c_51,c_37,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : iproveropt_run.sh %d %s
% 0.06/0.25  % Computer   : n007.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 20:17:36 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.26  % Running in FOF mode
% 1.11/0.83  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.11/0.83  
% 1.11/0.83  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.11/0.83  
% 1.11/0.83  ------  iProver source info
% 1.11/0.83  
% 1.11/0.83  git: date: 2020-06-30 10:37:57 +0100
% 1.11/0.83  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.11/0.83  git: non_committed_changes: false
% 1.11/0.83  git: last_make_outside_of_git: false
% 1.11/0.83  
% 1.11/0.83  ------ 
% 1.11/0.83  
% 1.11/0.83  ------ Input Options
% 1.11/0.83  
% 1.11/0.83  --out_options                           all
% 1.11/0.83  --tptp_safe_out                         true
% 1.11/0.83  --problem_path                          ""
% 1.11/0.83  --include_path                          ""
% 1.11/0.83  --clausifier                            res/vclausify_rel
% 1.11/0.83  --clausifier_options                    --mode clausify
% 1.11/0.83  --stdin                                 false
% 1.11/0.83  --stats_out                             all
% 1.11/0.83  
% 1.11/0.83  ------ General Options
% 1.11/0.83  
% 1.11/0.83  --fof                                   false
% 1.11/0.83  --time_out_real                         305.
% 1.11/0.83  --time_out_virtual                      -1.
% 1.11/0.83  --symbol_type_check                     false
% 1.11/0.83  --clausify_out                          false
% 1.11/0.83  --sig_cnt_out                           false
% 1.11/0.83  --trig_cnt_out                          false
% 1.11/0.83  --trig_cnt_out_tolerance                1.
% 1.11/0.83  --trig_cnt_out_sk_spl                   false
% 1.11/0.83  --abstr_cl_out                          false
% 1.11/0.83  
% 1.11/0.83  ------ Global Options
% 1.11/0.83  
% 1.11/0.83  --schedule                              default
% 1.11/0.83  --add_important_lit                     false
% 1.11/0.83  --prop_solver_per_cl                    1000
% 1.11/0.83  --min_unsat_core                        false
% 1.11/0.83  --soft_assumptions                      false
% 1.11/0.83  --soft_lemma_size                       3
% 1.11/0.83  --prop_impl_unit_size                   0
% 1.11/0.83  --prop_impl_unit                        []
% 1.11/0.83  --share_sel_clauses                     true
% 1.11/0.83  --reset_solvers                         false
% 1.11/0.83  --bc_imp_inh                            [conj_cone]
% 1.11/0.83  --conj_cone_tolerance                   3.
% 1.11/0.83  --extra_neg_conj                        none
% 1.11/0.83  --large_theory_mode                     true
% 1.11/0.83  --prolific_symb_bound                   200
% 1.11/0.83  --lt_threshold                          2000
% 1.11/0.83  --clause_weak_htbl                      true
% 1.11/0.83  --gc_record_bc_elim                     false
% 1.11/0.83  
% 1.11/0.83  ------ Preprocessing Options
% 1.11/0.83  
% 1.11/0.83  --preprocessing_flag                    true
% 1.11/0.83  --time_out_prep_mult                    0.1
% 1.11/0.83  --splitting_mode                        input
% 1.11/0.83  --splitting_grd                         true
% 1.11/0.83  --splitting_cvd                         false
% 1.11/0.83  --splitting_cvd_svl                     false
% 1.11/0.83  --splitting_nvd                         32
% 1.11/0.83  --sub_typing                            true
% 1.11/0.83  --prep_gs_sim                           true
% 1.11/0.83  --prep_unflatten                        true
% 1.11/0.83  --prep_res_sim                          true
% 1.11/0.83  --prep_upred                            true
% 1.11/0.83  --prep_sem_filter                       exhaustive
% 1.11/0.83  --prep_sem_filter_out                   false
% 1.11/0.83  --pred_elim                             true
% 1.11/0.83  --res_sim_input                         true
% 1.11/0.83  --eq_ax_congr_red                       true
% 1.11/0.83  --pure_diseq_elim                       true
% 1.11/0.83  --brand_transform                       false
% 1.11/0.83  --non_eq_to_eq                          false
% 1.11/0.83  --prep_def_merge                        true
% 1.11/0.83  --prep_def_merge_prop_impl              false
% 1.11/0.83  --prep_def_merge_mbd                    true
% 1.11/0.83  --prep_def_merge_tr_red                 false
% 1.11/0.83  --prep_def_merge_tr_cl                  false
% 1.11/0.83  --smt_preprocessing                     true
% 1.11/0.83  --smt_ac_axioms                         fast
% 1.11/0.83  --preprocessed_out                      false
% 1.11/0.83  --preprocessed_stats                    false
% 1.11/0.83  
% 1.11/0.83  ------ Abstraction refinement Options
% 1.11/0.83  
% 1.11/0.83  --abstr_ref                             []
% 1.11/0.83  --abstr_ref_prep                        false
% 1.11/0.83  --abstr_ref_until_sat                   false
% 1.11/0.83  --abstr_ref_sig_restrict                funpre
% 1.11/0.83  --abstr_ref_af_restrict_to_split_sk     false
% 1.11/0.83  --abstr_ref_under                       []
% 1.11/0.83  
% 1.11/0.83  ------ SAT Options
% 1.11/0.83  
% 1.11/0.83  --sat_mode                              false
% 1.11/0.83  --sat_fm_restart_options                ""
% 1.11/0.83  --sat_gr_def                            false
% 1.11/0.83  --sat_epr_types                         true
% 1.11/0.83  --sat_non_cyclic_types                  false
% 1.11/0.83  --sat_finite_models                     false
% 1.11/0.83  --sat_fm_lemmas                         false
% 1.11/0.83  --sat_fm_prep                           false
% 1.11/0.83  --sat_fm_uc_incr                        true
% 1.11/0.83  --sat_out_model                         small
% 1.11/0.83  --sat_out_clauses                       false
% 1.11/0.83  
% 1.11/0.83  ------ QBF Options
% 1.11/0.83  
% 1.11/0.83  --qbf_mode                              false
% 1.11/0.83  --qbf_elim_univ                         false
% 1.11/0.83  --qbf_dom_inst                          none
% 1.11/0.83  --qbf_dom_pre_inst                      false
% 1.11/0.83  --qbf_sk_in                             false
% 1.11/0.83  --qbf_pred_elim                         true
% 1.11/0.83  --qbf_split                             512
% 1.11/0.83  
% 1.11/0.83  ------ BMC1 Options
% 1.11/0.83  
% 1.11/0.83  --bmc1_incremental                      false
% 1.11/0.83  --bmc1_axioms                           reachable_all
% 1.11/0.83  --bmc1_min_bound                        0
% 1.11/0.83  --bmc1_max_bound                        -1
% 1.11/0.83  --bmc1_max_bound_default                -1
% 1.11/0.83  --bmc1_symbol_reachability              true
% 1.11/0.83  --bmc1_property_lemmas                  false
% 1.11/0.83  --bmc1_k_induction                      false
% 1.11/0.83  --bmc1_non_equiv_states                 false
% 1.11/0.83  --bmc1_deadlock                         false
% 1.11/0.83  --bmc1_ucm                              false
% 1.11/0.83  --bmc1_add_unsat_core                   none
% 1.11/0.83  --bmc1_unsat_core_children              false
% 1.11/0.83  --bmc1_unsat_core_extrapolate_axioms    false
% 1.11/0.83  --bmc1_out_stat                         full
% 1.11/0.83  --bmc1_ground_init                      false
% 1.11/0.83  --bmc1_pre_inst_next_state              false
% 1.11/0.83  --bmc1_pre_inst_state                   false
% 1.11/0.83  --bmc1_pre_inst_reach_state             false
% 1.11/0.83  --bmc1_out_unsat_core                   false
% 1.11/0.83  --bmc1_aig_witness_out                  false
% 1.11/0.83  --bmc1_verbose                          false
% 1.11/0.83  --bmc1_dump_clauses_tptp                false
% 1.11/0.83  --bmc1_dump_unsat_core_tptp             false
% 1.11/0.83  --bmc1_dump_file                        -
% 1.11/0.83  --bmc1_ucm_expand_uc_limit              128
% 1.11/0.83  --bmc1_ucm_n_expand_iterations          6
% 1.11/0.83  --bmc1_ucm_extend_mode                  1
% 1.11/0.83  --bmc1_ucm_init_mode                    2
% 1.11/0.83  --bmc1_ucm_cone_mode                    none
% 1.11/0.83  --bmc1_ucm_reduced_relation_type        0
% 1.11/0.83  --bmc1_ucm_relax_model                  4
% 1.11/0.83  --bmc1_ucm_full_tr_after_sat            true
% 1.11/0.83  --bmc1_ucm_expand_neg_assumptions       false
% 1.11/0.83  --bmc1_ucm_layered_model                none
% 1.11/0.83  --bmc1_ucm_max_lemma_size               10
% 1.11/0.83  
% 1.11/0.83  ------ AIG Options
% 1.11/0.83  
% 1.11/0.83  --aig_mode                              false
% 1.11/0.83  
% 1.11/0.83  ------ Instantiation Options
% 1.11/0.83  
% 1.11/0.83  --instantiation_flag                    true
% 1.11/0.83  --inst_sos_flag                         false
% 1.11/0.83  --inst_sos_phase                        true
% 1.11/0.83  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.11/0.83  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.11/0.83  --inst_lit_sel_side                     num_symb
% 1.11/0.83  --inst_solver_per_active                1400
% 1.11/0.83  --inst_solver_calls_frac                1.
% 1.11/0.83  --inst_passive_queue_type               priority_queues
% 1.11/0.83  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.11/0.83  --inst_passive_queues_freq              [25;2]
% 1.11/0.83  --inst_dismatching                      true
% 1.11/0.83  --inst_eager_unprocessed_to_passive     true
% 1.11/0.83  --inst_prop_sim_given                   true
% 1.11/0.83  --inst_prop_sim_new                     false
% 1.11/0.83  --inst_subs_new                         false
% 1.11/0.83  --inst_eq_res_simp                      false
% 1.11/0.83  --inst_subs_given                       false
% 1.11/0.83  --inst_orphan_elimination               true
% 1.11/0.83  --inst_learning_loop_flag               true
% 1.11/0.83  --inst_learning_start                   3000
% 1.11/0.83  --inst_learning_factor                  2
% 1.11/0.83  --inst_start_prop_sim_after_learn       3
% 1.11/0.83  --inst_sel_renew                        solver
% 1.11/0.83  --inst_lit_activity_flag                true
% 1.11/0.83  --inst_restr_to_given                   false
% 1.11/0.83  --inst_activity_threshold               500
% 1.11/0.83  --inst_out_proof                        true
% 1.11/0.83  
% 1.11/0.83  ------ Resolution Options
% 1.11/0.83  
% 1.11/0.83  --resolution_flag                       true
% 1.11/0.83  --res_lit_sel                           adaptive
% 1.11/0.83  --res_lit_sel_side                      none
% 1.11/0.83  --res_ordering                          kbo
% 1.11/0.83  --res_to_prop_solver                    active
% 1.11/0.83  --res_prop_simpl_new                    false
% 1.11/0.83  --res_prop_simpl_given                  true
% 1.11/0.83  --res_passive_queue_type                priority_queues
% 1.11/0.83  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.11/0.83  --res_passive_queues_freq               [15;5]
% 1.11/0.83  --res_forward_subs                      full
% 1.11/0.83  --res_backward_subs                     full
% 1.11/0.83  --res_forward_subs_resolution           true
% 1.11/0.83  --res_backward_subs_resolution          true
% 1.11/0.83  --res_orphan_elimination                true
% 1.11/0.83  --res_time_limit                        2.
% 1.11/0.83  --res_out_proof                         true
% 1.11/0.83  
% 1.11/0.83  ------ Superposition Options
% 1.11/0.83  
% 1.11/0.83  --superposition_flag                    true
% 1.11/0.83  --sup_passive_queue_type                priority_queues
% 1.11/0.83  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.11/0.83  --sup_passive_queues_freq               [8;1;4]
% 1.11/0.83  --demod_completeness_check              fast
% 1.11/0.83  --demod_use_ground                      true
% 1.11/0.83  --sup_to_prop_solver                    passive
% 1.11/0.83  --sup_prop_simpl_new                    true
% 1.11/0.83  --sup_prop_simpl_given                  true
% 1.11/0.83  --sup_fun_splitting                     false
% 1.11/0.83  --sup_smt_interval                      50000
% 1.11/0.83  
% 1.11/0.83  ------ Superposition Simplification Setup
% 1.11/0.83  
% 1.11/0.83  --sup_indices_passive                   []
% 1.11/0.83  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/0.83  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/0.83  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/0.83  --sup_full_triv                         [TrivRules;PropSubs]
% 1.11/0.83  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/0.83  --sup_full_bw                           [BwDemod]
% 1.11/0.83  --sup_immed_triv                        [TrivRules]
% 1.11/0.83  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.11/0.83  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/0.83  --sup_immed_bw_main                     []
% 1.11/0.83  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.11/0.83  --sup_input_triv                        [Unflattening;TrivRules]
% 1.11/0.83  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/0.83  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.11/0.83  
% 1.11/0.83  ------ Combination Options
% 1.11/0.83  
% 1.11/0.83  --comb_res_mult                         3
% 1.11/0.83  --comb_sup_mult                         2
% 1.11/0.83  --comb_inst_mult                        10
% 1.11/0.83  
% 1.11/0.83  ------ Debug Options
% 1.11/0.83  
% 1.11/0.83  --dbg_backtrace                         false
% 1.11/0.83  --dbg_dump_prop_clauses                 false
% 1.11/0.83  --dbg_dump_prop_clauses_file            -
% 1.11/0.83  --dbg_out_stat                          false
% 1.11/0.83  ------ Parsing...
% 1.11/0.83  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.11/0.83  
% 1.11/0.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.11/0.83  
% 1.11/0.83  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.11/0.83  
% 1.11/0.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.11/0.83  ------ Proving...
% 1.11/0.83  ------ Problem Properties 
% 1.11/0.83  
% 1.11/0.83  
% 1.11/0.83  clauses                                 18
% 1.11/0.83  conjectures                             2
% 1.11/0.83  EPR                                     7
% 1.11/0.83  Horn                                    17
% 1.11/0.83  unary                                   8
% 1.11/0.83  binary                                  4
% 1.11/0.83  lits                                    34
% 1.11/0.83  lits eq                                 11
% 1.11/0.83  fd_pure                                 0
% 1.11/0.83  fd_pseudo                               0
% 1.11/0.83  fd_cond                                 2
% 1.11/0.83  fd_pseudo_cond                          1
% 1.11/0.83  AC symbols                              0
% 1.11/0.83  
% 1.11/0.83  ------ Schedule dynamic 5 is on 
% 1.11/0.83  
% 1.11/0.83  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.11/0.83  
% 1.11/0.83  
% 1.11/0.83  ------ 
% 1.11/0.83  Current options:
% 1.11/0.83  ------ 
% 1.11/0.83  
% 1.11/0.83  ------ Input Options
% 1.11/0.83  
% 1.11/0.83  --out_options                           all
% 1.11/0.83  --tptp_safe_out                         true
% 1.11/0.83  --problem_path                          ""
% 1.11/0.83  --include_path                          ""
% 1.11/0.83  --clausifier                            res/vclausify_rel
% 1.11/0.83  --clausifier_options                    --mode clausify
% 1.11/0.83  --stdin                                 false
% 1.11/0.83  --stats_out                             all
% 1.11/0.83  
% 1.11/0.83  ------ General Options
% 1.11/0.83  
% 1.11/0.83  --fof                                   false
% 1.11/0.83  --time_out_real                         305.
% 1.11/0.83  --time_out_virtual                      -1.
% 1.11/0.83  --symbol_type_check                     false
% 1.11/0.83  --clausify_out                          false
% 1.11/0.83  --sig_cnt_out                           false
% 1.11/0.83  --trig_cnt_out                          false
% 1.11/0.83  --trig_cnt_out_tolerance                1.
% 1.11/0.83  --trig_cnt_out_sk_spl                   false
% 1.11/0.83  --abstr_cl_out                          false
% 1.11/0.83  
% 1.11/0.83  ------ Global Options
% 1.11/0.83  
% 1.11/0.83  --schedule                              default
% 1.11/0.83  --add_important_lit                     false
% 1.11/0.83  --prop_solver_per_cl                    1000
% 1.11/0.83  --min_unsat_core                        false
% 1.11/0.83  --soft_assumptions                      false
% 1.11/0.83  --soft_lemma_size                       3
% 1.11/0.83  --prop_impl_unit_size                   0
% 1.11/0.83  --prop_impl_unit                        []
% 1.11/0.83  --share_sel_clauses                     true
% 1.11/0.83  --reset_solvers                         false
% 1.11/0.83  --bc_imp_inh                            [conj_cone]
% 1.11/0.83  --conj_cone_tolerance                   3.
% 1.11/0.83  --extra_neg_conj                        none
% 1.11/0.83  --large_theory_mode                     true
% 1.11/0.83  --prolific_symb_bound                   200
% 1.11/0.83  --lt_threshold                          2000
% 1.11/0.83  --clause_weak_htbl                      true
% 1.11/0.83  --gc_record_bc_elim                     false
% 1.11/0.83  
% 1.11/0.83  ------ Preprocessing Options
% 1.11/0.83  
% 1.11/0.83  --preprocessing_flag                    true
% 1.11/0.83  --time_out_prep_mult                    0.1
% 1.11/0.83  --splitting_mode                        input
% 1.11/0.83  --splitting_grd                         true
% 1.11/0.83  --splitting_cvd                         false
% 1.11/0.83  --splitting_cvd_svl                     false
% 1.11/0.83  --splitting_nvd                         32
% 1.11/0.83  --sub_typing                            true
% 1.11/0.83  --prep_gs_sim                           true
% 1.11/0.83  --prep_unflatten                        true
% 1.11/0.83  --prep_res_sim                          true
% 1.11/0.83  --prep_upred                            true
% 1.11/0.83  --prep_sem_filter                       exhaustive
% 1.11/0.83  --prep_sem_filter_out                   false
% 1.11/0.83  --pred_elim                             true
% 1.11/0.83  --res_sim_input                         true
% 1.11/0.83  --eq_ax_congr_red                       true
% 1.11/0.83  --pure_diseq_elim                       true
% 1.11/0.83  --brand_transform                       false
% 1.11/0.83  --non_eq_to_eq                          false
% 1.11/0.83  --prep_def_merge                        true
% 1.11/0.83  --prep_def_merge_prop_impl              false
% 1.11/0.83  --prep_def_merge_mbd                    true
% 1.11/0.83  --prep_def_merge_tr_red                 false
% 1.11/0.83  --prep_def_merge_tr_cl                  false
% 1.11/0.83  --smt_preprocessing                     true
% 1.11/0.83  --smt_ac_axioms                         fast
% 1.11/0.83  --preprocessed_out                      false
% 1.11/0.83  --preprocessed_stats                    false
% 1.11/0.83  
% 1.11/0.83  ------ Abstraction refinement Options
% 1.11/0.83  
% 1.11/0.83  --abstr_ref                             []
% 1.11/0.83  --abstr_ref_prep                        false
% 1.11/0.83  --abstr_ref_until_sat                   false
% 1.11/0.83  --abstr_ref_sig_restrict                funpre
% 1.11/0.83  --abstr_ref_af_restrict_to_split_sk     false
% 1.11/0.83  --abstr_ref_under                       []
% 1.11/0.83  
% 1.11/0.83  ------ SAT Options
% 1.11/0.83  
% 1.11/0.83  --sat_mode                              false
% 1.11/0.83  --sat_fm_restart_options                ""
% 1.11/0.83  --sat_gr_def                            false
% 1.11/0.83  --sat_epr_types                         true
% 1.11/0.83  --sat_non_cyclic_types                  false
% 1.11/0.83  --sat_finite_models                     false
% 1.11/0.83  --sat_fm_lemmas                         false
% 1.11/0.83  --sat_fm_prep                           false
% 1.11/0.83  --sat_fm_uc_incr                        true
% 1.11/0.83  --sat_out_model                         small
% 1.11/0.83  --sat_out_clauses                       false
% 1.11/0.83  
% 1.11/0.83  ------ QBF Options
% 1.11/0.83  
% 1.11/0.83  --qbf_mode                              false
% 1.11/0.83  --qbf_elim_univ                         false
% 1.11/0.83  --qbf_dom_inst                          none
% 1.11/0.83  --qbf_dom_pre_inst                      false
% 1.11/0.83  --qbf_sk_in                             false
% 1.11/0.83  --qbf_pred_elim                         true
% 1.11/0.83  --qbf_split                             512
% 1.11/0.83  
% 1.11/0.83  ------ BMC1 Options
% 1.11/0.83  
% 1.11/0.83  --bmc1_incremental                      false
% 1.11/0.83  --bmc1_axioms                           reachable_all
% 1.11/0.83  --bmc1_min_bound                        0
% 1.11/0.83  --bmc1_max_bound                        -1
% 1.11/0.83  --bmc1_max_bound_default                -1
% 1.11/0.83  --bmc1_symbol_reachability              true
% 1.11/0.83  --bmc1_property_lemmas                  false
% 1.11/0.83  --bmc1_k_induction                      false
% 1.11/0.83  --bmc1_non_equiv_states                 false
% 1.11/0.83  --bmc1_deadlock                         false
% 1.11/0.83  --bmc1_ucm                              false
% 1.11/0.83  --bmc1_add_unsat_core                   none
% 1.11/0.83  --bmc1_unsat_core_children              false
% 1.11/0.83  --bmc1_unsat_core_extrapolate_axioms    false
% 1.11/0.83  --bmc1_out_stat                         full
% 1.11/0.83  --bmc1_ground_init                      false
% 1.11/0.83  --bmc1_pre_inst_next_state              false
% 1.11/0.83  --bmc1_pre_inst_state                   false
% 1.11/0.83  --bmc1_pre_inst_reach_state             false
% 1.11/0.83  --bmc1_out_unsat_core                   false
% 1.11/0.83  --bmc1_aig_witness_out                  false
% 1.11/0.83  --bmc1_verbose                          false
% 1.11/0.83  --bmc1_dump_clauses_tptp                false
% 1.11/0.83  --bmc1_dump_unsat_core_tptp             false
% 1.11/0.83  --bmc1_dump_file                        -
% 1.11/0.83  --bmc1_ucm_expand_uc_limit              128
% 1.11/0.83  --bmc1_ucm_n_expand_iterations          6
% 1.11/0.83  --bmc1_ucm_extend_mode                  1
% 1.11/0.83  --bmc1_ucm_init_mode                    2
% 1.11/0.83  --bmc1_ucm_cone_mode                    none
% 1.11/0.83  --bmc1_ucm_reduced_relation_type        0
% 1.11/0.83  --bmc1_ucm_relax_model                  4
% 1.11/0.83  --bmc1_ucm_full_tr_after_sat            true
% 1.11/0.83  --bmc1_ucm_expand_neg_assumptions       false
% 1.11/0.83  --bmc1_ucm_layered_model                none
% 1.11/0.83  --bmc1_ucm_max_lemma_size               10
% 1.11/0.83  
% 1.11/0.83  ------ AIG Options
% 1.11/0.83  
% 1.11/0.83  --aig_mode                              false
% 1.11/0.83  
% 1.11/0.83  ------ Instantiation Options
% 1.11/0.83  
% 1.11/0.83  --instantiation_flag                    true
% 1.11/0.83  --inst_sos_flag                         false
% 1.11/0.83  --inst_sos_phase                        true
% 1.11/0.83  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.11/0.83  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.11/0.83  --inst_lit_sel_side                     none
% 1.11/0.83  --inst_solver_per_active                1400
% 1.11/0.83  --inst_solver_calls_frac                1.
% 1.11/0.83  --inst_passive_queue_type               priority_queues
% 1.11/0.83  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.11/0.83  --inst_passive_queues_freq              [25;2]
% 1.11/0.83  --inst_dismatching                      true
% 1.11/0.83  --inst_eager_unprocessed_to_passive     true
% 1.11/0.83  --inst_prop_sim_given                   true
% 1.11/0.83  --inst_prop_sim_new                     false
% 1.11/0.83  --inst_subs_new                         false
% 1.11/0.83  --inst_eq_res_simp                      false
% 1.11/0.83  --inst_subs_given                       false
% 1.11/0.83  --inst_orphan_elimination               true
% 1.11/0.83  --inst_learning_loop_flag               true
% 1.11/0.83  --inst_learning_start                   3000
% 1.11/0.83  --inst_learning_factor                  2
% 1.11/0.83  --inst_start_prop_sim_after_learn       3
% 1.11/0.83  --inst_sel_renew                        solver
% 1.11/0.83  --inst_lit_activity_flag                true
% 1.11/0.83  --inst_restr_to_given                   false
% 1.11/0.83  --inst_activity_threshold               500
% 1.11/0.83  --inst_out_proof                        true
% 1.11/0.83  
% 1.11/0.83  ------ Resolution Options
% 1.11/0.83  
% 1.11/0.83  --resolution_flag                       false
% 1.11/0.83  --res_lit_sel                           adaptive
% 1.11/0.83  --res_lit_sel_side                      none
% 1.11/0.83  --res_ordering                          kbo
% 1.11/0.83  --res_to_prop_solver                    active
% 1.11/0.83  --res_prop_simpl_new                    false
% 1.11/0.83  --res_prop_simpl_given                  true
% 1.11/0.83  --res_passive_queue_type                priority_queues
% 1.11/0.83  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.11/0.83  --res_passive_queues_freq               [15;5]
% 1.11/0.83  --res_forward_subs                      full
% 1.11/0.83  --res_backward_subs                     full
% 1.11/0.83  --res_forward_subs_resolution           true
% 1.11/0.83  --res_backward_subs_resolution          true
% 1.11/0.83  --res_orphan_elimination                true
% 1.11/0.83  --res_time_limit                        2.
% 1.11/0.83  --res_out_proof                         true
% 1.11/0.83  
% 1.11/0.83  ------ Superposition Options
% 1.11/0.83  
% 1.11/0.83  --superposition_flag                    true
% 1.11/0.83  --sup_passive_queue_type                priority_queues
% 1.11/0.83  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.11/0.83  --sup_passive_queues_freq               [8;1;4]
% 1.11/0.83  --demod_completeness_check              fast
% 1.11/0.83  --demod_use_ground                      true
% 1.11/0.83  --sup_to_prop_solver                    passive
% 1.11/0.83  --sup_prop_simpl_new                    true
% 1.11/0.83  --sup_prop_simpl_given                  true
% 1.11/0.83  --sup_fun_splitting                     false
% 1.11/0.83  --sup_smt_interval                      50000
% 1.11/0.83  
% 1.11/0.83  ------ Superposition Simplification Setup
% 1.11/0.83  
% 1.11/0.83  --sup_indices_passive                   []
% 1.11/0.83  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/0.83  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/0.83  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/0.83  --sup_full_triv                         [TrivRules;PropSubs]
% 1.11/0.83  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/0.83  --sup_full_bw                           [BwDemod]
% 1.11/0.83  --sup_immed_triv                        [TrivRules]
% 1.11/0.83  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.11/0.84  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/0.84  --sup_immed_bw_main                     []
% 1.11/0.84  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.11/0.84  --sup_input_triv                        [Unflattening;TrivRules]
% 1.11/0.84  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/0.84  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.11/0.84  
% 1.11/0.84  ------ Combination Options
% 1.11/0.84  
% 1.11/0.84  --comb_res_mult                         3
% 1.11/0.84  --comb_sup_mult                         2
% 1.11/0.84  --comb_inst_mult                        10
% 1.11/0.84  
% 1.11/0.84  ------ Debug Options
% 1.11/0.84  
% 1.11/0.84  --dbg_backtrace                         false
% 1.11/0.84  --dbg_dump_prop_clauses                 false
% 1.11/0.84  --dbg_dump_prop_clauses_file            -
% 1.11/0.84  --dbg_out_stat                          false
% 1.11/0.84  
% 1.11/0.84  
% 1.11/0.84  
% 1.11/0.84  
% 1.11/0.84  ------ Proving...
% 1.11/0.84  
% 1.11/0.84  
% 1.11/0.84  % SZS status Theorem for theBenchmark.p
% 1.11/0.84  
% 1.11/0.84  % SZS output start CNFRefutation for theBenchmark.p
% 1.11/0.84  
% 1.11/0.84  fof(f7,axiom,(
% 1.11/0.84    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.11/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/0.84  
% 1.11/0.84  fof(f17,plain,(
% 1.11/0.84    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.11/0.84    inference(ennf_transformation,[],[f7])).
% 1.11/0.84  
% 1.11/0.84  fof(f18,plain,(
% 1.11/0.84    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.11/0.84    inference(flattening,[],[f17])).
% 1.11/0.84  
% 1.11/0.84  fof(f41,plain,(
% 1.11/0.84    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.11/0.84    inference(cnf_transformation,[],[f18])).
% 1.11/0.84  
% 1.11/0.84  fof(f13,conjecture,(
% 1.11/0.84    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.11/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/0.84  
% 1.11/0.84  fof(f14,negated_conjecture,(
% 1.11/0.84    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.11/0.84    inference(negated_conjecture,[],[f13])).
% 1.11/0.84  
% 1.11/0.84  fof(f24,plain,(
% 1.11/0.84    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.11/0.84    inference(ennf_transformation,[],[f14])).
% 1.11/0.84  
% 1.11/0.84  fof(f29,plain,(
% 1.11/0.84    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.11/0.84    introduced(choice_axiom,[])).
% 1.11/0.84  
% 1.11/0.84  fof(f30,plain,(
% 1.11/0.84    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.11/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f29])).
% 1.11/0.84  
% 1.11/0.84  fof(f48,plain,(
% 1.11/0.84    v1_relat_1(sK0)),
% 1.11/0.84    inference(cnf_transformation,[],[f30])).
% 1.11/0.84  
% 1.11/0.84  fof(f12,axiom,(
% 1.11/0.84    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.11/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/0.84  
% 1.11/0.84  fof(f46,plain,(
% 1.11/0.84    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.11/0.84    inference(cnf_transformation,[],[f12])).
% 1.11/0.84  
% 1.11/0.84  fof(f10,axiom,(
% 1.11/0.84    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.11/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/0.84  
% 1.11/0.84  fof(f22,plain,(
% 1.11/0.84    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.11/0.84    inference(ennf_transformation,[],[f10])).
% 1.11/0.84  
% 1.11/0.84  fof(f44,plain,(
% 1.11/0.84    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.11/0.84    inference(cnf_transformation,[],[f22])).
% 1.11/0.84  
% 1.11/0.84  fof(f6,axiom,(
% 1.11/0.84    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.11/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/0.84  
% 1.11/0.84  fof(f16,plain,(
% 1.11/0.84    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.11/0.84    inference(ennf_transformation,[],[f6])).
% 1.11/0.84  
% 1.11/0.84  fof(f40,plain,(
% 1.11/0.84    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.11/0.84    inference(cnf_transformation,[],[f16])).
% 1.11/0.84  
% 1.11/0.84  fof(f1,axiom,(
% 1.11/0.84    v1_xboole_0(k1_xboole_0)),
% 1.11/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/0.84  
% 1.11/0.84  fof(f31,plain,(
% 1.11/0.84    v1_xboole_0(k1_xboole_0)),
% 1.11/0.84    inference(cnf_transformation,[],[f1])).
% 1.11/0.84  
% 1.11/0.84  fof(f4,axiom,(
% 1.11/0.84    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.11/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/0.84  
% 1.11/0.84  fof(f36,plain,(
% 1.11/0.84    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.11/0.84    inference(cnf_transformation,[],[f4])).
% 1.11/0.84  
% 1.11/0.84  fof(f3,axiom,(
% 1.11/0.84    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.11/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/0.84  
% 1.11/0.84  fof(f25,plain,(
% 1.11/0.84    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.11/0.84    inference(nnf_transformation,[],[f3])).
% 1.11/0.84  
% 1.11/0.84  fof(f26,plain,(
% 1.11/0.84    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.11/0.84    inference(flattening,[],[f25])).
% 1.11/0.84  
% 1.11/0.84  fof(f35,plain,(
% 1.11/0.84    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.11/0.84    inference(cnf_transformation,[],[f26])).
% 1.11/0.84  
% 1.11/0.84  fof(f9,axiom,(
% 1.11/0.84    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.11/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/0.84  
% 1.11/0.84  fof(f21,plain,(
% 1.11/0.84    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.11/0.84    inference(ennf_transformation,[],[f9])).
% 1.11/0.84  
% 1.11/0.84  fof(f43,plain,(
% 1.11/0.84    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.11/0.84    inference(cnf_transformation,[],[f21])).
% 1.11/0.84  
% 1.11/0.84  fof(f5,axiom,(
% 1.11/0.84    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.11/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/0.84  
% 1.11/0.84  fof(f27,plain,(
% 1.11/0.84    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.11/0.84    inference(nnf_transformation,[],[f5])).
% 1.11/0.84  
% 1.11/0.84  fof(f28,plain,(
% 1.11/0.84    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.11/0.84    inference(flattening,[],[f27])).
% 1.11/0.84  
% 1.11/0.84  fof(f38,plain,(
% 1.11/0.84    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.11/0.84    inference(cnf_transformation,[],[f28])).
% 1.11/0.84  
% 1.11/0.84  fof(f53,plain,(
% 1.11/0.84    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.11/0.84    inference(equality_resolution,[],[f38])).
% 1.11/0.84  
% 1.11/0.84  fof(f47,plain,(
% 1.11/0.84    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.11/0.84    inference(cnf_transformation,[],[f12])).
% 1.11/0.84  
% 1.11/0.84  fof(f11,axiom,(
% 1.11/0.84    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.11/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/0.84  
% 1.11/0.84  fof(f23,plain,(
% 1.11/0.84    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.11/0.84    inference(ennf_transformation,[],[f11])).
% 1.11/0.84  
% 1.11/0.84  fof(f45,plain,(
% 1.11/0.84    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.11/0.84    inference(cnf_transformation,[],[f23])).
% 1.11/0.84  
% 1.11/0.84  fof(f8,axiom,(
% 1.11/0.84    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 1.11/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/0.84  
% 1.11/0.84  fof(f19,plain,(
% 1.11/0.84    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.11/0.84    inference(ennf_transformation,[],[f8])).
% 1.11/0.84  
% 1.11/0.84  fof(f20,plain,(
% 1.11/0.84    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.11/0.84    inference(flattening,[],[f19])).
% 1.11/0.84  
% 1.11/0.84  fof(f42,plain,(
% 1.11/0.84    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.11/0.84    inference(cnf_transformation,[],[f20])).
% 1.11/0.84  
% 1.11/0.84  fof(f2,axiom,(
% 1.11/0.84    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.11/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/0.84  
% 1.11/0.84  fof(f15,plain,(
% 1.11/0.84    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.11/0.84    inference(ennf_transformation,[],[f2])).
% 1.11/0.84  
% 1.11/0.84  fof(f32,plain,(
% 1.11/0.84    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.11/0.84    inference(cnf_transformation,[],[f15])).
% 1.11/0.84  
% 1.11/0.84  fof(f49,plain,(
% 1.11/0.84    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.11/0.84    inference(cnf_transformation,[],[f30])).
% 1.11/0.84  
% 1.11/0.84  cnf(c_10,plain,
% 1.11/0.84      ( ~ v1_relat_1(X0)
% 1.11/0.84      | ~ v1_relat_1(X1)
% 1.11/0.84      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 1.11/0.84      inference(cnf_transformation,[],[f41]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_474,plain,
% 1.11/0.84      ( v1_relat_1(X0) != iProver_top
% 1.11/0.84      | v1_relat_1(X1) != iProver_top
% 1.11/0.84      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 1.11/0.84      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_18,negated_conjecture,
% 1.11/0.84      ( v1_relat_1(sK0) ),
% 1.11/0.84      inference(cnf_transformation,[],[f48]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_469,plain,
% 1.11/0.84      ( v1_relat_1(sK0) = iProver_top ),
% 1.11/0.84      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_16,plain,
% 1.11/0.84      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.11/0.84      inference(cnf_transformation,[],[f46]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_13,plain,
% 1.11/0.84      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 1.11/0.84      | ~ v1_relat_1(X1)
% 1.11/0.84      | ~ v1_relat_1(X0) ),
% 1.11/0.84      inference(cnf_transformation,[],[f44]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_471,plain,
% 1.11/0.84      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 1.11/0.84      | v1_relat_1(X1) != iProver_top
% 1.11/0.84      | v1_relat_1(X0) != iProver_top ),
% 1.11/0.84      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_1209,plain,
% 1.11/0.84      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 1.11/0.84      | v1_relat_1(X0) != iProver_top
% 1.11/0.84      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.11/0.84      inference(superposition,[status(thm)],[c_16,c_471]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_9,plain,
% 1.11/0.84      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 1.11/0.84      inference(cnf_transformation,[],[f40]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_35,plain,
% 1.11/0.84      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 1.11/0.84      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_37,plain,
% 1.11/0.84      ( v1_relat_1(k1_xboole_0) = iProver_top
% 1.11/0.84      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.11/0.84      inference(instantiation,[status(thm)],[c_35]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_0,plain,
% 1.11/0.84      ( v1_xboole_0(k1_xboole_0) ),
% 1.11/0.84      inference(cnf_transformation,[],[f31]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_51,plain,
% 1.11/0.84      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.11/0.84      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_1369,plain,
% 1.11/0.84      ( v1_relat_1(X0) != iProver_top
% 1.11/0.84      | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 1.11/0.84      inference(global_propositional_subsumption,
% 1.11/0.84                [status(thm)],
% 1.11/0.84                [c_1209,c_37,c_51]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_1370,plain,
% 1.11/0.84      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 1.11/0.84      | v1_relat_1(X0) != iProver_top ),
% 1.11/0.84      inference(renaming,[status(thm)],[c_1369]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_5,plain,
% 1.11/0.84      ( r1_tarski(k1_xboole_0,X0) ),
% 1.11/0.84      inference(cnf_transformation,[],[f36]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_476,plain,
% 1.11/0.84      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.11/0.84      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_2,plain,
% 1.11/0.84      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.11/0.84      inference(cnf_transformation,[],[f35]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_478,plain,
% 1.11/0.84      ( X0 = X1
% 1.11/0.84      | r1_tarski(X0,X1) != iProver_top
% 1.11/0.84      | r1_tarski(X1,X0) != iProver_top ),
% 1.11/0.84      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_1108,plain,
% 1.11/0.84      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.11/0.84      inference(superposition,[status(thm)],[c_476,c_478]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_1376,plain,
% 1.11/0.84      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 1.11/0.84      | v1_relat_1(X0) != iProver_top ),
% 1.11/0.84      inference(superposition,[status(thm)],[c_1370,c_1108]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_2034,plain,
% 1.11/0.84      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 1.11/0.84      inference(superposition,[status(thm)],[c_469,c_1376]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_12,plain,
% 1.11/0.84      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 1.11/0.84      | ~ v1_relat_1(X0) ),
% 1.11/0.84      inference(cnf_transformation,[],[f43]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_472,plain,
% 1.11/0.84      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 1.11/0.84      | v1_relat_1(X0) != iProver_top ),
% 1.11/0.84      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_1109,plain,
% 1.11/0.84      ( k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)) = X0
% 1.11/0.84      | r1_tarski(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)),X0) != iProver_top
% 1.11/0.84      | v1_relat_1(X0) != iProver_top ),
% 1.11/0.84      inference(superposition,[status(thm)],[c_472,c_478]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_2155,plain,
% 1.11/0.84      ( k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k5_relat_1(k1_xboole_0,sK0)
% 1.11/0.84      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0)) != iProver_top
% 1.11/0.84      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 1.11/0.84      inference(superposition,[status(thm)],[c_2034,c_1109]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_2184,plain,
% 1.11/0.84      ( k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k5_relat_1(k1_xboole_0,sK0)
% 1.11/0.84      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))),k5_relat_1(k1_xboole_0,sK0)) != iProver_top
% 1.11/0.84      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 1.11/0.84      inference(light_normalisation,[status(thm)],[c_2155,c_2034]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_7,plain,
% 1.11/0.84      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.11/0.84      inference(cnf_transformation,[],[f53]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_2185,plain,
% 1.11/0.84      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
% 1.11/0.84      | r1_tarski(k1_xboole_0,k5_relat_1(k1_xboole_0,sK0)) != iProver_top
% 1.11/0.84      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 1.11/0.84      inference(demodulation,[status(thm)],[c_2184,c_7]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_15,plain,
% 1.11/0.84      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.11/0.84      inference(cnf_transformation,[],[f47]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_14,plain,
% 1.11/0.84      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 1.11/0.84      | ~ v1_relat_1(X1)
% 1.11/0.84      | ~ v1_relat_1(X0) ),
% 1.11/0.84      inference(cnf_transformation,[],[f45]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_470,plain,
% 1.11/0.84      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 1.11/0.84      | v1_relat_1(X1) != iProver_top
% 1.11/0.84      | v1_relat_1(X0) != iProver_top ),
% 1.11/0.84      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_755,plain,
% 1.11/0.84      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 1.11/0.84      | v1_relat_1(X0) != iProver_top
% 1.11/0.84      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.11/0.84      inference(superposition,[status(thm)],[c_15,c_470]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_1353,plain,
% 1.11/0.84      ( v1_relat_1(X0) != iProver_top
% 1.11/0.84      | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 1.11/0.84      inference(global_propositional_subsumption,
% 1.11/0.84                [status(thm)],
% 1.11/0.84                [c_755,c_37,c_51]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_1354,plain,
% 1.11/0.84      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 1.11/0.84      | v1_relat_1(X0) != iProver_top ),
% 1.11/0.84      inference(renaming,[status(thm)],[c_1353]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_1360,plain,
% 1.11/0.84      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 1.11/0.84      | v1_relat_1(X0) != iProver_top ),
% 1.11/0.84      inference(superposition,[status(thm)],[c_1354,c_1108]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_1574,plain,
% 1.11/0.84      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 1.11/0.84      inference(superposition,[status(thm)],[c_469,c_1360]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_11,plain,
% 1.11/0.84      ( ~ v1_relat_1(X0)
% 1.11/0.84      | v1_xboole_0(X0)
% 1.11/0.84      | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 1.11/0.84      inference(cnf_transformation,[],[f42]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_473,plain,
% 1.11/0.84      ( v1_relat_1(X0) != iProver_top
% 1.11/0.84      | v1_xboole_0(X0) = iProver_top
% 1.11/0.84      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 1.11/0.84      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_1591,plain,
% 1.11/0.84      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 1.11/0.84      | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
% 1.11/0.84      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.11/0.84      inference(superposition,[status(thm)],[c_1574,c_473]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_19,plain,
% 1.11/0.84      ( v1_relat_1(sK0) = iProver_top ),
% 1.11/0.84      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_591,plain,
% 1.11/0.84      ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 1.11/0.84      | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
% 1.11/0.84      | ~ v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 1.11/0.84      inference(instantiation,[status(thm)],[c_11]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_592,plain,
% 1.11/0.84      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 1.11/0.84      | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
% 1.11/0.84      | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) != iProver_top ),
% 1.11/0.84      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_631,plain,
% 1.11/0.84      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 1.11/0.84      | ~ v1_relat_1(sK0)
% 1.11/0.84      | ~ v1_relat_1(k1_xboole_0) ),
% 1.11/0.84      inference(instantiation,[status(thm)],[c_10]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_632,plain,
% 1.11/0.84      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
% 1.11/0.84      | v1_relat_1(sK0) != iProver_top
% 1.11/0.84      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.11/0.84      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_240,plain,
% 1.11/0.84      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.11/0.84      theory(equality) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_730,plain,
% 1.11/0.84      ( ~ v1_xboole_0(X0)
% 1.11/0.84      | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 1.11/0.84      | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != X0 ),
% 1.11/0.84      inference(instantiation,[status(thm)],[c_240]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_731,plain,
% 1.11/0.84      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != X0
% 1.11/0.84      | v1_xboole_0(X0) != iProver_top
% 1.11/0.84      | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 1.11/0.84      inference(predicate_to_equality,[status(thm)],[c_730]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_733,plain,
% 1.11/0.84      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != k1_xboole_0
% 1.11/0.84      | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 1.11/0.84      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.11/0.84      inference(instantiation,[status(thm)],[c_731]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_1716,plain,
% 1.11/0.84      ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top ),
% 1.11/0.84      inference(global_propositional_subsumption,
% 1.11/0.84                [status(thm)],
% 1.11/0.84                [c_1591,c_19,c_37,c_51,c_592,c_632,c_733,c_1574]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_1,plain,
% 1.11/0.84      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.11/0.84      inference(cnf_transformation,[],[f32]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_479,plain,
% 1.11/0.84      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 1.11/0.84      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_1722,plain,
% 1.11/0.84      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 1.11/0.84      inference(superposition,[status(thm)],[c_1716,c_479]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_17,negated_conjecture,
% 1.11/0.84      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 1.11/0.84      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 1.11/0.84      inference(cnf_transformation,[],[f49]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_1795,plain,
% 1.11/0.84      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
% 1.11/0.84      | k1_xboole_0 != k1_xboole_0 ),
% 1.11/0.84      inference(demodulation,[status(thm)],[c_1722,c_17]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_1796,plain,
% 1.11/0.84      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
% 1.11/0.84      inference(equality_resolution_simp,[status(thm)],[c_1795]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_2157,plain,
% 1.11/0.84      ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) = iProver_top
% 1.11/0.84      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 1.11/0.84      inference(superposition,[status(thm)],[c_2034,c_472]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_2172,plain,
% 1.11/0.84      ( r1_tarski(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) = iProver_top
% 1.11/0.84      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 1.11/0.84      inference(demodulation,[status(thm)],[c_2157,c_7]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_2247,plain,
% 1.11/0.84      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
% 1.11/0.84      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 1.11/0.84      inference(superposition,[status(thm)],[c_2172,c_1108]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_2254,plain,
% 1.11/0.84      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 1.11/0.84      inference(global_propositional_subsumption,
% 1.11/0.84                [status(thm)],
% 1.11/0.84                [c_2185,c_1796,c_2247]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(c_2259,plain,
% 1.11/0.84      ( v1_relat_1(sK0) != iProver_top
% 1.11/0.84      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.11/0.84      inference(superposition,[status(thm)],[c_474,c_2254]) ).
% 1.11/0.84  
% 1.11/0.84  cnf(contradiction,plain,
% 1.11/0.84      ( $false ),
% 1.11/0.84      inference(minisat,[status(thm)],[c_2259,c_51,c_37,c_19]) ).
% 1.11/0.84  
% 1.11/0.84  
% 1.11/0.84  % SZS output end CNFRefutation for theBenchmark.p
% 1.11/0.84  
% 1.11/0.84  ------                               Statistics
% 1.11/0.84  
% 1.11/0.84  ------ General
% 1.11/0.84  
% 1.11/0.84  abstr_ref_over_cycles:                  0
% 1.11/0.84  abstr_ref_under_cycles:                 0
% 1.11/0.84  gc_basic_clause_elim:                   0
% 1.11/0.84  forced_gc_time:                         0
% 1.11/0.84  parsing_time:                           0.01
% 1.11/0.84  unif_index_cands_time:                  0.
% 1.11/0.84  unif_index_add_time:                    0.
% 1.11/0.84  orderings_time:                         0.
% 1.11/0.84  out_proof_time:                         0.012
% 1.11/0.84  total_time:                             0.08
% 1.11/0.84  num_of_symbols:                         40
% 1.11/0.84  num_of_terms:                           1835
% 1.11/0.84  
% 1.11/0.84  ------ Preprocessing
% 1.11/0.84  
% 1.11/0.84  num_of_splits:                          0
% 1.11/0.84  num_of_split_atoms:                     0
% 1.11/0.84  num_of_reused_defs:                     0
% 1.11/0.84  num_eq_ax_congr_red:                    0
% 1.11/0.84  num_of_sem_filtered_clauses:            1
% 1.11/0.84  num_of_subtypes:                        0
% 1.11/0.84  monotx_restored_types:                  0
% 1.11/0.84  sat_num_of_epr_types:                   0
% 1.11/0.84  sat_num_of_non_cyclic_types:            0
% 1.11/0.84  sat_guarded_non_collapsed_types:        0
% 1.11/0.84  num_pure_diseq_elim:                    0
% 1.11/0.84  simp_replaced_by:                       0
% 1.11/0.84  res_preprocessed:                       91
% 1.11/0.84  prep_upred:                             0
% 1.11/0.84  prep_unflattend:                        0
% 1.11/0.84  smt_new_axioms:                         0
% 1.11/0.84  pred_elim_cands:                        3
% 1.11/0.84  pred_elim:                              0
% 1.11/0.84  pred_elim_cl:                           0
% 1.11/0.84  pred_elim_cycles:                       2
% 1.11/0.84  merged_defs:                            0
% 1.11/0.84  merged_defs_ncl:                        0
% 1.11/0.84  bin_hyper_res:                          0
% 1.11/0.84  prep_cycles:                            4
% 1.11/0.84  pred_elim_time:                         0.
% 1.11/0.84  splitting_time:                         0.
% 1.11/0.84  sem_filter_time:                        0.
% 1.11/0.84  monotx_time:                            0.
% 1.11/0.84  subtype_inf_time:                       0.
% 1.11/0.84  
% 1.11/0.84  ------ Problem properties
% 1.11/0.84  
% 1.11/0.84  clauses:                                18
% 1.11/0.84  conjectures:                            2
% 1.11/0.84  epr:                                    7
% 1.11/0.84  horn:                                   17
% 1.11/0.84  ground:                                 5
% 1.11/0.84  unary:                                  8
% 1.11/0.84  binary:                                 4
% 1.11/0.84  lits:                                   34
% 1.11/0.84  lits_eq:                                11
% 1.11/0.84  fd_pure:                                0
% 1.11/0.84  fd_pseudo:                              0
% 1.11/0.84  fd_cond:                                2
% 1.11/0.84  fd_pseudo_cond:                         1
% 1.11/0.84  ac_symbols:                             0
% 1.11/0.84  
% 1.11/0.84  ------ Propositional Solver
% 1.11/0.84  
% 1.11/0.84  prop_solver_calls:                      29
% 1.11/0.84  prop_fast_solver_calls:                 487
% 1.11/0.84  smt_solver_calls:                       0
% 1.11/0.84  smt_fast_solver_calls:                  0
% 1.11/0.84  prop_num_of_clauses:                    748
% 1.11/0.84  prop_preprocess_simplified:             3136
% 1.11/0.84  prop_fo_subsumed:                       15
% 1.11/0.84  prop_solver_time:                       0.
% 1.11/0.84  smt_solver_time:                        0.
% 1.11/0.84  smt_fast_solver_time:                   0.
% 1.11/0.84  prop_fast_solver_time:                  0.
% 1.11/0.84  prop_unsat_core_time:                   0.
% 1.11/0.84  
% 1.11/0.84  ------ QBF
% 1.11/0.84  
% 1.11/0.84  qbf_q_res:                              0
% 1.11/0.84  qbf_num_tautologies:                    0
% 1.11/0.84  qbf_prep_cycles:                        0
% 1.11/0.84  
% 1.11/0.84  ------ BMC1
% 1.11/0.84  
% 1.11/0.84  bmc1_current_bound:                     -1
% 1.11/0.84  bmc1_last_solved_bound:                 -1
% 1.11/0.84  bmc1_unsat_core_size:                   -1
% 1.11/0.84  bmc1_unsat_core_parents_size:           -1
% 1.11/0.84  bmc1_merge_next_fun:                    0
% 1.11/0.84  bmc1_unsat_core_clauses_time:           0.
% 1.11/0.84  
% 1.11/0.84  ------ Instantiation
% 1.11/0.84  
% 1.11/0.84  inst_num_of_clauses:                    293
% 1.11/0.84  inst_num_in_passive:                    105
% 1.11/0.84  inst_num_in_active:                     139
% 1.11/0.84  inst_num_in_unprocessed:                49
% 1.11/0.84  inst_num_of_loops:                      190
% 1.11/0.84  inst_num_of_learning_restarts:          0
% 1.11/0.84  inst_num_moves_active_passive:          47
% 1.11/0.84  inst_lit_activity:                      0
% 1.11/0.84  inst_lit_activity_moves:                0
% 1.11/0.84  inst_num_tautologies:                   0
% 1.11/0.84  inst_num_prop_implied:                  0
% 1.11/0.84  inst_num_existing_simplified:           0
% 1.11/0.84  inst_num_eq_res_simplified:             0
% 1.11/0.84  inst_num_child_elim:                    0
% 1.11/0.84  inst_num_of_dismatching_blockings:      47
% 1.11/0.84  inst_num_of_non_proper_insts:           329
% 1.11/0.84  inst_num_of_duplicates:                 0
% 1.11/0.84  inst_inst_num_from_inst_to_res:         0
% 1.11/0.84  inst_dismatching_checking_time:         0.
% 1.11/0.84  
% 1.11/0.84  ------ Resolution
% 1.11/0.84  
% 1.11/0.84  res_num_of_clauses:                     0
% 1.11/0.84  res_num_in_passive:                     0
% 1.11/0.84  res_num_in_active:                      0
% 1.11/0.84  res_num_of_loops:                       95
% 1.11/0.84  res_forward_subset_subsumed:            22
% 1.11/0.84  res_backward_subset_subsumed:           0
% 1.11/0.84  res_forward_subsumed:                   0
% 1.11/0.84  res_backward_subsumed:                  0
% 1.11/0.84  res_forward_subsumption_resolution:     0
% 1.11/0.84  res_backward_subsumption_resolution:    0
% 1.11/0.84  res_clause_to_clause_subsumption:       173
% 1.11/0.84  res_orphan_elimination:                 0
% 1.11/0.84  res_tautology_del:                      30
% 1.11/0.84  res_num_eq_res_simplified:              0
% 1.11/0.84  res_num_sel_changes:                    0
% 1.11/0.84  res_moves_from_active_to_pass:          0
% 1.11/0.84  
% 1.11/0.84  ------ Superposition
% 1.11/0.84  
% 1.11/0.84  sup_time_total:                         0.
% 1.11/0.84  sup_time_generating:                    0.
% 1.11/0.84  sup_time_sim_full:                      0.
% 1.11/0.84  sup_time_sim_immed:                     0.
% 1.11/0.84  
% 1.11/0.84  sup_num_of_clauses:                     50
% 1.11/0.84  sup_num_in_active:                      34
% 1.11/0.84  sup_num_in_passive:                     16
% 1.11/0.84  sup_num_of_loops:                       37
% 1.11/0.84  sup_fw_superposition:                   27
% 1.11/0.84  sup_bw_superposition:                   41
% 1.11/0.84  sup_immediate_simplified:               32
% 1.11/0.84  sup_given_eliminated:                   1
% 1.11/0.84  comparisons_done:                       0
% 1.11/0.84  comparisons_avoided:                    0
% 1.11/0.84  
% 1.11/0.84  ------ Simplifications
% 1.11/0.84  
% 1.11/0.84  
% 1.11/0.84  sim_fw_subset_subsumed:                 1
% 1.11/0.84  sim_bw_subset_subsumed:                 1
% 1.11/0.84  sim_fw_subsumed:                        13
% 1.11/0.84  sim_bw_subsumed:                        0
% 1.11/0.84  sim_fw_subsumption_res:                 0
% 1.11/0.84  sim_bw_subsumption_res:                 0
% 1.11/0.84  sim_tautology_del:                      1
% 1.11/0.84  sim_eq_tautology_del:                   9
% 1.11/0.84  sim_eq_res_simp:                        1
% 1.11/0.84  sim_fw_demodulated:                     10
% 1.11/0.84  sim_bw_demodulated:                     4
% 1.11/0.84  sim_light_normalised:                   26
% 1.11/0.84  sim_joinable_taut:                      0
% 1.11/0.84  sim_joinable_simp:                      0
% 1.11/0.84  sim_ac_normalised:                      0
% 1.11/0.84  sim_smt_subsumption:                    0
% 1.11/0.84  
%------------------------------------------------------------------------------
