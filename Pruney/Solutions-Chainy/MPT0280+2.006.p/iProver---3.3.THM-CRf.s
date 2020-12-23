%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:34 EST 2020

% Result     : Theorem 11.71s
% Output     : CNFRefutation 11.71s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 149 expanded)
%              Number of clauses        :   46 (  64 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  161 ( 268 expanded)
%              Number of equality atoms :   33 (  65 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f17])).

fof(f25,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f18])).

fof(f28,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f28])).

fof(f48,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
    inference(definition_unfolding,[],[f48,f41,f41])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f41])).

cnf(c_205,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2530,plain,
    ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
    | r1_tarski(X3,k3_xboole_0(X2,X1))
    | X3 != X0 ),
    inference(resolution,[status(thm)],[c_205,c_0])).

cnf(c_6,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_4794,plain,
    ( r1_tarski(X0,k3_xboole_0(X1,X2))
    | X0 != k3_xboole_0(k3_xboole_0(X2,X1),X3) ),
    inference(resolution,[status(thm)],[c_2530,c_6])).

cnf(c_11089,plain,
    ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,X1)) ),
    inference(resolution,[status(thm)],[c_4794,c_0])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11122,plain,
    ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X2) ),
    inference(resolution,[status(thm)],[c_11089,c_7])).

cnf(c_203,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_202,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1284,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_203,c_202])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2874,plain,
    ( ~ r1_tarski(X0,X1)
    | X0 = k3_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_1284,c_8])).

cnf(c_2542,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_205,c_202])).

cnf(c_3254,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_2874,c_2542])).

cnf(c_11452,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X2,X1)) ),
    inference(resolution,[status(thm)],[c_11122,c_3254])).

cnf(c_2534,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X3,k3_xboole_0(X1,X2))
    | X3 != X0 ),
    inference(resolution,[status(thm)],[c_205,c_8])).

cnf(c_7519,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_2534,c_202])).

cnf(c_11974,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(resolution,[status(thm)],[c_11452,c_7519])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15266,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,k1_zfmisc_1(X0))
    | r1_tarski(X2,k1_zfmisc_1(X1)) ),
    inference(resolution,[status(thm)],[c_11974,c_12])).

cnf(c_37274,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(k1_zfmisc_1(X0),X2),k1_zfmisc_1(X1)) ),
    inference(resolution,[status(thm)],[c_15266,c_6])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3212,plain,
    ( ~ r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)
    | r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),X2),X3) ),
    inference(resolution,[status(thm)],[c_2542,c_10])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_16787,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
    inference(resolution,[status(thm)],[c_3212,c_13])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_17251,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))))
    | ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
    inference(resolution,[status(thm)],[c_16787,c_5])).

cnf(c_387,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_590,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10,c_387])).

cnf(c_591,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_590])).

cnf(c_803,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))))
    | r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))))
    | ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_9,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1197,plain,
    ( r1_tarski(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1552,plain,
    ( r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))))
    | ~ r1_tarski(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_17254,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17251,c_591,c_803,c_1197,c_1552])).

cnf(c_17266,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))))
    | ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
    inference(resolution,[status(thm)],[c_17254,c_5])).

cnf(c_37513,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))))
    | ~ r1_tarski(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[status(thm)],[c_37274,c_17266])).

cnf(c_37524,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37513,c_1197])).

cnf(c_38325,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[status(thm)],[c_37524,c_12])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2399,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1171,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2398,plain,
    ( r1_tarski(sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38325,c_2399,c_2398])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:56:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.71/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.71/2.00  
% 11.71/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.71/2.00  
% 11.71/2.00  ------  iProver source info
% 11.71/2.00  
% 11.71/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.71/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.71/2.00  git: non_committed_changes: false
% 11.71/2.00  git: last_make_outside_of_git: false
% 11.71/2.00  
% 11.71/2.00  ------ 
% 11.71/2.00  ------ Parsing...
% 11.71/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.71/2.00  
% 11.71/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.71/2.00  
% 11.71/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.71/2.00  
% 11.71/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.71/2.00  ------ Proving...
% 11.71/2.00  ------ Problem Properties 
% 11.71/2.00  
% 11.71/2.00  
% 11.71/2.00  clauses                                 13
% 11.71/2.00  conjectures                             1
% 11.71/2.00  EPR                                     2
% 11.71/2.00  Horn                                    13
% 11.71/2.00  unary                                   7
% 11.71/2.00  binary                                  4
% 11.71/2.00  lits                                    21
% 11.71/2.00  lits eq                                 5
% 11.71/2.00  fd_pure                                 0
% 11.71/2.00  fd_pseudo                               0
% 11.71/2.00  fd_cond                                 0
% 11.71/2.00  fd_pseudo_cond                          1
% 11.71/2.00  AC symbols                              0
% 11.71/2.00  
% 11.71/2.00  ------ Input Options Time Limit: Unbounded
% 11.71/2.00  
% 11.71/2.00  
% 11.71/2.00  ------ 
% 11.71/2.00  Current options:
% 11.71/2.00  ------ 
% 11.71/2.00  
% 11.71/2.00  
% 11.71/2.00  
% 11.71/2.00  
% 11.71/2.00  ------ Proving...
% 11.71/2.00  
% 11.71/2.00  
% 11.71/2.00  % SZS status Theorem for theBenchmark.p
% 11.71/2.00  
% 11.71/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.71/2.00  
% 11.71/2.00  fof(f1,axiom,(
% 11.71/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f30,plain,(
% 11.71/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.71/2.00    inference(cnf_transformation,[],[f1])).
% 11.71/2.00  
% 11.71/2.00  fof(f5,axiom,(
% 11.71/2.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f36,plain,(
% 11.71/2.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 11.71/2.00    inference(cnf_transformation,[],[f5])).
% 11.71/2.00  
% 11.71/2.00  fof(f6,axiom,(
% 11.71/2.00    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f22,plain,(
% 11.71/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 11.71/2.00    inference(ennf_transformation,[],[f6])).
% 11.71/2.00  
% 11.71/2.00  fof(f37,plain,(
% 11.71/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 11.71/2.00    inference(cnf_transformation,[],[f22])).
% 11.71/2.00  
% 11.71/2.00  fof(f7,axiom,(
% 11.71/2.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f23,plain,(
% 11.71/2.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.71/2.00    inference(ennf_transformation,[],[f7])).
% 11.71/2.00  
% 11.71/2.00  fof(f38,plain,(
% 11.71/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.71/2.00    inference(cnf_transformation,[],[f23])).
% 11.71/2.00  
% 11.71/2.00  fof(f16,axiom,(
% 11.71/2.00    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f24,plain,(
% 11.71/2.00    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 11.71/2.00    inference(ennf_transformation,[],[f16])).
% 11.71/2.00  
% 11.71/2.00  fof(f47,plain,(
% 11.71/2.00    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.71/2.00    inference(cnf_transformation,[],[f24])).
% 11.71/2.00  
% 11.71/2.00  fof(f9,axiom,(
% 11.71/2.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f40,plain,(
% 11.71/2.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.71/2.00    inference(cnf_transformation,[],[f9])).
% 11.71/2.00  
% 11.71/2.00  fof(f17,conjecture,(
% 11.71/2.00    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f18,negated_conjecture,(
% 11.71/2.00    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 11.71/2.00    inference(negated_conjecture,[],[f17])).
% 11.71/2.00  
% 11.71/2.00  fof(f25,plain,(
% 11.71/2.00    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 11.71/2.00    inference(ennf_transformation,[],[f18])).
% 11.71/2.00  
% 11.71/2.00  fof(f28,plain,(
% 11.71/2.00    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 11.71/2.00    introduced(choice_axiom,[])).
% 11.71/2.00  
% 11.71/2.00  fof(f29,plain,(
% 11.71/2.00    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 11.71/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f28])).
% 11.71/2.00  
% 11.71/2.00  fof(f48,plain,(
% 11.71/2.00    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 11.71/2.00    inference(cnf_transformation,[],[f29])).
% 11.71/2.00  
% 11.71/2.00  fof(f10,axiom,(
% 11.71/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f41,plain,(
% 11.71/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 11.71/2.00    inference(cnf_transformation,[],[f10])).
% 11.71/2.00  
% 11.71/2.00  fof(f55,plain,(
% 11.71/2.00    ~r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))))),
% 11.71/2.00    inference(definition_unfolding,[],[f48,f41,f41])).
% 11.71/2.00  
% 11.71/2.00  fof(f4,axiom,(
% 11.71/2.00    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f20,plain,(
% 11.71/2.00    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 11.71/2.00    inference(ennf_transformation,[],[f4])).
% 11.71/2.00  
% 11.71/2.00  fof(f21,plain,(
% 11.71/2.00    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 11.71/2.00    inference(flattening,[],[f20])).
% 11.71/2.00  
% 11.71/2.00  fof(f35,plain,(
% 11.71/2.00    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 11.71/2.00    inference(cnf_transformation,[],[f21])).
% 11.71/2.00  
% 11.71/2.00  fof(f8,axiom,(
% 11.71/2.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f39,plain,(
% 11.71/2.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.71/2.01    inference(cnf_transformation,[],[f8])).
% 11.71/2.01  
% 11.71/2.01  fof(f53,plain,(
% 11.71/2.01    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) )),
% 11.71/2.01    inference(definition_unfolding,[],[f39,f41])).
% 11.71/2.01  
% 11.71/2.01  fof(f2,axiom,(
% 11.71/2.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.71/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.01  
% 11.71/2.01  fof(f26,plain,(
% 11.71/2.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.71/2.01    inference(nnf_transformation,[],[f2])).
% 11.71/2.01  
% 11.71/2.01  fof(f27,plain,(
% 11.71/2.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.71/2.01    inference(flattening,[],[f26])).
% 11.71/2.01  
% 11.71/2.01  fof(f31,plain,(
% 11.71/2.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.71/2.01    inference(cnf_transformation,[],[f27])).
% 11.71/2.01  
% 11.71/2.01  fof(f57,plain,(
% 11.71/2.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.71/2.01    inference(equality_resolution,[],[f31])).
% 11.71/2.01  
% 11.71/2.01  fof(f3,axiom,(
% 11.71/2.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 11.71/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.01  
% 11.71/2.01  fof(f19,plain,(
% 11.71/2.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 11.71/2.01    inference(ennf_transformation,[],[f3])).
% 11.71/2.01  
% 11.71/2.01  fof(f34,plain,(
% 11.71/2.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 11.71/2.01    inference(cnf_transformation,[],[f19])).
% 11.71/2.01  
% 11.71/2.01  fof(f52,plain,(
% 11.71/2.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 11.71/2.01    inference(definition_unfolding,[],[f34,f41])).
% 11.71/2.01  
% 11.71/2.01  cnf(c_205,plain,
% 11.71/2.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.71/2.01      theory(equality) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_0,plain,
% 11.71/2.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.71/2.01      inference(cnf_transformation,[],[f30]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_2530,plain,
% 11.71/2.01      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
% 11.71/2.01      | r1_tarski(X3,k3_xboole_0(X2,X1))
% 11.71/2.01      | X3 != X0 ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_205,c_0]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_6,plain,
% 11.71/2.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 11.71/2.01      inference(cnf_transformation,[],[f36]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_4794,plain,
% 11.71/2.01      ( r1_tarski(X0,k3_xboole_0(X1,X2))
% 11.71/2.01      | X0 != k3_xboole_0(k3_xboole_0(X2,X1),X3) ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_2530,c_6]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_11089,plain,
% 11.71/2.01      ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,X1)) ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_4794,c_0]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_7,plain,
% 11.71/2.01      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 11.71/2.01      inference(cnf_transformation,[],[f37]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_11122,plain,
% 11.71/2.01      ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X2) ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_11089,c_7]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_203,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_202,plain,( X0 = X0 ),theory(equality) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_1284,plain,
% 11.71/2.01      ( X0 != X1 | X1 = X0 ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_203,c_202]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_8,plain,
% 11.71/2.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 11.71/2.01      inference(cnf_transformation,[],[f38]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_2874,plain,
% 11.71/2.01      ( ~ r1_tarski(X0,X1) | X0 = k3_xboole_0(X0,X1) ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_1284,c_8]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_2542,plain,
% 11.71/2.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_205,c_202]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_3254,plain,
% 11.71/2.01      ( ~ r1_tarski(X0,X1)
% 11.71/2.01      | r1_tarski(X0,X2)
% 11.71/2.01      | ~ r1_tarski(k3_xboole_0(X0,X1),X2) ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_2874,c_2542]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_11452,plain,
% 11.71/2.01      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k3_xboole_0(X2,X1)) ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_11122,c_3254]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_2534,plain,
% 11.71/2.01      ( ~ r1_tarski(X0,X1)
% 11.71/2.01      | ~ r1_tarski(X1,X2)
% 11.71/2.01      | r1_tarski(X3,k3_xboole_0(X1,X2))
% 11.71/2.01      | X3 != X0 ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_205,c_8]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_7519,plain,
% 11.71/2.01      ( ~ r1_tarski(X0,X1)
% 11.71/2.01      | ~ r1_tarski(X1,X2)
% 11.71/2.01      | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_2534,c_202]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_11974,plain,
% 11.71/2.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_11452,c_7519]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_12,plain,
% 11.71/2.01      ( ~ r1_tarski(X0,X1) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
% 11.71/2.01      inference(cnf_transformation,[],[f47]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_15266,plain,
% 11.71/2.01      ( ~ r1_tarski(X0,X1)
% 11.71/2.01      | ~ r1_tarski(X2,k1_zfmisc_1(X0))
% 11.71/2.01      | r1_tarski(X2,k1_zfmisc_1(X1)) ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_11974,c_12]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_37274,plain,
% 11.71/2.01      ( ~ r1_tarski(X0,X1)
% 11.71/2.01      | r1_tarski(k3_xboole_0(k1_zfmisc_1(X0),X2),k1_zfmisc_1(X1)) ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_15266,c_6]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_10,plain,
% 11.71/2.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.71/2.01      inference(cnf_transformation,[],[f40]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_3212,plain,
% 11.71/2.01      ( ~ r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)
% 11.71/2.01      | r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),X2),X3) ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_2542,c_10]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_13,negated_conjecture,
% 11.71/2.01      ( ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
% 11.71/2.01      inference(cnf_transformation,[],[f55]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_16787,plain,
% 11.71/2.01      ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_3212,c_13]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_5,plain,
% 11.71/2.01      ( ~ r1_tarski(X0,X1)
% 11.71/2.01      | ~ r1_tarski(X2,X1)
% 11.71/2.01      | r1_tarski(k5_xboole_0(X0,X2),X1) ),
% 11.71/2.01      inference(cnf_transformation,[],[f35]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_17251,plain,
% 11.71/2.01      ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))))
% 11.71/2.01      | ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_16787,c_5]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_387,plain,
% 11.71/2.01      ( r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) != iProver_top ),
% 11.71/2.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_590,plain,
% 11.71/2.01      ( r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) != iProver_top ),
% 11.71/2.01      inference(demodulation,[status(thm)],[c_10,c_387]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_591,plain,
% 11.71/2.01      ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
% 11.71/2.01      inference(predicate_to_equality_rev,[status(thm)],[c_590]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_803,plain,
% 11.71/2.01      ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))))
% 11.71/2.01      | r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))))
% 11.71/2.01      | ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
% 11.71/2.01      inference(instantiation,[status(thm)],[c_5]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_9,plain,
% 11.71/2.01      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
% 11.71/2.01      inference(cnf_transformation,[],[f53]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_1197,plain,
% 11.71/2.01      ( r1_tarski(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
% 11.71/2.01      inference(instantiation,[status(thm)],[c_9]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_1552,plain,
% 11.71/2.01      ( r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))))
% 11.71/2.01      | ~ r1_tarski(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
% 11.71/2.01      inference(instantiation,[status(thm)],[c_12]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_17254,plain,
% 11.71/2.01      ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
% 11.71/2.01      inference(global_propositional_subsumption,
% 11.71/2.01                [status(thm)],
% 11.71/2.01                [c_17251,c_591,c_803,c_1197,c_1552]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_17266,plain,
% 11.71/2.01      ( ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))))
% 11.71/2.01      | ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_17254,c_5]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_37513,plain,
% 11.71/2.01      ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))))
% 11.71/2.01      | ~ r1_tarski(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_37274,c_17266]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_37524,plain,
% 11.71/2.01      ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
% 11.71/2.01      inference(global_propositional_subsumption,
% 11.71/2.01                [status(thm)],
% 11.71/2.01                [c_37513,c_1197]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_38325,plain,
% 11.71/2.01      ( ~ r1_tarski(sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
% 11.71/2.01      inference(resolution,[status(thm)],[c_37524,c_12]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_3,plain,
% 11.71/2.01      ( r1_tarski(X0,X0) ),
% 11.71/2.01      inference(cnf_transformation,[],[f57]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_2399,plain,
% 11.71/2.01      ( r1_tarski(sK1,sK1) ),
% 11.71/2.01      inference(instantiation,[status(thm)],[c_3]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_4,plain,
% 11.71/2.01      ( ~ r1_tarski(X0,X1)
% 11.71/2.01      | r1_tarski(X0,k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X2,X1))) ),
% 11.71/2.01      inference(cnf_transformation,[],[f52]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_1171,plain,
% 11.71/2.01      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
% 11.71/2.01      | ~ r1_tarski(X0,sK1) ),
% 11.71/2.01      inference(instantiation,[status(thm)],[c_4]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(c_2398,plain,
% 11.71/2.01      ( r1_tarski(sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
% 11.71/2.01      | ~ r1_tarski(sK1,sK1) ),
% 11.71/2.01      inference(instantiation,[status(thm)],[c_1171]) ).
% 11.71/2.01  
% 11.71/2.01  cnf(contradiction,plain,
% 11.71/2.01      ( $false ),
% 11.71/2.01      inference(minisat,[status(thm)],[c_38325,c_2399,c_2398]) ).
% 11.71/2.01  
% 11.71/2.01  
% 11.71/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.71/2.01  
% 11.71/2.01  ------                               Statistics
% 11.71/2.01  
% 11.71/2.01  ------ Selected
% 11.71/2.01  
% 11.71/2.01  total_time:                             1.265
% 11.71/2.01  
%------------------------------------------------------------------------------
