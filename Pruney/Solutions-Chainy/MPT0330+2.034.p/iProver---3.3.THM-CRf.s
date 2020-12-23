%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:13 EST 2020

% Result     : Theorem 27.43s
% Output     : CNFRefutation 27.43s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 228 expanded)
%              Number of clauses        :   55 (  85 expanded)
%              Number of leaves         :    9 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :  182 ( 450 expanded)
%              Number of equality atoms :   52 ( 126 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f24,f24])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f27,f24,f24])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f17,f18])).

fof(f29,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f31,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(definition_unfolding,[],[f31,f24,f24,f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_6,plain,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k2_zfmisc_1(X0,k3_tarski(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_105,plain,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X2_38))) = k2_zfmisc_1(X0_38,k3_tarski(k2_tarski(X1_38,X2_38))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_111,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(X0_38,k3_tarski(k2_tarski(X2_38,X1_38))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_284,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(X0_38,k3_tarski(k2_tarski(X2_38,X1_38))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_111])).

cnf(c_1331,plain,
    ( r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38)) != iProver_top
    | r1_tarski(X0_38,k2_zfmisc_1(X1_38,k3_tarski(k2_tarski(X3_38,X2_38)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_105,c_284])).

cnf(c_7,plain,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_104,plain,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X2_38,X1_38))) = k2_zfmisc_1(k3_tarski(k2_tarski(X0_38,X2_38)),X1_38) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1330,plain,
    ( r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38)) != iProver_top
    | r1_tarski(X0_38,k2_zfmisc_1(k3_tarski(k2_tarski(X3_38,X1_38)),X2_38)) = iProver_top ),
    inference(superposition,[status(thm)],[c_104,c_284])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_101,negated_conjecture,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_292,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_110,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X1_38,X2_38)
    | r1_tarski(X0_38,X2_38) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_285,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(X1_38,X2_38) != iProver_top
    | r1_tarski(X0_38,X2_38) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_110])).

cnf(c_4185,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),X0_38) != iProver_top
    | r1_tarski(sK0,X0_38) = iProver_top ),
    inference(superposition,[status(thm)],[c_292,c_285])).

cnf(c_6340,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X0_38,X1_38)) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(X2_38,X0_38)),X1_38)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1330,c_4185])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_108,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X2_38,X1_38)
    | r1_tarski(k3_tarski(k2_tarski(X0_38,X2_38)),X1_38) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_287,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(X2_38,X1_38) != iProver_top
    | r1_tarski(k3_tarski(k2_tarski(X0_38,X2_38)),X1_38) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_108])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_103,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_290,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_103])).

cnf(c_7993,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_287,c_290])).

cnf(c_9863,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1330,c_7993])).

cnf(c_19702,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top
    | r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6340,c_9863])).

cnf(c_11,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_106,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(k2_zfmisc_1(X0_38,X2_38),k2_zfmisc_1(X1_38,X2_38)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_370,plain,
    ( ~ r1_tarski(X0_38,k3_tarski(k2_tarski(X0_38,X1_38)))
    | r1_tarski(k2_zfmisc_1(X0_38,X2_38),k2_zfmisc_1(k3_tarski(k2_tarski(X0_38,X1_38)),X2_38)) ),
    inference(instantiation,[status(thm)],[c_106])).

cnf(c_14609,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))
    | ~ r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK4))) ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_14612,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) = iProver_top
    | r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14609])).

cnf(c_685,plain,
    ( ~ r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38))
    | r1_tarski(X0_38,k2_zfmisc_1(k3_tarski(k2_tarski(X1_38,X3_38)),X2_38))
    | ~ r1_tarski(k2_zfmisc_1(X1_38,X2_38),k2_zfmisc_1(k3_tarski(k2_tarski(X1_38,X3_38)),X2_38)) ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_36469,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_36470,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) = iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36469])).

cnf(c_2,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_109,plain,
    ( r1_tarski(X0_38,k3_tarski(k2_tarski(X0_38,X1_38))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_53968,plain,
    ( r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK4))) ),
    inference(instantiation,[status(thm)],[c_109])).

cnf(c_53969,plain,
    ( r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53968])).

cnf(c_53975,plain,
    ( r1_tarski(sK3,k3_tarski(k2_tarski(sK3,sK5))) ),
    inference(instantiation,[status(thm)],[c_109])).

cnf(c_53976,plain,
    ( r1_tarski(sK3,k3_tarski(k2_tarski(sK3,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53975])).

cnf(c_1481,plain,
    ( ~ r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38))
    | r1_tarski(X0_38,k2_zfmisc_1(X1_38,k3_tarski(k2_tarski(X2_38,X3_38))))
    | ~ r1_tarski(k2_zfmisc_1(X1_38,X2_38),k2_zfmisc_1(X1_38,k3_tarski(k2_tarski(X2_38,X3_38)))) ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_33443,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,X0_38))))
    | r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,X0_38))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1481])).

cnf(c_56152,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))))
    | r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_33443])).

cnf(c_56153,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) = iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56152])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_107,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(k2_zfmisc_1(X2_38,X0_38),k2_zfmisc_1(X2_38,X1_38)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_388,plain,
    ( ~ r1_tarski(X0_38,k3_tarski(k2_tarski(X0_38,X1_38)))
    | r1_tarski(k2_zfmisc_1(X2_38,X0_38),k2_zfmisc_1(X2_38,k3_tarski(k2_tarski(X0_38,X1_38)))) ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_63714,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))))
    | ~ r1_tarski(sK3,k3_tarski(k2_tarski(sK3,sK5))) ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_63717,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) = iProver_top
    | r1_tarski(sK3,k3_tarski(k2_tarski(sK3,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63714])).

cnf(c_100837,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19702,c_11,c_9863,c_14612,c_36470,c_53969,c_53976,c_56153,c_63717])).

cnf(c_100842,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1331,c_100837])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_12,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_100842,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 27.43/4.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.43/4.01  
% 27.43/4.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.43/4.01  
% 27.43/4.01  ------  iProver source info
% 27.43/4.01  
% 27.43/4.01  git: date: 2020-06-30 10:37:57 +0100
% 27.43/4.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.43/4.01  git: non_committed_changes: false
% 27.43/4.01  git: last_make_outside_of_git: false
% 27.43/4.01  
% 27.43/4.01  ------ 
% 27.43/4.01  ------ Parsing...
% 27.43/4.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.43/4.01  
% 27.43/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.43/4.01  
% 27.43/4.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.43/4.01  
% 27.43/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.43/4.01  ------ Proving...
% 27.43/4.01  ------ Problem Properties 
% 27.43/4.01  
% 27.43/4.01  
% 27.43/4.01  clauses                                 11
% 27.43/4.01  conjectures                             3
% 27.43/4.01  EPR                                     1
% 27.43/4.01  Horn                                    11
% 27.43/4.01  unary                                   6
% 27.43/4.01  binary                                  3
% 27.43/4.01  lits                                    18
% 27.43/4.01  lits eq                                 2
% 27.43/4.01  fd_pure                                 0
% 27.43/4.01  fd_pseudo                               0
% 27.43/4.01  fd_cond                                 0
% 27.43/4.01  fd_pseudo_cond                          0
% 27.43/4.01  AC symbols                              0
% 27.43/4.01  
% 27.43/4.01  ------ Input Options Time Limit: Unbounded
% 27.43/4.01  
% 27.43/4.01  
% 27.43/4.01  ------ 
% 27.43/4.01  Current options:
% 27.43/4.01  ------ 
% 27.43/4.01  
% 27.43/4.01  
% 27.43/4.01  
% 27.43/4.01  
% 27.43/4.01  ------ Proving...
% 27.43/4.01  
% 27.43/4.01  
% 27.43/4.01  % SZS status Theorem for theBenchmark.p
% 27.43/4.01  
% 27.43/4.01  % SZS output start CNFRefutation for theBenchmark.p
% 27.43/4.01  
% 27.43/4.01  fof(f7,axiom,(
% 27.43/4.01    ! [X0,X1,X2] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2))),
% 27.43/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.43/4.01  
% 27.43/4.01  fof(f28,plain,(
% 27.43/4.01    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))) )),
% 27.43/4.01    inference(cnf_transformation,[],[f7])).
% 27.43/4.01  
% 27.43/4.01  fof(f5,axiom,(
% 27.43/4.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 27.43/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.43/4.01  
% 27.43/4.01  fof(f24,plain,(
% 27.43/4.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 27.43/4.01    inference(cnf_transformation,[],[f5])).
% 27.43/4.01  
% 27.43/4.01  fof(f35,plain,(
% 27.43/4.01    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1)))) )),
% 27.43/4.01    inference(definition_unfolding,[],[f28,f24,f24])).
% 27.43/4.01  
% 27.43/4.01  fof(f1,axiom,(
% 27.43/4.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 27.43/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.43/4.01  
% 27.43/4.01  fof(f10,plain,(
% 27.43/4.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 27.43/4.01    inference(ennf_transformation,[],[f1])).
% 27.43/4.01  
% 27.43/4.01  fof(f20,plain,(
% 27.43/4.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 27.43/4.01    inference(cnf_transformation,[],[f10])).
% 27.43/4.01  
% 27.43/4.01  fof(f32,plain,(
% 27.43/4.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 27.43/4.01    inference(definition_unfolding,[],[f20,f24])).
% 27.43/4.01  
% 27.43/4.01  fof(f27,plain,(
% 27.43/4.01    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2)) )),
% 27.43/4.01    inference(cnf_transformation,[],[f7])).
% 27.43/4.01  
% 27.43/4.01  fof(f36,plain,(
% 27.43/4.01    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2)) )),
% 27.43/4.01    inference(definition_unfolding,[],[f27,f24,f24])).
% 27.43/4.01  
% 27.43/4.01  fof(f8,conjecture,(
% 27.43/4.01    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 27.43/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.43/4.01  
% 27.43/4.01  fof(f9,negated_conjecture,(
% 27.43/4.01    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 27.43/4.01    inference(negated_conjecture,[],[f8])).
% 27.43/4.01  
% 27.43/4.01  fof(f16,plain,(
% 27.43/4.01    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 27.43/4.01    inference(ennf_transformation,[],[f9])).
% 27.43/4.01  
% 27.43/4.01  fof(f17,plain,(
% 27.43/4.01    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 27.43/4.01    inference(flattening,[],[f16])).
% 27.43/4.01  
% 27.43/4.01  fof(f18,plain,(
% 27.43/4.01    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 27.43/4.01    introduced(choice_axiom,[])).
% 27.43/4.01  
% 27.43/4.01  fof(f19,plain,(
% 27.43/4.01    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 27.43/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f17,f18])).
% 27.43/4.01  
% 27.43/4.01  fof(f29,plain,(
% 27.43/4.01    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 27.43/4.01    inference(cnf_transformation,[],[f19])).
% 27.43/4.01  
% 27.43/4.01  fof(f2,axiom,(
% 27.43/4.01    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 27.43/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.43/4.01  
% 27.43/4.01  fof(f11,plain,(
% 27.43/4.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 27.43/4.01    inference(ennf_transformation,[],[f2])).
% 27.43/4.01  
% 27.43/4.01  fof(f12,plain,(
% 27.43/4.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 27.43/4.01    inference(flattening,[],[f11])).
% 27.43/4.01  
% 27.43/4.01  fof(f21,plain,(
% 27.43/4.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 27.43/4.01    inference(cnf_transformation,[],[f12])).
% 27.43/4.01  
% 27.43/4.01  fof(f4,axiom,(
% 27.43/4.01    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 27.43/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.43/4.01  
% 27.43/4.01  fof(f13,plain,(
% 27.43/4.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 27.43/4.01    inference(ennf_transformation,[],[f4])).
% 27.43/4.01  
% 27.43/4.01  fof(f14,plain,(
% 27.43/4.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 27.43/4.01    inference(flattening,[],[f13])).
% 27.43/4.01  
% 27.43/4.01  fof(f23,plain,(
% 27.43/4.01    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 27.43/4.01    inference(cnf_transformation,[],[f14])).
% 27.43/4.01  
% 27.43/4.01  fof(f34,plain,(
% 27.43/4.01    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 27.43/4.01    inference(definition_unfolding,[],[f23,f24])).
% 27.43/4.01  
% 27.43/4.01  fof(f31,plain,(
% 27.43/4.01    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 27.43/4.01    inference(cnf_transformation,[],[f19])).
% 27.43/4.01  
% 27.43/4.01  fof(f37,plain,(
% 27.43/4.01    ~r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 27.43/4.01    inference(definition_unfolding,[],[f31,f24,f24,f24])).
% 27.43/4.01  
% 27.43/4.01  fof(f6,axiom,(
% 27.43/4.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 27.43/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.43/4.01  
% 27.43/4.01  fof(f15,plain,(
% 27.43/4.01    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 27.43/4.01    inference(ennf_transformation,[],[f6])).
% 27.43/4.01  
% 27.43/4.01  fof(f25,plain,(
% 27.43/4.01    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 27.43/4.01    inference(cnf_transformation,[],[f15])).
% 27.43/4.01  
% 27.43/4.01  fof(f3,axiom,(
% 27.43/4.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 27.43/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.43/4.01  
% 27.43/4.01  fof(f22,plain,(
% 27.43/4.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 27.43/4.01    inference(cnf_transformation,[],[f3])).
% 27.43/4.01  
% 27.43/4.01  fof(f33,plain,(
% 27.43/4.01    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 27.43/4.01    inference(definition_unfolding,[],[f22,f24])).
% 27.43/4.01  
% 27.43/4.01  fof(f26,plain,(
% 27.43/4.01    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 27.43/4.01    inference(cnf_transformation,[],[f15])).
% 27.43/4.01  
% 27.43/4.01  fof(f30,plain,(
% 27.43/4.01    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 27.43/4.01    inference(cnf_transformation,[],[f19])).
% 27.43/4.01  
% 27.43/4.01  cnf(c_6,plain,
% 27.43/4.01      ( k3_tarski(k2_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k2_zfmisc_1(X0,k3_tarski(k2_tarski(X1,X2))) ),
% 27.43/4.01      inference(cnf_transformation,[],[f35]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_105,plain,
% 27.43/4.01      ( k3_tarski(k2_tarski(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X2_38))) = k2_zfmisc_1(X0_38,k3_tarski(k2_tarski(X1_38,X2_38))) ),
% 27.43/4.01      inference(subtyping,[status(esa)],[c_6]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_0,plain,
% 27.43/4.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
% 27.43/4.01      inference(cnf_transformation,[],[f32]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_111,plain,
% 27.43/4.01      ( ~ r1_tarski(X0_38,X1_38)
% 27.43/4.01      | r1_tarski(X0_38,k3_tarski(k2_tarski(X2_38,X1_38))) ),
% 27.43/4.01      inference(subtyping,[status(esa)],[c_0]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_284,plain,
% 27.43/4.01      ( r1_tarski(X0_38,X1_38) != iProver_top
% 27.43/4.01      | r1_tarski(X0_38,k3_tarski(k2_tarski(X2_38,X1_38))) = iProver_top ),
% 27.43/4.01      inference(predicate_to_equality,[status(thm)],[c_111]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_1331,plain,
% 27.43/4.01      ( r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38)) != iProver_top
% 27.43/4.01      | r1_tarski(X0_38,k2_zfmisc_1(X1_38,k3_tarski(k2_tarski(X3_38,X2_38)))) = iProver_top ),
% 27.43/4.01      inference(superposition,[status(thm)],[c_105,c_284]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_7,plain,
% 27.43/4.01      ( k3_tarski(k2_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 27.43/4.01      inference(cnf_transformation,[],[f36]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_104,plain,
% 27.43/4.01      ( k3_tarski(k2_tarski(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X2_38,X1_38))) = k2_zfmisc_1(k3_tarski(k2_tarski(X0_38,X2_38)),X1_38) ),
% 27.43/4.01      inference(subtyping,[status(esa)],[c_7]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_1330,plain,
% 27.43/4.01      ( r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38)) != iProver_top
% 27.43/4.01      | r1_tarski(X0_38,k2_zfmisc_1(k3_tarski(k2_tarski(X3_38,X1_38)),X2_38)) = iProver_top ),
% 27.43/4.01      inference(superposition,[status(thm)],[c_104,c_284]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_10,negated_conjecture,
% 27.43/4.01      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
% 27.43/4.01      inference(cnf_transformation,[],[f29]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_101,negated_conjecture,
% 27.43/4.01      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
% 27.43/4.01      inference(subtyping,[status(esa)],[c_10]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_292,plain,
% 27.43/4.01      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 27.43/4.01      inference(predicate_to_equality,[status(thm)],[c_101]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_1,plain,
% 27.43/4.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 27.43/4.01      inference(cnf_transformation,[],[f21]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_110,plain,
% 27.43/4.01      ( ~ r1_tarski(X0_38,X1_38)
% 27.43/4.01      | ~ r1_tarski(X1_38,X2_38)
% 27.43/4.01      | r1_tarski(X0_38,X2_38) ),
% 27.43/4.01      inference(subtyping,[status(esa)],[c_1]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_285,plain,
% 27.43/4.01      ( r1_tarski(X0_38,X1_38) != iProver_top
% 27.43/4.01      | r1_tarski(X1_38,X2_38) != iProver_top
% 27.43/4.01      | r1_tarski(X0_38,X2_38) = iProver_top ),
% 27.43/4.01      inference(predicate_to_equality,[status(thm)],[c_110]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_4185,plain,
% 27.43/4.01      ( r1_tarski(k2_zfmisc_1(sK2,sK3),X0_38) != iProver_top
% 27.43/4.01      | r1_tarski(sK0,X0_38) = iProver_top ),
% 27.43/4.01      inference(superposition,[status(thm)],[c_292,c_285]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_6340,plain,
% 27.43/4.01      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X0_38,X1_38)) != iProver_top
% 27.43/4.01      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(X2_38,X0_38)),X1_38)) = iProver_top ),
% 27.43/4.01      inference(superposition,[status(thm)],[c_1330,c_4185]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_3,plain,
% 27.43/4.01      ( ~ r1_tarski(X0,X1)
% 27.43/4.01      | ~ r1_tarski(X2,X1)
% 27.43/4.01      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 27.43/4.01      inference(cnf_transformation,[],[f34]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_108,plain,
% 27.43/4.01      ( ~ r1_tarski(X0_38,X1_38)
% 27.43/4.01      | ~ r1_tarski(X2_38,X1_38)
% 27.43/4.01      | r1_tarski(k3_tarski(k2_tarski(X0_38,X2_38)),X1_38) ),
% 27.43/4.01      inference(subtyping,[status(esa)],[c_3]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_287,plain,
% 27.43/4.01      ( r1_tarski(X0_38,X1_38) != iProver_top
% 27.43/4.01      | r1_tarski(X2_38,X1_38) != iProver_top
% 27.43/4.01      | r1_tarski(k3_tarski(k2_tarski(X0_38,X2_38)),X1_38) = iProver_top ),
% 27.43/4.01      inference(predicate_to_equality,[status(thm)],[c_108]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_8,negated_conjecture,
% 27.43/4.01      ( ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
% 27.43/4.01      inference(cnf_transformation,[],[f37]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_103,negated_conjecture,
% 27.43/4.01      ( ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
% 27.43/4.01      inference(subtyping,[status(esa)],[c_8]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_290,plain,
% 27.43/4.01      ( r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
% 27.43/4.01      inference(predicate_to_equality,[status(thm)],[c_103]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_7993,plain,
% 27.43/4.01      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top
% 27.43/4.01      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
% 27.43/4.01      inference(superposition,[status(thm)],[c_287,c_290]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_9863,plain,
% 27.43/4.01      ( r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top
% 27.43/4.01      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
% 27.43/4.01      inference(superposition,[status(thm)],[c_1330,c_7993]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_19702,plain,
% 27.43/4.01      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top
% 27.43/4.01      | r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
% 27.43/4.01      inference(superposition,[status(thm)],[c_6340,c_9863]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_11,plain,
% 27.43/4.01      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 27.43/4.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_5,plain,
% 27.43/4.01      ( ~ r1_tarski(X0,X1)
% 27.43/4.01      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
% 27.43/4.01      inference(cnf_transformation,[],[f25]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_106,plain,
% 27.43/4.01      ( ~ r1_tarski(X0_38,X1_38)
% 27.43/4.01      | r1_tarski(k2_zfmisc_1(X0_38,X2_38),k2_zfmisc_1(X1_38,X2_38)) ),
% 27.43/4.01      inference(subtyping,[status(esa)],[c_5]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_370,plain,
% 27.43/4.01      ( ~ r1_tarski(X0_38,k3_tarski(k2_tarski(X0_38,X1_38)))
% 27.43/4.01      | r1_tarski(k2_zfmisc_1(X0_38,X2_38),k2_zfmisc_1(k3_tarski(k2_tarski(X0_38,X1_38)),X2_38)) ),
% 27.43/4.01      inference(instantiation,[status(thm)],[c_106]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_14609,plain,
% 27.43/4.01      ( r1_tarski(k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))
% 27.43/4.01      | ~ r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK4))) ),
% 27.43/4.01      inference(instantiation,[status(thm)],[c_370]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_14612,plain,
% 27.43/4.01      ( r1_tarski(k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) = iProver_top
% 27.43/4.01      | r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK4))) != iProver_top ),
% 27.43/4.01      inference(predicate_to_equality,[status(thm)],[c_14609]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_685,plain,
% 27.43/4.01      ( ~ r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38))
% 27.43/4.01      | r1_tarski(X0_38,k2_zfmisc_1(k3_tarski(k2_tarski(X1_38,X3_38)),X2_38))
% 27.43/4.01      | ~ r1_tarski(k2_zfmisc_1(X1_38,X2_38),k2_zfmisc_1(k3_tarski(k2_tarski(X1_38,X3_38)),X2_38)) ),
% 27.43/4.01      inference(instantiation,[status(thm)],[c_110]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_36469,plain,
% 27.43/4.01      ( ~ r1_tarski(k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))
% 27.43/4.01      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))
% 27.43/4.01      | ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) ),
% 27.43/4.01      inference(instantiation,[status(thm)],[c_685]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_36470,plain,
% 27.43/4.01      ( r1_tarski(k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top
% 27.43/4.01      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) = iProver_top
% 27.43/4.01      | r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
% 27.43/4.01      inference(predicate_to_equality,[status(thm)],[c_36469]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_2,plain,
% 27.43/4.01      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 27.43/4.01      inference(cnf_transformation,[],[f33]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_109,plain,
% 27.43/4.01      ( r1_tarski(X0_38,k3_tarski(k2_tarski(X0_38,X1_38))) ),
% 27.43/4.01      inference(subtyping,[status(esa)],[c_2]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_53968,plain,
% 27.43/4.01      ( r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK4))) ),
% 27.43/4.01      inference(instantiation,[status(thm)],[c_109]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_53969,plain,
% 27.43/4.01      ( r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK4))) = iProver_top ),
% 27.43/4.01      inference(predicate_to_equality,[status(thm)],[c_53968]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_53975,plain,
% 27.43/4.01      ( r1_tarski(sK3,k3_tarski(k2_tarski(sK3,sK5))) ),
% 27.43/4.01      inference(instantiation,[status(thm)],[c_109]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_53976,plain,
% 27.43/4.01      ( r1_tarski(sK3,k3_tarski(k2_tarski(sK3,sK5))) = iProver_top ),
% 27.43/4.01      inference(predicate_to_equality,[status(thm)],[c_53975]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_1481,plain,
% 27.43/4.01      ( ~ r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38))
% 27.43/4.01      | r1_tarski(X0_38,k2_zfmisc_1(X1_38,k3_tarski(k2_tarski(X2_38,X3_38))))
% 27.43/4.01      | ~ r1_tarski(k2_zfmisc_1(X1_38,X2_38),k2_zfmisc_1(X1_38,k3_tarski(k2_tarski(X2_38,X3_38)))) ),
% 27.43/4.01      inference(instantiation,[status(thm)],[c_110]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_33443,plain,
% 27.43/4.01      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,X0_38))))
% 27.43/4.01      | r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,X0_38))))
% 27.43/4.01      | ~ r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
% 27.43/4.01      inference(instantiation,[status(thm)],[c_1481]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_56152,plain,
% 27.43/4.01      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))))
% 27.43/4.01      | r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))))
% 27.43/4.01      | ~ r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
% 27.43/4.01      inference(instantiation,[status(thm)],[c_33443]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_56153,plain,
% 27.43/4.01      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top
% 27.43/4.01      | r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) = iProver_top
% 27.43/4.01      | r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) != iProver_top ),
% 27.43/4.01      inference(predicate_to_equality,[status(thm)],[c_56152]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_4,plain,
% 27.43/4.01      ( ~ r1_tarski(X0,X1)
% 27.43/4.01      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
% 27.43/4.01      inference(cnf_transformation,[],[f26]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_107,plain,
% 27.43/4.01      ( ~ r1_tarski(X0_38,X1_38)
% 27.43/4.01      | r1_tarski(k2_zfmisc_1(X2_38,X0_38),k2_zfmisc_1(X2_38,X1_38)) ),
% 27.43/4.01      inference(subtyping,[status(esa)],[c_4]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_388,plain,
% 27.43/4.01      ( ~ r1_tarski(X0_38,k3_tarski(k2_tarski(X0_38,X1_38)))
% 27.43/4.01      | r1_tarski(k2_zfmisc_1(X2_38,X0_38),k2_zfmisc_1(X2_38,k3_tarski(k2_tarski(X0_38,X1_38)))) ),
% 27.43/4.01      inference(instantiation,[status(thm)],[c_107]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_63714,plain,
% 27.43/4.01      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))))
% 27.43/4.01      | ~ r1_tarski(sK3,k3_tarski(k2_tarski(sK3,sK5))) ),
% 27.43/4.01      inference(instantiation,[status(thm)],[c_388]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_63717,plain,
% 27.43/4.01      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) = iProver_top
% 27.43/4.01      | r1_tarski(sK3,k3_tarski(k2_tarski(sK3,sK5))) != iProver_top ),
% 27.43/4.01      inference(predicate_to_equality,[status(thm)],[c_63714]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_100837,plain,
% 27.43/4.01      ( r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
% 27.43/4.01      inference(global_propositional_subsumption,
% 27.43/4.01                [status(thm)],
% 27.43/4.01                [c_19702,c_11,c_9863,c_14612,c_36470,c_53969,c_53976,
% 27.43/4.01                 c_56153,c_63717]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_100842,plain,
% 27.43/4.01      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 27.43/4.01      inference(superposition,[status(thm)],[c_1331,c_100837]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_9,negated_conjecture,
% 27.43/4.01      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
% 27.43/4.01      inference(cnf_transformation,[],[f30]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(c_12,plain,
% 27.43/4.01      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 27.43/4.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.43/4.01  
% 27.43/4.01  cnf(contradiction,plain,
% 27.43/4.01      ( $false ),
% 27.43/4.01      inference(minisat,[status(thm)],[c_100842,c_12]) ).
% 27.43/4.01  
% 27.43/4.01  
% 27.43/4.01  % SZS output end CNFRefutation for theBenchmark.p
% 27.43/4.01  
% 27.43/4.01  ------                               Statistics
% 27.43/4.01  
% 27.43/4.01  ------ Selected
% 27.43/4.01  
% 27.43/4.01  total_time:                             3.256
% 27.43/4.01  
%------------------------------------------------------------------------------
