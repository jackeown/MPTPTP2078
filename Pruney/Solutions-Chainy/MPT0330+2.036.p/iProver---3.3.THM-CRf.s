%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:13 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 287 expanded)
%              Number of clauses        :   37 (  50 expanded)
%              Number of leaves         :   11 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :  138 ( 400 expanded)
%              Number of equality atoms :   51 ( 236 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f34])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2) ),
    inference(definition_unfolding,[],[f29,f36,f36])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f36])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_tarski(k3_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f30,f36,f36])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f23,f36])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f19])).

fof(f31,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f36])).

fof(f33,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    ~ r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    inference(definition_unfolding,[],[f33,f36,f36,f36])).

fof(f32,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_5,plain,
    ( k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_82,plain,
    ( k3_tarski(k3_enumset1(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X2_38,X1_38))) = k2_zfmisc_1(k3_tarski(k3_enumset1(X0_38,X0_38,X0_38,X0_38,X2_38)),X1_38) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_87,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(X0_38,k3_tarski(k3_enumset1(X2_38,X2_38,X2_38,X2_38,X1_38))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_213,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(X0_38,k3_tarski(k3_enumset1(X2_38,X2_38,X2_38,X2_38,X1_38))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_87])).

cnf(c_761,plain,
    ( r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38)) != iProver_top
    | r1_tarski(X0_38,k2_zfmisc_1(k3_tarski(k3_enumset1(X3_38,X3_38,X3_38,X3_38,X1_38)),X2_38)) = iProver_top ),
    inference(superposition,[status(thm)],[c_82,c_213])).

cnf(c_4,plain,
    ( k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k2_zfmisc_1(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_83,plain,
    ( k3_tarski(k3_enumset1(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X2_38))) = k2_zfmisc_1(X0_38,k3_tarski(k3_enumset1(X1_38,X1_38,X1_38,X1_38,X2_38))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_85,plain,
    ( r1_tarski(X0_38,k3_tarski(k3_enumset1(X0_38,X0_38,X0_38,X0_38,X1_38))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_215,plain,
    ( r1_tarski(X0_38,k3_tarski(k3_enumset1(X0_38,X0_38,X0_38,X0_38,X1_38))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_85])).

cnf(c_770,plain,
    ( r1_tarski(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,k3_tarski(k3_enumset1(X1_38,X1_38,X1_38,X1_38,X2_38)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_83,c_215])).

cnf(c_760,plain,
    ( r1_tarski(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(k3_tarski(k3_enumset1(X0_38,X0_38,X0_38,X0_38,X2_38)),X1_38)) = iProver_top ),
    inference(superposition,[status(thm)],[c_82,c_215])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_79,negated_conjecture,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_219,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_79])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_86,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X1_38,X2_38)
    | r1_tarski(X0_38,X2_38) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_214,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(X1_38,X2_38) != iProver_top
    | r1_tarski(X0_38,X2_38) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_86])).

cnf(c_539,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),X0_38) != iProver_top
    | r1_tarski(sK0,X0_38) = iProver_top ),
    inference(superposition,[status(thm)],[c_219,c_214])).

cnf(c_905,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0_38)),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_539])).

cnf(c_1248,plain,
    ( r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0_38)),sK3),X1_38) != iProver_top
    | r1_tarski(sK0,X1_38) = iProver_top ),
    inference(superposition,[status(thm)],[c_905,c_214])).

cnf(c_2244,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0_38)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X1_38)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_770,c_1248])).

cnf(c_771,plain,
    ( r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38)) != iProver_top
    | r1_tarski(X0_38,k2_zfmisc_1(X1_38,k3_tarski(k3_enumset1(X3_38,X3_38,X3_38,X3_38,X2_38)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_83,c_213])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_84,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X2_38,X1_38)
    | r1_tarski(k3_tarski(k3_enumset1(X0_38,X0_38,X0_38,X0_38,X2_38)),X1_38) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_216,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(X2_38,X1_38) != iProver_top
    | r1_tarski(k3_tarski(k3_enumset1(X0_38,X0_38,X0_38,X0_38,X2_38)),X1_38) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_84])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_81,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_217,plain,
    ( r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_81])).

cnf(c_1686,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_216,c_217])).

cnf(c_2745,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),sK5)) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_1686])).

cnf(c_11244,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2244,c_2745])).

cnf(c_11254,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_761,c_11244])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_10,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11254,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:03:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 4.07/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/0.97  
% 4.07/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.07/0.97  
% 4.07/0.97  ------  iProver source info
% 4.07/0.97  
% 4.07/0.97  git: date: 2020-06-30 10:37:57 +0100
% 4.07/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.07/0.97  git: non_committed_changes: false
% 4.07/0.97  git: last_make_outside_of_git: false
% 4.07/0.97  
% 4.07/0.97  ------ 
% 4.07/0.97  
% 4.07/0.97  ------ Input Options
% 4.07/0.97  
% 4.07/0.97  --out_options                           all
% 4.07/0.97  --tptp_safe_out                         true
% 4.07/0.97  --problem_path                          ""
% 4.07/0.97  --include_path                          ""
% 4.07/0.97  --clausifier                            res/vclausify_rel
% 4.07/0.97  --clausifier_options                    ""
% 4.07/0.97  --stdin                                 false
% 4.07/0.97  --stats_out                             all
% 4.07/0.97  
% 4.07/0.97  ------ General Options
% 4.07/0.97  
% 4.07/0.97  --fof                                   false
% 4.07/0.97  --time_out_real                         305.
% 4.07/0.97  --time_out_virtual                      -1.
% 4.07/0.97  --symbol_type_check                     false
% 4.07/0.97  --clausify_out                          false
% 4.07/0.97  --sig_cnt_out                           false
% 4.07/0.97  --trig_cnt_out                          false
% 4.07/0.97  --trig_cnt_out_tolerance                1.
% 4.07/0.97  --trig_cnt_out_sk_spl                   false
% 4.07/0.97  --abstr_cl_out                          false
% 4.07/0.97  
% 4.07/0.97  ------ Global Options
% 4.07/0.97  
% 4.07/0.97  --schedule                              default
% 4.07/0.97  --add_important_lit                     false
% 4.07/0.97  --prop_solver_per_cl                    1000
% 4.07/0.97  --min_unsat_core                        false
% 4.07/0.97  --soft_assumptions                      false
% 4.07/0.97  --soft_lemma_size                       3
% 4.07/0.97  --prop_impl_unit_size                   0
% 4.07/0.97  --prop_impl_unit                        []
% 4.07/0.97  --share_sel_clauses                     true
% 4.07/0.97  --reset_solvers                         false
% 4.07/0.97  --bc_imp_inh                            [conj_cone]
% 4.07/0.97  --conj_cone_tolerance                   3.
% 4.07/0.97  --extra_neg_conj                        none
% 4.07/0.97  --large_theory_mode                     true
% 4.07/0.97  --prolific_symb_bound                   200
% 4.07/0.97  --lt_threshold                          2000
% 4.07/0.97  --clause_weak_htbl                      true
% 4.07/0.97  --gc_record_bc_elim                     false
% 4.07/0.97  
% 4.07/0.97  ------ Preprocessing Options
% 4.07/0.97  
% 4.07/0.97  --preprocessing_flag                    true
% 4.07/0.97  --time_out_prep_mult                    0.1
% 4.07/0.97  --splitting_mode                        input
% 4.07/0.97  --splitting_grd                         true
% 4.07/0.97  --splitting_cvd                         false
% 4.07/0.97  --splitting_cvd_svl                     false
% 4.07/0.97  --splitting_nvd                         32
% 4.07/0.97  --sub_typing                            true
% 4.07/0.97  --prep_gs_sim                           true
% 4.07/0.97  --prep_unflatten                        true
% 4.07/0.97  --prep_res_sim                          true
% 4.07/0.97  --prep_upred                            true
% 4.07/0.97  --prep_sem_filter                       exhaustive
% 4.07/0.97  --prep_sem_filter_out                   false
% 4.07/0.97  --pred_elim                             true
% 4.07/0.97  --res_sim_input                         true
% 4.07/0.97  --eq_ax_congr_red                       true
% 4.07/0.97  --pure_diseq_elim                       true
% 4.07/0.97  --brand_transform                       false
% 4.07/0.97  --non_eq_to_eq                          false
% 4.07/0.97  --prep_def_merge                        true
% 4.07/0.97  --prep_def_merge_prop_impl              false
% 4.07/0.97  --prep_def_merge_mbd                    true
% 4.07/0.97  --prep_def_merge_tr_red                 false
% 4.07/0.97  --prep_def_merge_tr_cl                  false
% 4.07/0.97  --smt_preprocessing                     true
% 4.07/0.97  --smt_ac_axioms                         fast
% 4.07/0.97  --preprocessed_out                      false
% 4.07/0.97  --preprocessed_stats                    false
% 4.07/0.97  
% 4.07/0.97  ------ Abstraction refinement Options
% 4.07/0.97  
% 4.07/0.97  --abstr_ref                             []
% 4.07/0.97  --abstr_ref_prep                        false
% 4.07/0.97  --abstr_ref_until_sat                   false
% 4.07/0.97  --abstr_ref_sig_restrict                funpre
% 4.07/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 4.07/0.97  --abstr_ref_under                       []
% 4.07/0.97  
% 4.07/0.97  ------ SAT Options
% 4.07/0.97  
% 4.07/0.97  --sat_mode                              false
% 4.07/0.97  --sat_fm_restart_options                ""
% 4.07/0.97  --sat_gr_def                            false
% 4.07/0.97  --sat_epr_types                         true
% 4.07/0.97  --sat_non_cyclic_types                  false
% 4.07/0.97  --sat_finite_models                     false
% 4.07/0.97  --sat_fm_lemmas                         false
% 4.07/0.97  --sat_fm_prep                           false
% 4.07/0.97  --sat_fm_uc_incr                        true
% 4.07/0.97  --sat_out_model                         small
% 4.07/0.97  --sat_out_clauses                       false
% 4.07/0.97  
% 4.07/0.97  ------ QBF Options
% 4.07/0.97  
% 4.07/0.97  --qbf_mode                              false
% 4.07/0.97  --qbf_elim_univ                         false
% 4.07/0.97  --qbf_dom_inst                          none
% 4.07/0.97  --qbf_dom_pre_inst                      false
% 4.07/0.97  --qbf_sk_in                             false
% 4.07/0.97  --qbf_pred_elim                         true
% 4.07/0.97  --qbf_split                             512
% 4.07/0.97  
% 4.07/0.97  ------ BMC1 Options
% 4.07/0.97  
% 4.07/0.97  --bmc1_incremental                      false
% 4.07/0.97  --bmc1_axioms                           reachable_all
% 4.07/0.97  --bmc1_min_bound                        0
% 4.07/0.97  --bmc1_max_bound                        -1
% 4.07/0.97  --bmc1_max_bound_default                -1
% 4.07/0.97  --bmc1_symbol_reachability              true
% 4.07/0.97  --bmc1_property_lemmas                  false
% 4.07/0.97  --bmc1_k_induction                      false
% 4.07/0.97  --bmc1_non_equiv_states                 false
% 4.07/0.97  --bmc1_deadlock                         false
% 4.07/0.97  --bmc1_ucm                              false
% 4.07/0.97  --bmc1_add_unsat_core                   none
% 4.07/0.97  --bmc1_unsat_core_children              false
% 4.07/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 4.07/0.97  --bmc1_out_stat                         full
% 4.07/0.97  --bmc1_ground_init                      false
% 4.07/0.97  --bmc1_pre_inst_next_state              false
% 4.07/0.97  --bmc1_pre_inst_state                   false
% 4.07/0.97  --bmc1_pre_inst_reach_state             false
% 4.07/0.97  --bmc1_out_unsat_core                   false
% 4.07/0.97  --bmc1_aig_witness_out                  false
% 4.07/0.97  --bmc1_verbose                          false
% 4.07/0.97  --bmc1_dump_clauses_tptp                false
% 4.07/0.97  --bmc1_dump_unsat_core_tptp             false
% 4.07/0.97  --bmc1_dump_file                        -
% 4.07/0.97  --bmc1_ucm_expand_uc_limit              128
% 4.07/0.97  --bmc1_ucm_n_expand_iterations          6
% 4.07/0.97  --bmc1_ucm_extend_mode                  1
% 4.07/0.97  --bmc1_ucm_init_mode                    2
% 4.07/0.97  --bmc1_ucm_cone_mode                    none
% 4.07/0.97  --bmc1_ucm_reduced_relation_type        0
% 4.07/0.97  --bmc1_ucm_relax_model                  4
% 4.07/0.97  --bmc1_ucm_full_tr_after_sat            true
% 4.07/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 4.07/0.97  --bmc1_ucm_layered_model                none
% 4.07/0.97  --bmc1_ucm_max_lemma_size               10
% 4.07/0.97  
% 4.07/0.97  ------ AIG Options
% 4.07/0.97  
% 4.07/0.97  --aig_mode                              false
% 4.07/0.97  
% 4.07/0.97  ------ Instantiation Options
% 4.07/0.97  
% 4.07/0.97  --instantiation_flag                    true
% 4.07/0.97  --inst_sos_flag                         true
% 4.07/0.97  --inst_sos_phase                        true
% 4.07/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.07/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.07/0.97  --inst_lit_sel_side                     num_symb
% 4.07/0.97  --inst_solver_per_active                1400
% 4.07/0.97  --inst_solver_calls_frac                1.
% 4.07/0.97  --inst_passive_queue_type               priority_queues
% 4.07/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.07/0.97  --inst_passive_queues_freq              [25;2]
% 4.07/0.97  --inst_dismatching                      true
% 4.07/0.97  --inst_eager_unprocessed_to_passive     true
% 4.07/0.97  --inst_prop_sim_given                   true
% 4.07/0.97  --inst_prop_sim_new                     false
% 4.07/0.97  --inst_subs_new                         false
% 4.07/0.97  --inst_eq_res_simp                      false
% 4.07/0.97  --inst_subs_given                       false
% 4.07/0.97  --inst_orphan_elimination               true
% 4.07/0.97  --inst_learning_loop_flag               true
% 4.07/0.97  --inst_learning_start                   3000
% 4.07/0.97  --inst_learning_factor                  2
% 4.07/0.97  --inst_start_prop_sim_after_learn       3
% 4.07/0.97  --inst_sel_renew                        solver
% 4.07/0.97  --inst_lit_activity_flag                true
% 4.07/0.97  --inst_restr_to_given                   false
% 4.07/0.97  --inst_activity_threshold               500
% 4.07/0.97  --inst_out_proof                        true
% 4.07/0.97  
% 4.07/0.97  ------ Resolution Options
% 4.07/0.97  
% 4.07/0.97  --resolution_flag                       true
% 4.07/0.97  --res_lit_sel                           adaptive
% 4.07/0.97  --res_lit_sel_side                      none
% 4.07/0.97  --res_ordering                          kbo
% 4.07/0.97  --res_to_prop_solver                    active
% 4.07/0.97  --res_prop_simpl_new                    false
% 4.07/0.97  --res_prop_simpl_given                  true
% 4.07/0.97  --res_passive_queue_type                priority_queues
% 4.07/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.07/0.97  --res_passive_queues_freq               [15;5]
% 4.07/0.97  --res_forward_subs                      full
% 4.07/0.97  --res_backward_subs                     full
% 4.07/0.97  --res_forward_subs_resolution           true
% 4.07/0.97  --res_backward_subs_resolution          true
% 4.07/0.97  --res_orphan_elimination                true
% 4.07/0.97  --res_time_limit                        2.
% 4.07/0.97  --res_out_proof                         true
% 4.07/0.97  
% 4.07/0.97  ------ Superposition Options
% 4.07/0.97  
% 4.07/0.97  --superposition_flag                    true
% 4.07/0.97  --sup_passive_queue_type                priority_queues
% 4.07/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.07/0.97  --sup_passive_queues_freq               [8;1;4]
% 4.07/0.97  --demod_completeness_check              fast
% 4.07/0.97  --demod_use_ground                      true
% 4.07/0.97  --sup_to_prop_solver                    passive
% 4.07/0.97  --sup_prop_simpl_new                    true
% 4.07/0.97  --sup_prop_simpl_given                  true
% 4.07/0.97  --sup_fun_splitting                     true
% 4.07/0.97  --sup_smt_interval                      50000
% 4.07/0.97  
% 4.07/0.97  ------ Superposition Simplification Setup
% 4.07/0.97  
% 4.07/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.07/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.07/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.07/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.07/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 4.07/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.07/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.07/0.97  --sup_immed_triv                        [TrivRules]
% 4.07/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.97  --sup_immed_bw_main                     []
% 4.07/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.07/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 4.07/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.97  --sup_input_bw                          []
% 4.07/0.97  
% 4.07/0.97  ------ Combination Options
% 4.07/0.97  
% 4.07/0.97  --comb_res_mult                         3
% 4.07/0.97  --comb_sup_mult                         2
% 4.07/0.97  --comb_inst_mult                        10
% 4.07/0.97  
% 4.07/0.97  ------ Debug Options
% 4.07/0.97  
% 4.07/0.97  --dbg_backtrace                         false
% 4.07/0.97  --dbg_dump_prop_clauses                 false
% 4.07/0.97  --dbg_dump_prop_clauses_file            -
% 4.07/0.97  --dbg_out_stat                          false
% 4.07/0.97  ------ Parsing...
% 4.07/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.07/0.97  
% 4.07/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.07/0.97  
% 4.07/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.07/0.97  
% 4.07/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.07/0.97  ------ Proving...
% 4.07/0.97  ------ Problem Properties 
% 4.07/0.97  
% 4.07/0.97  
% 4.07/0.97  clauses                                 9
% 4.07/0.97  conjectures                             3
% 4.07/0.97  EPR                                     1
% 4.07/0.97  Horn                                    9
% 4.07/0.97  unary                                   6
% 4.07/0.97  binary                                  1
% 4.07/0.97  lits                                    14
% 4.07/0.97  lits eq                                 2
% 4.07/0.97  fd_pure                                 0
% 4.07/0.97  fd_pseudo                               0
% 4.07/0.97  fd_cond                                 0
% 4.07/0.97  fd_pseudo_cond                          0
% 4.07/0.97  AC symbols                              0
% 4.07/0.97  
% 4.07/0.97  ------ Schedule dynamic 5 is on 
% 4.07/0.97  
% 4.07/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.07/0.97  
% 4.07/0.97  
% 4.07/0.97  ------ 
% 4.07/0.97  Current options:
% 4.07/0.97  ------ 
% 4.07/0.97  
% 4.07/0.97  ------ Input Options
% 4.07/0.97  
% 4.07/0.97  --out_options                           all
% 4.07/0.97  --tptp_safe_out                         true
% 4.07/0.97  --problem_path                          ""
% 4.07/0.97  --include_path                          ""
% 4.07/0.97  --clausifier                            res/vclausify_rel
% 4.07/0.97  --clausifier_options                    ""
% 4.07/0.97  --stdin                                 false
% 4.07/0.97  --stats_out                             all
% 4.07/0.97  
% 4.07/0.97  ------ General Options
% 4.07/0.97  
% 4.07/0.97  --fof                                   false
% 4.07/0.97  --time_out_real                         305.
% 4.07/0.97  --time_out_virtual                      -1.
% 4.07/0.97  --symbol_type_check                     false
% 4.07/0.98  --clausify_out                          false
% 4.07/0.98  --sig_cnt_out                           false
% 4.07/0.98  --trig_cnt_out                          false
% 4.07/0.98  --trig_cnt_out_tolerance                1.
% 4.07/0.98  --trig_cnt_out_sk_spl                   false
% 4.07/0.98  --abstr_cl_out                          false
% 4.07/0.98  
% 4.07/0.98  ------ Global Options
% 4.07/0.98  
% 4.07/0.98  --schedule                              default
% 4.07/0.98  --add_important_lit                     false
% 4.07/0.98  --prop_solver_per_cl                    1000
% 4.07/0.98  --min_unsat_core                        false
% 4.07/0.98  --soft_assumptions                      false
% 4.07/0.98  --soft_lemma_size                       3
% 4.07/0.98  --prop_impl_unit_size                   0
% 4.07/0.98  --prop_impl_unit                        []
% 4.07/0.98  --share_sel_clauses                     true
% 4.07/0.98  --reset_solvers                         false
% 4.07/0.98  --bc_imp_inh                            [conj_cone]
% 4.07/0.98  --conj_cone_tolerance                   3.
% 4.07/0.98  --extra_neg_conj                        none
% 4.07/0.98  --large_theory_mode                     true
% 4.07/0.98  --prolific_symb_bound                   200
% 4.07/0.98  --lt_threshold                          2000
% 4.07/0.98  --clause_weak_htbl                      true
% 4.07/0.98  --gc_record_bc_elim                     false
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing Options
% 4.07/0.98  
% 4.07/0.98  --preprocessing_flag                    true
% 4.07/0.98  --time_out_prep_mult                    0.1
% 4.07/0.98  --splitting_mode                        input
% 4.07/0.98  --splitting_grd                         true
% 4.07/0.98  --splitting_cvd                         false
% 4.07/0.98  --splitting_cvd_svl                     false
% 4.07/0.98  --splitting_nvd                         32
% 4.07/0.98  --sub_typing                            true
% 4.07/0.98  --prep_gs_sim                           true
% 4.07/0.98  --prep_unflatten                        true
% 4.07/0.98  --prep_res_sim                          true
% 4.07/0.98  --prep_upred                            true
% 4.07/0.98  --prep_sem_filter                       exhaustive
% 4.07/0.98  --prep_sem_filter_out                   false
% 4.07/0.98  --pred_elim                             true
% 4.07/0.98  --res_sim_input                         true
% 4.07/0.98  --eq_ax_congr_red                       true
% 4.07/0.98  --pure_diseq_elim                       true
% 4.07/0.98  --brand_transform                       false
% 4.07/0.98  --non_eq_to_eq                          false
% 4.07/0.98  --prep_def_merge                        true
% 4.07/0.98  --prep_def_merge_prop_impl              false
% 4.07/0.98  --prep_def_merge_mbd                    true
% 4.07/0.98  --prep_def_merge_tr_red                 false
% 4.07/0.98  --prep_def_merge_tr_cl                  false
% 4.07/0.98  --smt_preprocessing                     true
% 4.07/0.98  --smt_ac_axioms                         fast
% 4.07/0.98  --preprocessed_out                      false
% 4.07/0.98  --preprocessed_stats                    false
% 4.07/0.98  
% 4.07/0.98  ------ Abstraction refinement Options
% 4.07/0.98  
% 4.07/0.98  --abstr_ref                             []
% 4.07/0.98  --abstr_ref_prep                        false
% 4.07/0.98  --abstr_ref_until_sat                   false
% 4.07/0.98  --abstr_ref_sig_restrict                funpre
% 4.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.07/0.98  --abstr_ref_under                       []
% 4.07/0.98  
% 4.07/0.98  ------ SAT Options
% 4.07/0.98  
% 4.07/0.98  --sat_mode                              false
% 4.07/0.98  --sat_fm_restart_options                ""
% 4.07/0.98  --sat_gr_def                            false
% 4.07/0.98  --sat_epr_types                         true
% 4.07/0.98  --sat_non_cyclic_types                  false
% 4.07/0.98  --sat_finite_models                     false
% 4.07/0.98  --sat_fm_lemmas                         false
% 4.07/0.98  --sat_fm_prep                           false
% 4.07/0.98  --sat_fm_uc_incr                        true
% 4.07/0.98  --sat_out_model                         small
% 4.07/0.98  --sat_out_clauses                       false
% 4.07/0.98  
% 4.07/0.98  ------ QBF Options
% 4.07/0.98  
% 4.07/0.98  --qbf_mode                              false
% 4.07/0.98  --qbf_elim_univ                         false
% 4.07/0.98  --qbf_dom_inst                          none
% 4.07/0.98  --qbf_dom_pre_inst                      false
% 4.07/0.98  --qbf_sk_in                             false
% 4.07/0.98  --qbf_pred_elim                         true
% 4.07/0.98  --qbf_split                             512
% 4.07/0.98  
% 4.07/0.98  ------ BMC1 Options
% 4.07/0.98  
% 4.07/0.98  --bmc1_incremental                      false
% 4.07/0.98  --bmc1_axioms                           reachable_all
% 4.07/0.98  --bmc1_min_bound                        0
% 4.07/0.98  --bmc1_max_bound                        -1
% 4.07/0.98  --bmc1_max_bound_default                -1
% 4.07/0.98  --bmc1_symbol_reachability              true
% 4.07/0.98  --bmc1_property_lemmas                  false
% 4.07/0.98  --bmc1_k_induction                      false
% 4.07/0.98  --bmc1_non_equiv_states                 false
% 4.07/0.98  --bmc1_deadlock                         false
% 4.07/0.98  --bmc1_ucm                              false
% 4.07/0.98  --bmc1_add_unsat_core                   none
% 4.07/0.98  --bmc1_unsat_core_children              false
% 4.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.07/0.98  --bmc1_out_stat                         full
% 4.07/0.98  --bmc1_ground_init                      false
% 4.07/0.98  --bmc1_pre_inst_next_state              false
% 4.07/0.98  --bmc1_pre_inst_state                   false
% 4.07/0.98  --bmc1_pre_inst_reach_state             false
% 4.07/0.98  --bmc1_out_unsat_core                   false
% 4.07/0.98  --bmc1_aig_witness_out                  false
% 4.07/0.98  --bmc1_verbose                          false
% 4.07/0.98  --bmc1_dump_clauses_tptp                false
% 4.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.07/0.98  --bmc1_dump_file                        -
% 4.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.07/0.98  --bmc1_ucm_extend_mode                  1
% 4.07/0.98  --bmc1_ucm_init_mode                    2
% 4.07/0.98  --bmc1_ucm_cone_mode                    none
% 4.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.07/0.98  --bmc1_ucm_relax_model                  4
% 4.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.07/0.98  --bmc1_ucm_layered_model                none
% 4.07/0.98  --bmc1_ucm_max_lemma_size               10
% 4.07/0.98  
% 4.07/0.98  ------ AIG Options
% 4.07/0.98  
% 4.07/0.98  --aig_mode                              false
% 4.07/0.98  
% 4.07/0.98  ------ Instantiation Options
% 4.07/0.98  
% 4.07/0.98  --instantiation_flag                    true
% 4.07/0.98  --inst_sos_flag                         true
% 4.07/0.98  --inst_sos_phase                        true
% 4.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.07/0.98  --inst_lit_sel_side                     none
% 4.07/0.98  --inst_solver_per_active                1400
% 4.07/0.98  --inst_solver_calls_frac                1.
% 4.07/0.98  --inst_passive_queue_type               priority_queues
% 4.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.07/0.98  --inst_passive_queues_freq              [25;2]
% 4.07/0.98  --inst_dismatching                      true
% 4.07/0.98  --inst_eager_unprocessed_to_passive     true
% 4.07/0.98  --inst_prop_sim_given                   true
% 4.07/0.98  --inst_prop_sim_new                     false
% 4.07/0.98  --inst_subs_new                         false
% 4.07/0.98  --inst_eq_res_simp                      false
% 4.07/0.98  --inst_subs_given                       false
% 4.07/0.98  --inst_orphan_elimination               true
% 4.07/0.98  --inst_learning_loop_flag               true
% 4.07/0.98  --inst_learning_start                   3000
% 4.07/0.98  --inst_learning_factor                  2
% 4.07/0.98  --inst_start_prop_sim_after_learn       3
% 4.07/0.98  --inst_sel_renew                        solver
% 4.07/0.98  --inst_lit_activity_flag                true
% 4.07/0.98  --inst_restr_to_given                   false
% 4.07/0.98  --inst_activity_threshold               500
% 4.07/0.98  --inst_out_proof                        true
% 4.07/0.98  
% 4.07/0.98  ------ Resolution Options
% 4.07/0.98  
% 4.07/0.98  --resolution_flag                       false
% 4.07/0.98  --res_lit_sel                           adaptive
% 4.07/0.98  --res_lit_sel_side                      none
% 4.07/0.98  --res_ordering                          kbo
% 4.07/0.98  --res_to_prop_solver                    active
% 4.07/0.98  --res_prop_simpl_new                    false
% 4.07/0.98  --res_prop_simpl_given                  true
% 4.07/0.98  --res_passive_queue_type                priority_queues
% 4.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.07/0.98  --res_passive_queues_freq               [15;5]
% 4.07/0.98  --res_forward_subs                      full
% 4.07/0.98  --res_backward_subs                     full
% 4.07/0.98  --res_forward_subs_resolution           true
% 4.07/0.98  --res_backward_subs_resolution          true
% 4.07/0.98  --res_orphan_elimination                true
% 4.07/0.98  --res_time_limit                        2.
% 4.07/0.98  --res_out_proof                         true
% 4.07/0.98  
% 4.07/0.98  ------ Superposition Options
% 4.07/0.98  
% 4.07/0.98  --superposition_flag                    true
% 4.07/0.98  --sup_passive_queue_type                priority_queues
% 4.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.07/0.98  --demod_completeness_check              fast
% 4.07/0.98  --demod_use_ground                      true
% 4.07/0.98  --sup_to_prop_solver                    passive
% 4.07/0.98  --sup_prop_simpl_new                    true
% 4.07/0.98  --sup_prop_simpl_given                  true
% 4.07/0.98  --sup_fun_splitting                     true
% 4.07/0.98  --sup_smt_interval                      50000
% 4.07/0.98  
% 4.07/0.98  ------ Superposition Simplification Setup
% 4.07/0.98  
% 4.07/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.07/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.07/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.07/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.07/0.98  --sup_immed_triv                        [TrivRules]
% 4.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_immed_bw_main                     []
% 4.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/0.98  --sup_input_bw                          []
% 4.07/0.98  
% 4.07/0.98  ------ Combination Options
% 4.07/0.98  
% 4.07/0.98  --comb_res_mult                         3
% 4.07/0.98  --comb_sup_mult                         2
% 4.07/0.98  --comb_inst_mult                        10
% 4.07/0.98  
% 4.07/0.98  ------ Debug Options
% 4.07/0.98  
% 4.07/0.98  --dbg_backtrace                         false
% 4.07/0.98  --dbg_dump_prop_clauses                 false
% 4.07/0.98  --dbg_dump_prop_clauses_file            -
% 4.07/0.98  --dbg_out_stat                          false
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  ------ Proving...
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  % SZS status Theorem for theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  fof(f9,axiom,(
% 4.07/0.98    ! [X0,X1,X2] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f29,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f9])).
% 4.07/0.98  
% 4.07/0.98  fof(f8,axiom,(
% 4.07/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f28,plain,(
% 4.07/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f8])).
% 4.07/0.98  
% 4.07/0.98  fof(f5,axiom,(
% 4.07/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f25,plain,(
% 4.07/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f5])).
% 4.07/0.98  
% 4.07/0.98  fof(f6,axiom,(
% 4.07/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f26,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f6])).
% 4.07/0.98  
% 4.07/0.98  fof(f7,axiom,(
% 4.07/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f27,plain,(
% 4.07/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f7])).
% 4.07/0.98  
% 4.07/0.98  fof(f34,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 4.07/0.98    inference(definition_unfolding,[],[f26,f27])).
% 4.07/0.98  
% 4.07/0.98  fof(f35,plain,(
% 4.07/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 4.07/0.98    inference(definition_unfolding,[],[f25,f34])).
% 4.07/0.98  
% 4.07/0.98  fof(f36,plain,(
% 4.07/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 4.07/0.98    inference(definition_unfolding,[],[f28,f35])).
% 4.07/0.98  
% 4.07/0.98  fof(f41,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2)) )),
% 4.07/0.98    inference(definition_unfolding,[],[f29,f36,f36])).
% 4.07/0.98  
% 4.07/0.98  fof(f1,axiom,(
% 4.07/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f12,plain,(
% 4.07/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 4.07/0.98    inference(ennf_transformation,[],[f1])).
% 4.07/0.98  
% 4.07/0.98  fof(f21,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f12])).
% 4.07/0.98  
% 4.07/0.98  fof(f37,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 4.07/0.98    inference(definition_unfolding,[],[f21,f36])).
% 4.07/0.98  
% 4.07/0.98  fof(f30,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f9])).
% 4.07/0.98  
% 4.07/0.98  fof(f40,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (k3_tarski(k3_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 4.07/0.98    inference(definition_unfolding,[],[f30,f36,f36])).
% 4.07/0.98  
% 4.07/0.98  fof(f3,axiom,(
% 4.07/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f23,plain,(
% 4.07/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.07/0.98    inference(cnf_transformation,[],[f3])).
% 4.07/0.98  
% 4.07/0.98  fof(f38,plain,(
% 4.07/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 4.07/0.98    inference(definition_unfolding,[],[f23,f36])).
% 4.07/0.98  
% 4.07/0.98  fof(f10,conjecture,(
% 4.07/0.98    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f11,negated_conjecture,(
% 4.07/0.98    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 4.07/0.98    inference(negated_conjecture,[],[f10])).
% 4.07/0.98  
% 4.07/0.98  fof(f17,plain,(
% 4.07/0.98    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 4.07/0.98    inference(ennf_transformation,[],[f11])).
% 4.07/0.98  
% 4.07/0.98  fof(f18,plain,(
% 4.07/0.98    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 4.07/0.98    inference(flattening,[],[f17])).
% 4.07/0.98  
% 4.07/0.98  fof(f19,plain,(
% 4.07/0.98    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 4.07/0.98    introduced(choice_axiom,[])).
% 4.07/0.98  
% 4.07/0.98  fof(f20,plain,(
% 4.07/0.98    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 4.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f19])).
% 4.07/0.98  
% 4.07/0.98  fof(f31,plain,(
% 4.07/0.98    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 4.07/0.98    inference(cnf_transformation,[],[f20])).
% 4.07/0.98  
% 4.07/0.98  fof(f2,axiom,(
% 4.07/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f13,plain,(
% 4.07/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 4.07/0.98    inference(ennf_transformation,[],[f2])).
% 4.07/0.98  
% 4.07/0.98  fof(f14,plain,(
% 4.07/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 4.07/0.98    inference(flattening,[],[f13])).
% 4.07/0.98  
% 4.07/0.98  fof(f22,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f14])).
% 4.07/0.98  
% 4.07/0.98  fof(f4,axiom,(
% 4.07/0.98    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 4.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f15,plain,(
% 4.07/0.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 4.07/0.98    inference(ennf_transformation,[],[f4])).
% 4.07/0.98  
% 4.07/0.98  fof(f16,plain,(
% 4.07/0.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 4.07/0.98    inference(flattening,[],[f15])).
% 4.07/0.98  
% 4.07/0.98  fof(f24,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f16])).
% 4.07/0.98  
% 4.07/0.98  fof(f39,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 4.07/0.98    inference(definition_unfolding,[],[f24,f36])).
% 4.07/0.98  
% 4.07/0.98  fof(f33,plain,(
% 4.07/0.98    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 4.07/0.98    inference(cnf_transformation,[],[f20])).
% 4.07/0.98  
% 4.07/0.98  fof(f42,plain,(
% 4.07/0.98    ~r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))),
% 4.07/0.98    inference(definition_unfolding,[],[f33,f36,f36,f36])).
% 4.07/0.98  
% 4.07/0.98  fof(f32,plain,(
% 4.07/0.98    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 4.07/0.98    inference(cnf_transformation,[],[f20])).
% 4.07/0.98  
% 4.07/0.98  cnf(c_5,plain,
% 4.07/0.98      ( k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) ),
% 4.07/0.98      inference(cnf_transformation,[],[f41]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_82,plain,
% 4.07/0.98      ( k3_tarski(k3_enumset1(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X2_38,X1_38))) = k2_zfmisc_1(k3_tarski(k3_enumset1(X0_38,X0_38,X0_38,X0_38,X2_38)),X1_38) ),
% 4.07/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_0,plain,
% 4.07/0.98      ( ~ r1_tarski(X0,X1)
% 4.07/0.98      | r1_tarski(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
% 4.07/0.98      inference(cnf_transformation,[],[f37]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_87,plain,
% 4.07/0.98      ( ~ r1_tarski(X0_38,X1_38)
% 4.07/0.98      | r1_tarski(X0_38,k3_tarski(k3_enumset1(X2_38,X2_38,X2_38,X2_38,X1_38))) ),
% 4.07/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_213,plain,
% 4.07/0.98      ( r1_tarski(X0_38,X1_38) != iProver_top
% 4.07/0.98      | r1_tarski(X0_38,k3_tarski(k3_enumset1(X2_38,X2_38,X2_38,X2_38,X1_38))) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_87]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_761,plain,
% 4.07/0.98      ( r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38)) != iProver_top
% 4.07/0.98      | r1_tarski(X0_38,k2_zfmisc_1(k3_tarski(k3_enumset1(X3_38,X3_38,X3_38,X3_38,X1_38)),X2_38)) = iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_82,c_213]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_4,plain,
% 4.07/0.98      ( k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k2_zfmisc_1(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
% 4.07/0.98      inference(cnf_transformation,[],[f40]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_83,plain,
% 4.07/0.98      ( k3_tarski(k3_enumset1(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X2_38))) = k2_zfmisc_1(X0_38,k3_tarski(k3_enumset1(X1_38,X1_38,X1_38,X1_38,X2_38))) ),
% 4.07/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_2,plain,
% 4.07/0.98      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 4.07/0.98      inference(cnf_transformation,[],[f38]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_85,plain,
% 4.07/0.98      ( r1_tarski(X0_38,k3_tarski(k3_enumset1(X0_38,X0_38,X0_38,X0_38,X1_38))) ),
% 4.07/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_215,plain,
% 4.07/0.98      ( r1_tarski(X0_38,k3_tarski(k3_enumset1(X0_38,X0_38,X0_38,X0_38,X1_38))) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_85]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_770,plain,
% 4.07/0.98      ( r1_tarski(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,k3_tarski(k3_enumset1(X1_38,X1_38,X1_38,X1_38,X2_38)))) = iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_83,c_215]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_760,plain,
% 4.07/0.98      ( r1_tarski(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(k3_tarski(k3_enumset1(X0_38,X0_38,X0_38,X0_38,X2_38)),X1_38)) = iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_82,c_215]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_8,negated_conjecture,
% 4.07/0.98      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
% 4.07/0.98      inference(cnf_transformation,[],[f31]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_79,negated_conjecture,
% 4.07/0.98      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
% 4.07/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_219,plain,
% 4.07/0.98      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_79]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1,plain,
% 4.07/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 4.07/0.98      inference(cnf_transformation,[],[f22]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_86,plain,
% 4.07/0.98      ( ~ r1_tarski(X0_38,X1_38)
% 4.07/0.98      | ~ r1_tarski(X1_38,X2_38)
% 4.07/0.98      | r1_tarski(X0_38,X2_38) ),
% 4.07/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_214,plain,
% 4.07/0.98      ( r1_tarski(X0_38,X1_38) != iProver_top
% 4.07/0.98      | r1_tarski(X1_38,X2_38) != iProver_top
% 4.07/0.98      | r1_tarski(X0_38,X2_38) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_86]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_539,plain,
% 4.07/0.98      ( r1_tarski(k2_zfmisc_1(sK2,sK3),X0_38) != iProver_top
% 4.07/0.98      | r1_tarski(sK0,X0_38) = iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_219,c_214]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_905,plain,
% 4.07/0.98      ( r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0_38)),sK3)) = iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_760,c_539]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1248,plain,
% 4.07/0.98      ( r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0_38)),sK3),X1_38) != iProver_top
% 4.07/0.98      | r1_tarski(sK0,X1_38) = iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_905,c_214]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_2244,plain,
% 4.07/0.98      ( r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0_38)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X1_38)))) = iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_770,c_1248]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_771,plain,
% 4.07/0.98      ( r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38)) != iProver_top
% 4.07/0.98      | r1_tarski(X0_38,k2_zfmisc_1(X1_38,k3_tarski(k3_enumset1(X3_38,X3_38,X3_38,X3_38,X2_38)))) = iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_83,c_213]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_3,plain,
% 4.07/0.98      ( ~ r1_tarski(X0,X1)
% 4.07/0.98      | ~ r1_tarski(X2,X1)
% 4.07/0.98      | r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) ),
% 4.07/0.98      inference(cnf_transformation,[],[f39]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_84,plain,
% 4.07/0.98      ( ~ r1_tarski(X0_38,X1_38)
% 4.07/0.98      | ~ r1_tarski(X2_38,X1_38)
% 4.07/0.98      | r1_tarski(k3_tarski(k3_enumset1(X0_38,X0_38,X0_38,X0_38,X2_38)),X1_38) ),
% 4.07/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_216,plain,
% 4.07/0.98      ( r1_tarski(X0_38,X1_38) != iProver_top
% 4.07/0.98      | r1_tarski(X2_38,X1_38) != iProver_top
% 4.07/0.98      | r1_tarski(k3_tarski(k3_enumset1(X0_38,X0_38,X0_38,X0_38,X2_38)),X1_38) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_84]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_6,negated_conjecture,
% 4.07/0.98      ( ~ r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
% 4.07/0.98      inference(cnf_transformation,[],[f42]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_81,negated_conjecture,
% 4.07/0.98      ( ~ r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
% 4.07/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_217,plain,
% 4.07/0.98      ( r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_81]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1686,plain,
% 4.07/0.98      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top
% 4.07/0.98      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_216,c_217]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_2745,plain,
% 4.07/0.98      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),sK5)) != iProver_top
% 4.07/0.98      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_771,c_1686]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_11244,plain,
% 4.07/0.98      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),sK5)) != iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_2244,c_2745]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_11254,plain,
% 4.07/0.98      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_761,c_11244]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_7,negated_conjecture,
% 4.07/0.98      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
% 4.07/0.98      inference(cnf_transformation,[],[f32]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_10,plain,
% 4.07/0.98      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(contradiction,plain,
% 4.07/0.98      ( $false ),
% 4.07/0.98      inference(minisat,[status(thm)],[c_11254,c_10]) ).
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  ------                               Statistics
% 4.07/0.98  
% 4.07/0.98  ------ General
% 4.07/0.98  
% 4.07/0.98  abstr_ref_over_cycles:                  0
% 4.07/0.98  abstr_ref_under_cycles:                 0
% 4.07/0.98  gc_basic_clause_elim:                   0
% 4.07/0.98  forced_gc_time:                         0
% 4.07/0.98  parsing_time:                           0.007
% 4.07/0.98  unif_index_cands_time:                  0.
% 4.07/0.98  unif_index_add_time:                    0.
% 4.07/0.98  orderings_time:                         0.
% 4.07/0.98  out_proof_time:                         0.008
% 4.07/0.98  total_time:                             0.491
% 4.07/0.98  num_of_symbols:                         43
% 4.07/0.98  num_of_terms:                           18083
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing
% 4.07/0.98  
% 4.07/0.98  num_of_splits:                          0
% 4.07/0.98  num_of_split_atoms:                     0
% 4.07/0.98  num_of_reused_defs:                     0
% 4.07/0.98  num_eq_ax_congr_red:                    0
% 4.07/0.98  num_of_sem_filtered_clauses:            1
% 4.07/0.98  num_of_subtypes:                        2
% 4.07/0.98  monotx_restored_types:                  0
% 4.07/0.98  sat_num_of_epr_types:                   0
% 4.07/0.98  sat_num_of_non_cyclic_types:            0
% 4.07/0.98  sat_guarded_non_collapsed_types:        0
% 4.07/0.98  num_pure_diseq_elim:                    0
% 4.07/0.98  simp_replaced_by:                       0
% 4.07/0.98  res_preprocessed:                       42
% 4.07/0.98  prep_upred:                             0
% 4.07/0.98  prep_unflattend:                        0
% 4.07/0.98  smt_new_axioms:                         0
% 4.07/0.98  pred_elim_cands:                        1
% 4.07/0.98  pred_elim:                              0
% 4.07/0.98  pred_elim_cl:                           0
% 4.07/0.98  pred_elim_cycles:                       1
% 4.07/0.98  merged_defs:                            0
% 4.07/0.98  merged_defs_ncl:                        0
% 4.07/0.98  bin_hyper_res:                          0
% 4.07/0.98  prep_cycles:                            3
% 4.07/0.98  pred_elim_time:                         0.
% 4.07/0.98  splitting_time:                         0.
% 4.07/0.98  sem_filter_time:                        0.
% 4.07/0.98  monotx_time:                            0.
% 4.07/0.98  subtype_inf_time:                       0.
% 4.07/0.98  
% 4.07/0.98  ------ Problem properties
% 4.07/0.98  
% 4.07/0.98  clauses:                                9
% 4.07/0.98  conjectures:                            3
% 4.07/0.98  epr:                                    1
% 4.07/0.98  horn:                                   9
% 4.07/0.98  ground:                                 3
% 4.07/0.98  unary:                                  6
% 4.07/0.98  binary:                                 1
% 4.07/0.98  lits:                                   14
% 4.07/0.98  lits_eq:                                2
% 4.07/0.98  fd_pure:                                0
% 4.07/0.98  fd_pseudo:                              0
% 4.07/0.98  fd_cond:                                0
% 4.07/0.98  fd_pseudo_cond:                         0
% 4.07/0.98  ac_symbols:                             0
% 4.07/0.98  
% 4.07/0.98  ------ Propositional Solver
% 4.07/0.98  
% 4.07/0.98  prop_solver_calls:                      26
% 4.07/0.98  prop_fast_solver_calls:                 326
% 4.07/0.98  smt_solver_calls:                       0
% 4.07/0.98  smt_fast_solver_calls:                  0
% 4.07/0.98  prop_num_of_clauses:                    6659
% 4.07/0.98  prop_preprocess_simplified:             7752
% 4.07/0.98  prop_fo_subsumed:                       8
% 4.07/0.98  prop_solver_time:                       0.
% 4.07/0.98  smt_solver_time:                        0.
% 4.07/0.98  smt_fast_solver_time:                   0.
% 4.07/0.98  prop_fast_solver_time:                  0.
% 4.07/0.98  prop_unsat_core_time:                   0.
% 4.07/0.98  
% 4.07/0.98  ------ QBF
% 4.07/0.98  
% 4.07/0.98  qbf_q_res:                              0
% 4.07/0.98  qbf_num_tautologies:                    0
% 4.07/0.98  qbf_prep_cycles:                        0
% 4.07/0.98  
% 4.07/0.98  ------ BMC1
% 4.07/0.98  
% 4.07/0.98  bmc1_current_bound:                     -1
% 4.07/0.98  bmc1_last_solved_bound:                 -1
% 4.07/0.98  bmc1_unsat_core_size:                   -1
% 4.07/0.98  bmc1_unsat_core_parents_size:           -1
% 4.07/0.98  bmc1_merge_next_fun:                    0
% 4.07/0.98  bmc1_unsat_core_clauses_time:           0.
% 4.07/0.98  
% 4.07/0.98  ------ Instantiation
% 4.07/0.98  
% 4.07/0.98  inst_num_of_clauses:                    947
% 4.07/0.98  inst_num_in_passive:                    362
% 4.07/0.98  inst_num_in_active:                     414
% 4.07/0.98  inst_num_in_unprocessed:                171
% 4.07/0.98  inst_num_of_loops:                      440
% 4.07/0.98  inst_num_of_learning_restarts:          0
% 4.07/0.98  inst_num_moves_active_passive:          24
% 4.07/0.98  inst_lit_activity:                      0
% 4.07/0.98  inst_lit_activity_moves:                0
% 4.07/0.98  inst_num_tautologies:                   0
% 4.07/0.98  inst_num_prop_implied:                  0
% 4.07/0.98  inst_num_existing_simplified:           0
% 4.07/0.98  inst_num_eq_res_simplified:             0
% 4.07/0.98  inst_num_child_elim:                    0
% 4.07/0.98  inst_num_of_dismatching_blockings:      1126
% 4.07/0.98  inst_num_of_non_proper_insts:           1018
% 4.07/0.98  inst_num_of_duplicates:                 0
% 4.07/0.98  inst_inst_num_from_inst_to_res:         0
% 4.07/0.98  inst_dismatching_checking_time:         0.
% 4.07/0.98  
% 4.07/0.98  ------ Resolution
% 4.07/0.98  
% 4.07/0.98  res_num_of_clauses:                     0
% 4.07/0.98  res_num_in_passive:                     0
% 4.07/0.98  res_num_in_active:                      0
% 4.07/0.98  res_num_of_loops:                       45
% 4.07/0.98  res_forward_subset_subsumed:            116
% 4.07/0.98  res_backward_subset_subsumed:           0
% 4.07/0.98  res_forward_subsumed:                   0
% 4.07/0.98  res_backward_subsumed:                  0
% 4.07/0.98  res_forward_subsumption_resolution:     0
% 4.07/0.98  res_backward_subsumption_resolution:    0
% 4.07/0.98  res_clause_to_clause_subsumption:       8163
% 4.07/0.98  res_orphan_elimination:                 0
% 4.07/0.98  res_tautology_del:                      40
% 4.07/0.98  res_num_eq_res_simplified:              0
% 4.07/0.98  res_num_sel_changes:                    0
% 4.07/0.98  res_moves_from_active_to_pass:          0
% 4.07/0.98  
% 4.07/0.98  ------ Superposition
% 4.07/0.98  
% 4.07/0.98  sup_time_total:                         0.
% 4.07/0.98  sup_time_generating:                    0.
% 4.07/0.98  sup_time_sim_full:                      0.
% 4.07/0.98  sup_time_sim_immed:                     0.
% 4.07/0.98  
% 4.07/0.98  sup_num_of_clauses:                     1036
% 4.07/0.98  sup_num_in_active:                      76
% 4.07/0.98  sup_num_in_passive:                     960
% 4.07/0.98  sup_num_of_loops:                       87
% 4.07/0.98  sup_fw_superposition:                   843
% 4.07/0.98  sup_bw_superposition:                   794
% 4.07/0.98  sup_immediate_simplified:               262
% 4.07/0.98  sup_given_eliminated:                   0
% 4.07/0.98  comparisons_done:                       0
% 4.07/0.98  comparisons_avoided:                    0
% 4.07/0.98  
% 4.07/0.98  ------ Simplifications
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  sim_fw_subset_subsumed:                 4
% 4.07/0.98  sim_bw_subset_subsumed:                 8
% 4.07/0.98  sim_fw_subsumed:                        27
% 4.07/0.98  sim_bw_subsumed:                        8
% 4.07/0.98  sim_fw_subsumption_res:                 0
% 4.07/0.98  sim_bw_subsumption_res:                 0
% 4.07/0.98  sim_tautology_del:                      1
% 4.07/0.98  sim_eq_tautology_del:                   6
% 4.07/0.98  sim_eq_res_simp:                        0
% 4.07/0.98  sim_fw_demodulated:                     256
% 4.07/0.98  sim_bw_demodulated:                     0
% 4.07/0.98  sim_light_normalised:                   0
% 4.07/0.98  sim_joinable_taut:                      0
% 4.07/0.98  sim_joinable_simp:                      0
% 4.07/0.98  sim_ac_normalised:                      0
% 4.07/0.98  sim_smt_subsumption:                    0
% 4.07/0.98  
%------------------------------------------------------------------------------
