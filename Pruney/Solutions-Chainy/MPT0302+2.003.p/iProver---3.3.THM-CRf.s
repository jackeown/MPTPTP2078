%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:03 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 275 expanded)
%              Number of clauses        :   56 (  99 expanded)
%              Number of leaves         :   14 (  60 expanded)
%              Depth                    :   22
%              Number of atoms          :  215 ( 797 expanded)
%              Number of equality atoms :  132 ( 460 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f34])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f38])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f24,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f25,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f24])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK3 != sK4
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK4,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( sK3 != sK4
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK4,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f40])).

fof(f68,plain,(
    k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f42,f61,f61])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f61])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f71,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_973,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_967,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_28,negated_conjecture,
    ( k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_24,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_965,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1383,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_965])).

cnf(c_4485,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_1383])).

cnf(c_5227,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_973,c_4485])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_482,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_495,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_483,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1145,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_1146,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_6011,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5227,c_26,c_495,c_1146])).

cnf(c_6020,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK2(sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_973,c_6011])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1147,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_1148,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_6672,plain,
    ( r2_hidden(sK2(sK3),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6020,c_27,c_495,c_1148])).

cnf(c_23,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_966,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2395,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_966])).

cnf(c_4486,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_2395])).

cnf(c_6677,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK2(sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6672,c_4486])).

cnf(c_1138,plain,
    ( r2_hidden(sK2(sK3),sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1139,plain,
    ( k1_xboole_0 = sK3
    | r2_hidden(sK2(sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1138])).

cnf(c_7109,plain,
    ( r2_hidden(sK2(sK3),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6677,c_27,c_1139])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_983,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5250,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK0(sK4,X1),sK3) = iProver_top
    | r1_tarski(sK4,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_983,c_4486])).

cnf(c_7114,plain,
    ( r2_hidden(sK0(sK4,X0),sK3) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7109,c_5250])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_984,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7236,plain,
    ( r1_tarski(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7114,c_984])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_972,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7830,plain,
    ( k4_xboole_0(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7236,c_972])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_8310,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7830,c_1])).

cnf(c_6019,plain,
    ( r2_hidden(sK0(sK3,X0),sK4) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_983,c_6011])).

cnf(c_7220,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6019,c_984])).

cnf(c_7538,plain,
    ( k4_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7220,c_972])).

cnf(c_8316,plain,
    ( k4_xboole_0(sK4,k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_8310,c_7538])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_18,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_970,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1213,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_970])).

cnf(c_3496,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1213,c_972])).

cnf(c_3519,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_3496,c_7])).

cnf(c_8317,plain,
    ( sK4 = sK3 ),
    inference(demodulation,[status(thm)],[c_8316,c_3519])).

cnf(c_25,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_10019,plain,
    ( sK3 != sK3 ),
    inference(demodulation,[status(thm)],[c_8317,c_25])).

cnf(c_10020,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_10019])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:03:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.97/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/0.99  
% 2.97/0.99  ------  iProver source info
% 2.97/0.99  
% 2.97/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.97/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/0.99  git: non_committed_changes: false
% 2.97/0.99  git: last_make_outside_of_git: false
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options
% 2.97/0.99  
% 2.97/0.99  --out_options                           all
% 2.97/0.99  --tptp_safe_out                         true
% 2.97/0.99  --problem_path                          ""
% 2.97/0.99  --include_path                          ""
% 2.97/0.99  --clausifier                            res/vclausify_rel
% 2.97/0.99  --clausifier_options                    --mode clausify
% 2.97/0.99  --stdin                                 false
% 2.97/0.99  --stats_out                             all
% 2.97/0.99  
% 2.97/0.99  ------ General Options
% 2.97/0.99  
% 2.97/0.99  --fof                                   false
% 2.97/0.99  --time_out_real                         305.
% 2.97/0.99  --time_out_virtual                      -1.
% 2.97/0.99  --symbol_type_check                     false
% 2.97/0.99  --clausify_out                          false
% 2.97/0.99  --sig_cnt_out                           false
% 2.97/0.99  --trig_cnt_out                          false
% 2.97/0.99  --trig_cnt_out_tolerance                1.
% 2.97/0.99  --trig_cnt_out_sk_spl                   false
% 2.97/0.99  --abstr_cl_out                          false
% 2.97/0.99  
% 2.97/0.99  ------ Global Options
% 2.97/0.99  
% 2.97/0.99  --schedule                              default
% 2.97/0.99  --add_important_lit                     false
% 2.97/0.99  --prop_solver_per_cl                    1000
% 2.97/0.99  --min_unsat_core                        false
% 2.97/0.99  --soft_assumptions                      false
% 2.97/0.99  --soft_lemma_size                       3
% 2.97/0.99  --prop_impl_unit_size                   0
% 2.97/0.99  --prop_impl_unit                        []
% 2.97/0.99  --share_sel_clauses                     true
% 2.97/0.99  --reset_solvers                         false
% 2.97/0.99  --bc_imp_inh                            [conj_cone]
% 2.97/0.99  --conj_cone_tolerance                   3.
% 2.97/0.99  --extra_neg_conj                        none
% 2.97/0.99  --large_theory_mode                     true
% 2.97/0.99  --prolific_symb_bound                   200
% 2.97/0.99  --lt_threshold                          2000
% 2.97/0.99  --clause_weak_htbl                      true
% 2.97/0.99  --gc_record_bc_elim                     false
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing Options
% 2.97/0.99  
% 2.97/0.99  --preprocessing_flag                    true
% 2.97/0.99  --time_out_prep_mult                    0.1
% 2.97/0.99  --splitting_mode                        input
% 2.97/0.99  --splitting_grd                         true
% 2.97/0.99  --splitting_cvd                         false
% 2.97/0.99  --splitting_cvd_svl                     false
% 2.97/0.99  --splitting_nvd                         32
% 2.97/0.99  --sub_typing                            true
% 2.97/0.99  --prep_gs_sim                           true
% 2.97/0.99  --prep_unflatten                        true
% 2.97/0.99  --prep_res_sim                          true
% 2.97/0.99  --prep_upred                            true
% 2.97/0.99  --prep_sem_filter                       exhaustive
% 2.97/0.99  --prep_sem_filter_out                   false
% 2.97/0.99  --pred_elim                             true
% 2.97/0.99  --res_sim_input                         true
% 2.97/0.99  --eq_ax_congr_red                       true
% 2.97/0.99  --pure_diseq_elim                       true
% 2.97/0.99  --brand_transform                       false
% 2.97/0.99  --non_eq_to_eq                          false
% 2.97/0.99  --prep_def_merge                        true
% 2.97/0.99  --prep_def_merge_prop_impl              false
% 2.97/0.99  --prep_def_merge_mbd                    true
% 2.97/0.99  --prep_def_merge_tr_red                 false
% 2.97/0.99  --prep_def_merge_tr_cl                  false
% 2.97/0.99  --smt_preprocessing                     true
% 2.97/0.99  --smt_ac_axioms                         fast
% 2.97/0.99  --preprocessed_out                      false
% 2.97/0.99  --preprocessed_stats                    false
% 2.97/0.99  
% 2.97/0.99  ------ Abstraction refinement Options
% 2.97/0.99  
% 2.97/0.99  --abstr_ref                             []
% 2.97/0.99  --abstr_ref_prep                        false
% 2.97/0.99  --abstr_ref_until_sat                   false
% 2.97/0.99  --abstr_ref_sig_restrict                funpre
% 2.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.99  --abstr_ref_under                       []
% 2.97/0.99  
% 2.97/0.99  ------ SAT Options
% 2.97/0.99  
% 2.97/0.99  --sat_mode                              false
% 2.97/0.99  --sat_fm_restart_options                ""
% 2.97/0.99  --sat_gr_def                            false
% 2.97/0.99  --sat_epr_types                         true
% 2.97/0.99  --sat_non_cyclic_types                  false
% 2.97/0.99  --sat_finite_models                     false
% 2.97/0.99  --sat_fm_lemmas                         false
% 2.97/0.99  --sat_fm_prep                           false
% 2.97/0.99  --sat_fm_uc_incr                        true
% 2.97/0.99  --sat_out_model                         small
% 2.97/0.99  --sat_out_clauses                       false
% 2.97/0.99  
% 2.97/0.99  ------ QBF Options
% 2.97/0.99  
% 2.97/0.99  --qbf_mode                              false
% 2.97/0.99  --qbf_elim_univ                         false
% 2.97/0.99  --qbf_dom_inst                          none
% 2.97/0.99  --qbf_dom_pre_inst                      false
% 2.97/0.99  --qbf_sk_in                             false
% 2.97/0.99  --qbf_pred_elim                         true
% 2.97/0.99  --qbf_split                             512
% 2.97/0.99  
% 2.97/0.99  ------ BMC1 Options
% 2.97/0.99  
% 2.97/0.99  --bmc1_incremental                      false
% 2.97/0.99  --bmc1_axioms                           reachable_all
% 2.97/0.99  --bmc1_min_bound                        0
% 2.97/0.99  --bmc1_max_bound                        -1
% 2.97/0.99  --bmc1_max_bound_default                -1
% 2.97/0.99  --bmc1_symbol_reachability              true
% 2.97/0.99  --bmc1_property_lemmas                  false
% 2.97/0.99  --bmc1_k_induction                      false
% 2.97/0.99  --bmc1_non_equiv_states                 false
% 2.97/0.99  --bmc1_deadlock                         false
% 2.97/0.99  --bmc1_ucm                              false
% 2.97/0.99  --bmc1_add_unsat_core                   none
% 2.97/0.99  --bmc1_unsat_core_children              false
% 2.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.99  --bmc1_out_stat                         full
% 2.97/0.99  --bmc1_ground_init                      false
% 2.97/0.99  --bmc1_pre_inst_next_state              false
% 2.97/0.99  --bmc1_pre_inst_state                   false
% 2.97/0.99  --bmc1_pre_inst_reach_state             false
% 2.97/0.99  --bmc1_out_unsat_core                   false
% 2.97/0.99  --bmc1_aig_witness_out                  false
% 2.97/0.99  --bmc1_verbose                          false
% 2.97/0.99  --bmc1_dump_clauses_tptp                false
% 2.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.99  --bmc1_dump_file                        -
% 2.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.99  --bmc1_ucm_extend_mode                  1
% 2.97/0.99  --bmc1_ucm_init_mode                    2
% 2.97/0.99  --bmc1_ucm_cone_mode                    none
% 2.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.99  --bmc1_ucm_relax_model                  4
% 2.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.99  --bmc1_ucm_layered_model                none
% 2.97/0.99  --bmc1_ucm_max_lemma_size               10
% 2.97/0.99  
% 2.97/0.99  ------ AIG Options
% 2.97/0.99  
% 2.97/0.99  --aig_mode                              false
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation Options
% 2.97/0.99  
% 2.97/0.99  --instantiation_flag                    true
% 2.97/0.99  --inst_sos_flag                         false
% 2.97/0.99  --inst_sos_phase                        true
% 2.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel_side                     num_symb
% 2.97/0.99  --inst_solver_per_active                1400
% 2.97/0.99  --inst_solver_calls_frac                1.
% 2.97/0.99  --inst_passive_queue_type               priority_queues
% 2.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.99  --inst_passive_queues_freq              [25;2]
% 2.97/0.99  --inst_dismatching                      true
% 2.97/0.99  --inst_eager_unprocessed_to_passive     true
% 2.97/0.99  --inst_prop_sim_given                   true
% 2.97/0.99  --inst_prop_sim_new                     false
% 2.97/0.99  --inst_subs_new                         false
% 2.97/0.99  --inst_eq_res_simp                      false
% 2.97/0.99  --inst_subs_given                       false
% 2.97/0.99  --inst_orphan_elimination               true
% 2.97/0.99  --inst_learning_loop_flag               true
% 2.97/0.99  --inst_learning_start                   3000
% 2.97/0.99  --inst_learning_factor                  2
% 2.97/0.99  --inst_start_prop_sim_after_learn       3
% 2.97/0.99  --inst_sel_renew                        solver
% 2.97/0.99  --inst_lit_activity_flag                true
% 2.97/0.99  --inst_restr_to_given                   false
% 2.97/0.99  --inst_activity_threshold               500
% 2.97/0.99  --inst_out_proof                        true
% 2.97/0.99  
% 2.97/0.99  ------ Resolution Options
% 2.97/0.99  
% 2.97/0.99  --resolution_flag                       true
% 2.97/0.99  --res_lit_sel                           adaptive
% 2.97/0.99  --res_lit_sel_side                      none
% 2.97/0.99  --res_ordering                          kbo
% 2.97/0.99  --res_to_prop_solver                    active
% 2.97/0.99  --res_prop_simpl_new                    false
% 2.97/0.99  --res_prop_simpl_given                  true
% 2.97/0.99  --res_passive_queue_type                priority_queues
% 2.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.99  --res_passive_queues_freq               [15;5]
% 2.97/0.99  --res_forward_subs                      full
% 2.97/0.99  --res_backward_subs                     full
% 2.97/0.99  --res_forward_subs_resolution           true
% 2.97/0.99  --res_backward_subs_resolution          true
% 2.97/0.99  --res_orphan_elimination                true
% 2.97/0.99  --res_time_limit                        2.
% 2.97/0.99  --res_out_proof                         true
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Options
% 2.97/0.99  
% 2.97/0.99  --superposition_flag                    true
% 2.97/0.99  --sup_passive_queue_type                priority_queues
% 2.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.99  --demod_completeness_check              fast
% 2.97/0.99  --demod_use_ground                      true
% 2.97/0.99  --sup_to_prop_solver                    passive
% 2.97/0.99  --sup_prop_simpl_new                    true
% 2.97/0.99  --sup_prop_simpl_given                  true
% 2.97/0.99  --sup_fun_splitting                     false
% 2.97/0.99  --sup_smt_interval                      50000
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Simplification Setup
% 2.97/0.99  
% 2.97/0.99  --sup_indices_passive                   []
% 2.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_full_bw                           [BwDemod]
% 2.97/0.99  --sup_immed_triv                        [TrivRules]
% 2.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_immed_bw_main                     []
% 2.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  
% 2.97/0.99  ------ Combination Options
% 2.97/0.99  
% 2.97/0.99  --comb_res_mult                         3
% 2.97/0.99  --comb_sup_mult                         2
% 2.97/0.99  --comb_inst_mult                        10
% 2.97/0.99  
% 2.97/0.99  ------ Debug Options
% 2.97/0.99  
% 2.97/0.99  --dbg_backtrace                         false
% 2.97/0.99  --dbg_dump_prop_clauses                 false
% 2.97/0.99  --dbg_dump_prop_clauses_file            -
% 2.97/0.99  --dbg_out_stat                          false
% 2.97/0.99  ------ Parsing...
% 2.97/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/0.99  ------ Proving...
% 2.97/0.99  ------ Problem Properties 
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  clauses                                 29
% 2.97/0.99  conjectures                             4
% 2.97/0.99  EPR                                     4
% 2.97/0.99  Horn                                    23
% 2.97/0.99  unary                                   10
% 2.97/0.99  binary                                  13
% 2.97/0.99  lits                                    54
% 2.97/0.99  lits eq                                 16
% 2.97/0.99  fd_pure                                 0
% 2.97/0.99  fd_pseudo                               0
% 2.97/0.99  fd_cond                                 1
% 2.97/0.99  fd_pseudo_cond                          0
% 2.97/0.99  AC symbols                              0
% 2.97/0.99  
% 2.97/0.99  ------ Schedule dynamic 5 is on 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ 
% 2.97/0.99  Current options:
% 2.97/0.99  ------ 
% 2.97/0.99  
% 2.97/0.99  ------ Input Options
% 2.97/0.99  
% 2.97/0.99  --out_options                           all
% 2.97/0.99  --tptp_safe_out                         true
% 2.97/0.99  --problem_path                          ""
% 2.97/0.99  --include_path                          ""
% 2.97/0.99  --clausifier                            res/vclausify_rel
% 2.97/0.99  --clausifier_options                    --mode clausify
% 2.97/0.99  --stdin                                 false
% 2.97/0.99  --stats_out                             all
% 2.97/0.99  
% 2.97/0.99  ------ General Options
% 2.97/0.99  
% 2.97/0.99  --fof                                   false
% 2.97/0.99  --time_out_real                         305.
% 2.97/0.99  --time_out_virtual                      -1.
% 2.97/0.99  --symbol_type_check                     false
% 2.97/0.99  --clausify_out                          false
% 2.97/0.99  --sig_cnt_out                           false
% 2.97/0.99  --trig_cnt_out                          false
% 2.97/0.99  --trig_cnt_out_tolerance                1.
% 2.97/0.99  --trig_cnt_out_sk_spl                   false
% 2.97/0.99  --abstr_cl_out                          false
% 2.97/0.99  
% 2.97/0.99  ------ Global Options
% 2.97/0.99  
% 2.97/0.99  --schedule                              default
% 2.97/0.99  --add_important_lit                     false
% 2.97/0.99  --prop_solver_per_cl                    1000
% 2.97/0.99  --min_unsat_core                        false
% 2.97/0.99  --soft_assumptions                      false
% 2.97/0.99  --soft_lemma_size                       3
% 2.97/0.99  --prop_impl_unit_size                   0
% 2.97/0.99  --prop_impl_unit                        []
% 2.97/0.99  --share_sel_clauses                     true
% 2.97/0.99  --reset_solvers                         false
% 2.97/0.99  --bc_imp_inh                            [conj_cone]
% 2.97/0.99  --conj_cone_tolerance                   3.
% 2.97/0.99  --extra_neg_conj                        none
% 2.97/0.99  --large_theory_mode                     true
% 2.97/0.99  --prolific_symb_bound                   200
% 2.97/0.99  --lt_threshold                          2000
% 2.97/0.99  --clause_weak_htbl                      true
% 2.97/0.99  --gc_record_bc_elim                     false
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing Options
% 2.97/0.99  
% 2.97/0.99  --preprocessing_flag                    true
% 2.97/0.99  --time_out_prep_mult                    0.1
% 2.97/0.99  --splitting_mode                        input
% 2.97/0.99  --splitting_grd                         true
% 2.97/0.99  --splitting_cvd                         false
% 2.97/0.99  --splitting_cvd_svl                     false
% 2.97/0.99  --splitting_nvd                         32
% 2.97/0.99  --sub_typing                            true
% 2.97/0.99  --prep_gs_sim                           true
% 2.97/0.99  --prep_unflatten                        true
% 2.97/0.99  --prep_res_sim                          true
% 2.97/0.99  --prep_upred                            true
% 2.97/0.99  --prep_sem_filter                       exhaustive
% 2.97/0.99  --prep_sem_filter_out                   false
% 2.97/0.99  --pred_elim                             true
% 2.97/0.99  --res_sim_input                         true
% 2.97/0.99  --eq_ax_congr_red                       true
% 2.97/0.99  --pure_diseq_elim                       true
% 2.97/0.99  --brand_transform                       false
% 2.97/0.99  --non_eq_to_eq                          false
% 2.97/0.99  --prep_def_merge                        true
% 2.97/0.99  --prep_def_merge_prop_impl              false
% 2.97/0.99  --prep_def_merge_mbd                    true
% 2.97/0.99  --prep_def_merge_tr_red                 false
% 2.97/0.99  --prep_def_merge_tr_cl                  false
% 2.97/0.99  --smt_preprocessing                     true
% 2.97/0.99  --smt_ac_axioms                         fast
% 2.97/0.99  --preprocessed_out                      false
% 2.97/0.99  --preprocessed_stats                    false
% 2.97/0.99  
% 2.97/0.99  ------ Abstraction refinement Options
% 2.97/0.99  
% 2.97/0.99  --abstr_ref                             []
% 2.97/0.99  --abstr_ref_prep                        false
% 2.97/0.99  --abstr_ref_until_sat                   false
% 2.97/0.99  --abstr_ref_sig_restrict                funpre
% 2.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.99  --abstr_ref_under                       []
% 2.97/0.99  
% 2.97/0.99  ------ SAT Options
% 2.97/0.99  
% 2.97/0.99  --sat_mode                              false
% 2.97/0.99  --sat_fm_restart_options                ""
% 2.97/0.99  --sat_gr_def                            false
% 2.97/0.99  --sat_epr_types                         true
% 2.97/0.99  --sat_non_cyclic_types                  false
% 2.97/0.99  --sat_finite_models                     false
% 2.97/0.99  --sat_fm_lemmas                         false
% 2.97/0.99  --sat_fm_prep                           false
% 2.97/0.99  --sat_fm_uc_incr                        true
% 2.97/0.99  --sat_out_model                         small
% 2.97/0.99  --sat_out_clauses                       false
% 2.97/0.99  
% 2.97/0.99  ------ QBF Options
% 2.97/0.99  
% 2.97/0.99  --qbf_mode                              false
% 2.97/0.99  --qbf_elim_univ                         false
% 2.97/0.99  --qbf_dom_inst                          none
% 2.97/0.99  --qbf_dom_pre_inst                      false
% 2.97/0.99  --qbf_sk_in                             false
% 2.97/0.99  --qbf_pred_elim                         true
% 2.97/0.99  --qbf_split                             512
% 2.97/0.99  
% 2.97/0.99  ------ BMC1 Options
% 2.97/0.99  
% 2.97/0.99  --bmc1_incremental                      false
% 2.97/0.99  --bmc1_axioms                           reachable_all
% 2.97/0.99  --bmc1_min_bound                        0
% 2.97/0.99  --bmc1_max_bound                        -1
% 2.97/0.99  --bmc1_max_bound_default                -1
% 2.97/0.99  --bmc1_symbol_reachability              true
% 2.97/0.99  --bmc1_property_lemmas                  false
% 2.97/0.99  --bmc1_k_induction                      false
% 2.97/0.99  --bmc1_non_equiv_states                 false
% 2.97/0.99  --bmc1_deadlock                         false
% 2.97/0.99  --bmc1_ucm                              false
% 2.97/0.99  --bmc1_add_unsat_core                   none
% 2.97/0.99  --bmc1_unsat_core_children              false
% 2.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.99  --bmc1_out_stat                         full
% 2.97/0.99  --bmc1_ground_init                      false
% 2.97/0.99  --bmc1_pre_inst_next_state              false
% 2.97/0.99  --bmc1_pre_inst_state                   false
% 2.97/0.99  --bmc1_pre_inst_reach_state             false
% 2.97/0.99  --bmc1_out_unsat_core                   false
% 2.97/0.99  --bmc1_aig_witness_out                  false
% 2.97/0.99  --bmc1_verbose                          false
% 2.97/0.99  --bmc1_dump_clauses_tptp                false
% 2.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.99  --bmc1_dump_file                        -
% 2.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.99  --bmc1_ucm_extend_mode                  1
% 2.97/0.99  --bmc1_ucm_init_mode                    2
% 2.97/0.99  --bmc1_ucm_cone_mode                    none
% 2.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.99  --bmc1_ucm_relax_model                  4
% 2.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.99  --bmc1_ucm_layered_model                none
% 2.97/0.99  --bmc1_ucm_max_lemma_size               10
% 2.97/0.99  
% 2.97/0.99  ------ AIG Options
% 2.97/0.99  
% 2.97/0.99  --aig_mode                              false
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation Options
% 2.97/0.99  
% 2.97/0.99  --instantiation_flag                    true
% 2.97/0.99  --inst_sos_flag                         false
% 2.97/0.99  --inst_sos_phase                        true
% 2.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.99  --inst_lit_sel_side                     none
% 2.97/0.99  --inst_solver_per_active                1400
% 2.97/0.99  --inst_solver_calls_frac                1.
% 2.97/0.99  --inst_passive_queue_type               priority_queues
% 2.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.99  --inst_passive_queues_freq              [25;2]
% 2.97/0.99  --inst_dismatching                      true
% 2.97/0.99  --inst_eager_unprocessed_to_passive     true
% 2.97/0.99  --inst_prop_sim_given                   true
% 2.97/0.99  --inst_prop_sim_new                     false
% 2.97/0.99  --inst_subs_new                         false
% 2.97/0.99  --inst_eq_res_simp                      false
% 2.97/0.99  --inst_subs_given                       false
% 2.97/0.99  --inst_orphan_elimination               true
% 2.97/0.99  --inst_learning_loop_flag               true
% 2.97/0.99  --inst_learning_start                   3000
% 2.97/0.99  --inst_learning_factor                  2
% 2.97/0.99  --inst_start_prop_sim_after_learn       3
% 2.97/0.99  --inst_sel_renew                        solver
% 2.97/0.99  --inst_lit_activity_flag                true
% 2.97/0.99  --inst_restr_to_given                   false
% 2.97/0.99  --inst_activity_threshold               500
% 2.97/0.99  --inst_out_proof                        true
% 2.97/0.99  
% 2.97/0.99  ------ Resolution Options
% 2.97/0.99  
% 2.97/0.99  --resolution_flag                       false
% 2.97/0.99  --res_lit_sel                           adaptive
% 2.97/0.99  --res_lit_sel_side                      none
% 2.97/0.99  --res_ordering                          kbo
% 2.97/0.99  --res_to_prop_solver                    active
% 2.97/0.99  --res_prop_simpl_new                    false
% 2.97/0.99  --res_prop_simpl_given                  true
% 2.97/0.99  --res_passive_queue_type                priority_queues
% 2.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.99  --res_passive_queues_freq               [15;5]
% 2.97/0.99  --res_forward_subs                      full
% 2.97/0.99  --res_backward_subs                     full
% 2.97/0.99  --res_forward_subs_resolution           true
% 2.97/0.99  --res_backward_subs_resolution          true
% 2.97/0.99  --res_orphan_elimination                true
% 2.97/0.99  --res_time_limit                        2.
% 2.97/0.99  --res_out_proof                         true
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Options
% 2.97/0.99  
% 2.97/0.99  --superposition_flag                    true
% 2.97/0.99  --sup_passive_queue_type                priority_queues
% 2.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.99  --demod_completeness_check              fast
% 2.97/0.99  --demod_use_ground                      true
% 2.97/0.99  --sup_to_prop_solver                    passive
% 2.97/0.99  --sup_prop_simpl_new                    true
% 2.97/0.99  --sup_prop_simpl_given                  true
% 2.97/0.99  --sup_fun_splitting                     false
% 2.97/0.99  --sup_smt_interval                      50000
% 2.97/0.99  
% 2.97/0.99  ------ Superposition Simplification Setup
% 2.97/0.99  
% 2.97/0.99  --sup_indices_passive                   []
% 2.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_full_bw                           [BwDemod]
% 2.97/0.99  --sup_immed_triv                        [TrivRules]
% 2.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_immed_bw_main                     []
% 2.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.99  
% 2.97/0.99  ------ Combination Options
% 2.97/0.99  
% 2.97/0.99  --comb_res_mult                         3
% 2.97/0.99  --comb_sup_mult                         2
% 2.97/0.99  --comb_inst_mult                        10
% 2.97/0.99  
% 2.97/0.99  ------ Debug Options
% 2.97/0.99  
% 2.97/0.99  --dbg_backtrace                         false
% 2.97/0.99  --dbg_dump_prop_clauses                 false
% 2.97/0.99  --dbg_dump_prop_clauses_file            -
% 2.97/0.99  --dbg_out_stat                          false
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  ------ Proving...
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  % SZS status Theorem for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99   Resolution empty clause
% 2.97/0.99  
% 2.97/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  fof(f7,axiom,(
% 2.97/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f23,plain,(
% 2.97/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.97/0.99    inference(ennf_transformation,[],[f7])).
% 2.97/0.99  
% 2.97/0.99  fof(f34,plain,(
% 2.97/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f35,plain,(
% 2.97/0.99    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f34])).
% 2.97/0.99  
% 2.97/0.99  fof(f55,plain,(
% 2.97/0.99    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.97/0.99    inference(cnf_transformation,[],[f35])).
% 2.97/0.99  
% 2.97/0.99  fof(f15,axiom,(
% 2.97/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f38,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.97/0.99    inference(nnf_transformation,[],[f15])).
% 2.97/0.99  
% 2.97/0.99  fof(f39,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.97/0.99    inference(flattening,[],[f38])).
% 2.97/0.99  
% 2.97/0.99  fof(f67,plain,(
% 2.97/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f39])).
% 2.97/0.99  
% 2.97/0.99  fof(f16,conjecture,(
% 2.97/0.99    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f17,negated_conjecture,(
% 2.97/0.99    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.97/0.99    inference(negated_conjecture,[],[f16])).
% 2.97/0.99  
% 2.97/0.99  fof(f24,plain,(
% 2.97/0.99    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 2.97/0.99    inference(ennf_transformation,[],[f17])).
% 2.97/0.99  
% 2.97/0.99  fof(f25,plain,(
% 2.97/0.99    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 2.97/0.99    inference(flattening,[],[f24])).
% 2.97/0.99  
% 2.97/0.99  fof(f40,plain,(
% 2.97/0.99    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK3 != sK4 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK4,sK3))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f41,plain,(
% 2.97/0.99    sK3 != sK4 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK4,sK3)),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f40])).
% 2.97/0.99  
% 2.97/0.99  fof(f68,plain,(
% 2.97/0.99    k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK4,sK3)),
% 2.97/0.99    inference(cnf_transformation,[],[f41])).
% 2.97/0.99  
% 2.97/0.99  fof(f65,plain,(
% 2.97/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f39])).
% 2.97/0.99  
% 2.97/0.99  fof(f70,plain,(
% 2.97/0.99    k1_xboole_0 != sK4),
% 2.97/0.99    inference(cnf_transformation,[],[f41])).
% 2.97/0.99  
% 2.97/0.99  fof(f69,plain,(
% 2.97/0.99    k1_xboole_0 != sK3),
% 2.97/0.99    inference(cnf_transformation,[],[f41])).
% 2.97/0.99  
% 2.97/0.99  fof(f66,plain,(
% 2.97/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f39])).
% 2.97/0.99  
% 2.97/0.99  fof(f2,axiom,(
% 2.97/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f20,plain,(
% 2.97/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.97/0.99    inference(ennf_transformation,[],[f2])).
% 2.97/0.99  
% 2.97/0.99  fof(f26,plain,(
% 2.97/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.97/0.99    inference(nnf_transformation,[],[f20])).
% 2.97/0.99  
% 2.97/0.99  fof(f27,plain,(
% 2.97/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.97/0.99    inference(rectify,[],[f26])).
% 2.97/0.99  
% 2.97/0.99  fof(f28,plain,(
% 2.97/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f29,plain,(
% 2.97/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.97/0.99  
% 2.97/0.99  fof(f44,plain,(
% 2.97/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f29])).
% 2.97/0.99  
% 2.97/0.99  fof(f45,plain,(
% 2.97/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f29])).
% 2.97/0.99  
% 2.97/0.99  fof(f8,axiom,(
% 2.97/0.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f36,plain,(
% 2.97/0.99    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.97/0.99    inference(nnf_transformation,[],[f8])).
% 2.97/0.99  
% 2.97/0.99  fof(f57,plain,(
% 2.97/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f36])).
% 2.97/0.99  
% 2.97/0.99  fof(f1,axiom,(
% 2.97/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f42,plain,(
% 2.97/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f1])).
% 2.97/0.99  
% 2.97/0.99  fof(f12,axiom,(
% 2.97/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f61,plain,(
% 2.97/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f12])).
% 2.97/0.99  
% 2.97/0.99  fof(f73,plain,(
% 2.97/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.97/0.99    inference(definition_unfolding,[],[f42,f61,f61])).
% 2.97/0.99  
% 2.97/0.99  fof(f4,axiom,(
% 2.97/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f18,plain,(
% 2.97/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.97/0.99    inference(rectify,[],[f4])).
% 2.97/0.99  
% 2.97/0.99  fof(f48,plain,(
% 2.97/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.97/0.99    inference(cnf_transformation,[],[f18])).
% 2.97/0.99  
% 2.97/0.99  fof(f76,plain,(
% 2.97/0.99    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 2.97/0.99    inference(definition_unfolding,[],[f48,f61])).
% 2.97/0.99  
% 2.97/0.99  fof(f11,axiom,(
% 2.97/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f60,plain,(
% 2.97/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f11])).
% 2.97/0.99  
% 2.97/0.99  fof(f80,plain,(
% 2.97/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 2.97/0.99    inference(definition_unfolding,[],[f60,f61])).
% 2.97/0.99  
% 2.97/0.99  fof(f71,plain,(
% 2.97/0.99    sK3 != sK4),
% 2.97/0.99    inference(cnf_transformation,[],[f41])).
% 2.97/0.99  
% 2.97/0.99  cnf(c_14,plain,
% 2.97/0.99      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_973,plain,
% 2.97/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_22,plain,
% 2.97/0.99      ( ~ r2_hidden(X0,X1)
% 2.97/0.99      | ~ r2_hidden(X2,X3)
% 2.97/0.99      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_967,plain,
% 2.97/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.97/0.99      | r2_hidden(X2,X3) != iProver_top
% 2.97/0.99      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_28,negated_conjecture,
% 2.97/0.99      ( k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK4,sK3) ),
% 2.97/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_24,plain,
% 2.97/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_965,plain,
% 2.97/0.99      ( r2_hidden(X0,X1) = iProver_top
% 2.97/0.99      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1383,plain,
% 2.97/0.99      ( r2_hidden(X0,sK4) = iProver_top
% 2.97/0.99      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_28,c_965]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4485,plain,
% 2.97/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 2.97/0.99      | r2_hidden(X1,sK4) = iProver_top
% 2.97/0.99      | r2_hidden(X1,sK3) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_967,c_1383]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5227,plain,
% 2.97/0.99      ( sK4 = k1_xboole_0
% 2.97/0.99      | r2_hidden(X0,sK4) = iProver_top
% 2.97/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_973,c_4485]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_26,negated_conjecture,
% 2.97/0.99      ( k1_xboole_0 != sK4 ),
% 2.97/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_482,plain,( X0 = X0 ),theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_495,plain,
% 2.97/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_482]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_483,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1145,plain,
% 2.97/0.99      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_483]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1146,plain,
% 2.97/0.99      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1145]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6011,plain,
% 2.97/0.99      ( r2_hidden(X0,sK4) = iProver_top | r2_hidden(X0,sK3) != iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_5227,c_26,c_495,c_1146]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6020,plain,
% 2.97/0.99      ( sK3 = k1_xboole_0 | r2_hidden(sK2(sK3),sK4) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_973,c_6011]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_27,negated_conjecture,
% 2.97/0.99      ( k1_xboole_0 != sK3 ),
% 2.97/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1147,plain,
% 2.97/0.99      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_483]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1148,plain,
% 2.97/0.99      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1147]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6672,plain,
% 2.97/0.99      ( r2_hidden(sK2(sK3),sK4) = iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_6020,c_27,c_495,c_1148]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_23,plain,
% 2.97/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_966,plain,
% 2.97/0.99      ( r2_hidden(X0,X1) = iProver_top
% 2.97/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2395,plain,
% 2.97/0.99      ( r2_hidden(X0,sK3) = iProver_top
% 2.97/0.99      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_28,c_966]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4486,plain,
% 2.97/0.99      ( r2_hidden(X0,sK4) != iProver_top
% 2.97/0.99      | r2_hidden(X1,sK3) != iProver_top
% 2.97/0.99      | r2_hidden(X0,sK3) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_967,c_2395]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6677,plain,
% 2.97/0.99      ( r2_hidden(X0,sK3) != iProver_top
% 2.97/0.99      | r2_hidden(sK2(sK3),sK3) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_6672,c_4486]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1138,plain,
% 2.97/0.99      ( r2_hidden(sK2(sK3),sK3) | k1_xboole_0 = sK3 ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1139,plain,
% 2.97/0.99      ( k1_xboole_0 = sK3 | r2_hidden(sK2(sK3),sK3) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_1138]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7109,plain,
% 2.97/0.99      ( r2_hidden(sK2(sK3),sK3) = iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_6677,c_27,c_1139]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3,plain,
% 2.97/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.97/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_983,plain,
% 2.97/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.97/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_5250,plain,
% 2.97/0.99      ( r2_hidden(X0,sK3) != iProver_top
% 2.97/0.99      | r2_hidden(sK0(sK4,X1),sK3) = iProver_top
% 2.97/0.99      | r1_tarski(sK4,X1) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_983,c_4486]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7114,plain,
% 2.97/0.99      ( r2_hidden(sK0(sK4,X0),sK3) = iProver_top
% 2.97/0.99      | r1_tarski(sK4,X0) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_7109,c_5250]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2,plain,
% 2.97/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.97/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_984,plain,
% 2.97/0.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.97/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7236,plain,
% 2.97/0.99      ( r1_tarski(sK4,sK3) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_7114,c_984]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_15,plain,
% 2.97/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_972,plain,
% 2.97/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7830,plain,
% 2.97/0.99      ( k4_xboole_0(sK4,sK3) = k1_xboole_0 ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_7236,c_972]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1,plain,
% 2.97/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8310,plain,
% 2.97/0.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK4,k1_xboole_0) ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_7830,c_1]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_6019,plain,
% 2.97/0.99      ( r2_hidden(sK0(sK3,X0),sK4) = iProver_top
% 2.97/0.99      | r1_tarski(sK3,X0) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_983,c_6011]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7220,plain,
% 2.97/0.99      ( r1_tarski(sK3,sK4) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_6019,c_984]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7538,plain,
% 2.97/0.99      ( k4_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_7220,c_972]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8316,plain,
% 2.97/0.99      ( k4_xboole_0(sK4,k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0) ),
% 2.97/0.99      inference(light_normalisation,[status(thm)],[c_8310,c_7538]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_7,plain,
% 2.97/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_18,plain,
% 2.97/0.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_970,plain,
% 2.97/0.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1213,plain,
% 2.97/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_7,c_970]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3496,plain,
% 2.97/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_1213,c_972]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3519,plain,
% 2.97/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_3496,c_7]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_8317,plain,
% 2.97/0.99      ( sK4 = sK3 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_8316,c_3519]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_25,negated_conjecture,
% 2.97/0.99      ( sK3 != sK4 ),
% 2.97/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_10019,plain,
% 2.97/0.99      ( sK3 != sK3 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_8317,c_25]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_10020,plain,
% 2.97/0.99      ( $false ),
% 2.97/0.99      inference(equality_resolution_simp,[status(thm)],[c_10019]) ).
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  ------                               Statistics
% 2.97/0.99  
% 2.97/0.99  ------ General
% 2.97/0.99  
% 2.97/0.99  abstr_ref_over_cycles:                  0
% 2.97/0.99  abstr_ref_under_cycles:                 0
% 2.97/0.99  gc_basic_clause_elim:                   0
% 2.97/0.99  forced_gc_time:                         0
% 2.97/0.99  parsing_time:                           0.009
% 2.97/0.99  unif_index_cands_time:                  0.
% 2.97/0.99  unif_index_add_time:                    0.
% 2.97/0.99  orderings_time:                         0.
% 2.97/0.99  out_proof_time:                         0.007
% 2.97/0.99  total_time:                             0.254
% 2.97/0.99  num_of_symbols:                         44
% 2.97/0.99  num_of_terms:                           11563
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing
% 2.97/0.99  
% 2.97/0.99  num_of_splits:                          0
% 2.97/0.99  num_of_split_atoms:                     0
% 2.97/0.99  num_of_reused_defs:                     0
% 2.97/0.99  num_eq_ax_congr_red:                    20
% 2.97/0.99  num_of_sem_filtered_clauses:            1
% 2.97/0.99  num_of_subtypes:                        0
% 2.97/0.99  monotx_restored_types:                  0
% 2.97/0.99  sat_num_of_epr_types:                   0
% 2.97/0.99  sat_num_of_non_cyclic_types:            0
% 2.97/0.99  sat_guarded_non_collapsed_types:        0
% 2.97/0.99  num_pure_diseq_elim:                    0
% 2.97/0.99  simp_replaced_by:                       0
% 2.97/0.99  res_preprocessed:                       102
% 2.97/0.99  prep_upred:                             0
% 2.97/0.99  prep_unflattend:                        10
% 2.97/0.99  smt_new_axioms:                         0
% 2.97/0.99  pred_elim_cands:                        3
% 2.97/0.99  pred_elim:                              0
% 2.97/0.99  pred_elim_cl:                           0
% 2.97/0.99  pred_elim_cycles:                       2
% 2.97/0.99  merged_defs:                            18
% 2.97/0.99  merged_defs_ncl:                        0
% 2.97/0.99  bin_hyper_res:                          18
% 2.97/0.99  prep_cycles:                            3
% 2.97/0.99  pred_elim_time:                         0.003
% 2.97/0.99  splitting_time:                         0.
% 2.97/0.99  sem_filter_time:                        0.
% 2.97/0.99  monotx_time:                            0.
% 2.97/0.99  subtype_inf_time:                       0.
% 2.97/0.99  
% 2.97/0.99  ------ Problem properties
% 2.97/0.99  
% 2.97/0.99  clauses:                                29
% 2.97/0.99  conjectures:                            4
% 2.97/0.99  epr:                                    4
% 2.97/0.99  horn:                                   23
% 2.97/0.99  ground:                                 4
% 2.97/0.99  unary:                                  10
% 2.97/0.99  binary:                                 13
% 2.97/0.99  lits:                                   54
% 2.97/0.99  lits_eq:                                16
% 2.97/0.99  fd_pure:                                0
% 2.97/0.99  fd_pseudo:                              0
% 2.97/0.99  fd_cond:                                1
% 2.97/0.99  fd_pseudo_cond:                         0
% 2.97/0.99  ac_symbols:                             0
% 2.97/0.99  
% 2.97/0.99  ------ Propositional Solver
% 2.97/0.99  
% 2.97/0.99  prop_solver_calls:                      25
% 2.97/1.00  prop_fast_solver_calls:                 564
% 2.97/1.00  smt_solver_calls:                       0
% 2.97/1.00  smt_fast_solver_calls:                  0
% 2.97/1.00  prop_num_of_clauses:                    4779
% 2.97/1.00  prop_preprocess_simplified:             9401
% 2.97/1.00  prop_fo_subsumed:                       8
% 2.97/1.00  prop_solver_time:                       0.
% 2.97/1.00  smt_solver_time:                        0.
% 2.97/1.00  smt_fast_solver_time:                   0.
% 2.97/1.00  prop_fast_solver_time:                  0.
% 2.97/1.00  prop_unsat_core_time:                   0.
% 2.97/1.00  
% 2.97/1.00  ------ QBF
% 2.97/1.00  
% 2.97/1.00  qbf_q_res:                              0
% 2.97/1.00  qbf_num_tautologies:                    0
% 2.97/1.00  qbf_prep_cycles:                        0
% 2.97/1.00  
% 2.97/1.00  ------ BMC1
% 2.97/1.00  
% 2.97/1.00  bmc1_current_bound:                     -1
% 2.97/1.00  bmc1_last_solved_bound:                 -1
% 2.97/1.00  bmc1_unsat_core_size:                   -1
% 2.97/1.00  bmc1_unsat_core_parents_size:           -1
% 2.97/1.00  bmc1_merge_next_fun:                    0
% 2.97/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.97/1.00  
% 2.97/1.00  ------ Instantiation
% 2.97/1.00  
% 2.97/1.00  inst_num_of_clauses:                    1234
% 2.97/1.00  inst_num_in_passive:                    380
% 2.97/1.00  inst_num_in_active:                     280
% 2.97/1.00  inst_num_in_unprocessed:                574
% 2.97/1.00  inst_num_of_loops:                      350
% 2.97/1.00  inst_num_of_learning_restarts:          0
% 2.97/1.00  inst_num_moves_active_passive:          67
% 2.97/1.00  inst_lit_activity:                      0
% 2.97/1.00  inst_lit_activity_moves:                1
% 2.97/1.00  inst_num_tautologies:                   0
% 2.97/1.00  inst_num_prop_implied:                  0
% 2.97/1.00  inst_num_existing_simplified:           0
% 2.97/1.00  inst_num_eq_res_simplified:             0
% 2.97/1.00  inst_num_child_elim:                    0
% 2.97/1.00  inst_num_of_dismatching_blockings:      491
% 2.97/1.00  inst_num_of_non_proper_insts:           816
% 2.97/1.00  inst_num_of_duplicates:                 0
% 2.97/1.00  inst_inst_num_from_inst_to_res:         0
% 2.97/1.00  inst_dismatching_checking_time:         0.
% 2.97/1.00  
% 2.97/1.00  ------ Resolution
% 2.97/1.00  
% 2.97/1.00  res_num_of_clauses:                     0
% 2.97/1.00  res_num_in_passive:                     0
% 2.97/1.00  res_num_in_active:                      0
% 2.97/1.00  res_num_of_loops:                       105
% 2.97/1.00  res_forward_subset_subsumed:            16
% 2.97/1.00  res_backward_subset_subsumed:           0
% 2.97/1.00  res_forward_subsumed:                   0
% 2.97/1.00  res_backward_subsumed:                  0
% 2.97/1.00  res_forward_subsumption_resolution:     0
% 2.97/1.00  res_backward_subsumption_resolution:    0
% 2.97/1.00  res_clause_to_clause_subsumption:       770
% 2.97/1.00  res_orphan_elimination:                 0
% 2.97/1.00  res_tautology_del:                      57
% 2.97/1.00  res_num_eq_res_simplified:              0
% 2.97/1.00  res_num_sel_changes:                    0
% 2.97/1.00  res_moves_from_active_to_pass:          0
% 2.97/1.00  
% 2.97/1.00  ------ Superposition
% 2.97/1.00  
% 2.97/1.00  sup_time_total:                         0.
% 2.97/1.00  sup_time_generating:                    0.
% 2.97/1.00  sup_time_sim_full:                      0.
% 2.97/1.00  sup_time_sim_immed:                     0.
% 2.97/1.00  
% 2.97/1.00  sup_num_of_clauses:                     121
% 2.97/1.00  sup_num_in_active:                      39
% 2.97/1.00  sup_num_in_passive:                     82
% 2.97/1.00  sup_num_of_loops:                       69
% 2.97/1.00  sup_fw_superposition:                   205
% 2.97/1.00  sup_bw_superposition:                   212
% 2.97/1.00  sup_immediate_simplified:               216
% 2.97/1.00  sup_given_eliminated:                   1
% 2.97/1.00  comparisons_done:                       0
% 2.97/1.00  comparisons_avoided:                    0
% 2.97/1.00  
% 2.97/1.00  ------ Simplifications
% 2.97/1.00  
% 2.97/1.00  
% 2.97/1.00  sim_fw_subset_subsumed:                 11
% 2.97/1.00  sim_bw_subset_subsumed:                 7
% 2.97/1.00  sim_fw_subsumed:                        40
% 2.97/1.00  sim_bw_subsumed:                        1
% 2.97/1.00  sim_fw_subsumption_res:                 0
% 2.97/1.00  sim_bw_subsumption_res:                 0
% 2.97/1.00  sim_tautology_del:                      4
% 2.97/1.00  sim_eq_tautology_del:                   43
% 2.97/1.00  sim_eq_res_simp:                        9
% 2.97/1.00  sim_fw_demodulated:                     87
% 2.97/1.00  sim_bw_demodulated:                     34
% 2.97/1.00  sim_light_normalised:                   114
% 2.97/1.00  sim_joinable_taut:                      0
% 2.97/1.00  sim_joinable_simp:                      0
% 2.97/1.00  sim_ac_normalised:                      0
% 2.97/1.00  sim_smt_subsumption:                    0
% 2.97/1.00  
%------------------------------------------------------------------------------
