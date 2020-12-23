%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:37 EST 2020

% Result     : Theorem 19.51s
% Output     : CNFRefutation 19.51s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 941 expanded)
%              Number of clauses        :  106 ( 308 expanded)
%              Number of leaves         :   18 ( 196 expanded)
%              Depth                    :   26
%              Number of atoms          :  450 (3223 expanded)
%              Number of equality atoms :  259 (1674 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f12])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f31])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f9])).

fof(f16,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK3)) != sK3 ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    k1_setfam_1(k1_tarski(sK3)) != sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f33])).

fof(f55,plain,(
    k1_setfam_1(k1_tarski(sK3)) != sK3 ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f66,plain,(
    k1_setfam_1(k2_tarski(sK3,sK3)) != sK3 ),
    inference(definition_unfolding,[],[f55,f45])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f69,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f58])).

fof(f70,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f69])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f71,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X1))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f47,f45])).

fof(f73,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f61])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f46,f45,f45])).

cnf(c_17,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X1,k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_72125,plain,
    ( r2_hidden(arAF0_sK2_0_1(X0),X0)
    | r1_tarski(X1,k1_setfam_1(X0))
    | ~ iProver_ARSWP_99
    | k1_xboole_0 = X0 ),
    inference(arg_filter_abstr,[status(unp)],[c_17])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_19,negated_conjecture,
    ( k1_setfam_1(k2_tarski(sK3,sK3)) != sK3 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_72395,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK3,sK3)),sK3)
    | ~ r1_tarski(sK3,k1_setfam_1(k2_tarski(sK3,sK3))) ),
    inference(resolution,[status(thm)],[c_3,c_19])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_5290,plain,
    ( r2_hidden(sK3,k2_tarski(sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_setfam_1(X1),X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_5120,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_setfam_1(X1),X0) ),
    inference(resolution,[status(thm)],[c_5,c_18])).

cnf(c_4823,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK3,sK3)),sK3)
    | ~ r1_tarski(sK3,k1_setfam_1(k2_tarski(sK3,sK3))) ),
    inference(resolution,[status(thm)],[c_3,c_19])).

cnf(c_5416,plain,
    ( ~ r2_hidden(sK3,k2_tarski(sK3,sK3))
    | ~ r1_tarski(sK3,k1_setfam_1(k2_tarski(sK3,sK3))) ),
    inference(resolution,[status(thm)],[c_5120,c_4823])).

cnf(c_72398,plain,
    ( ~ r1_tarski(sK3,k1_setfam_1(k2_tarski(sK3,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_72395,c_5290,c_5416])).

cnf(c_73707,plain,
    ( r2_hidden(arAF0_sK2_0_1(k2_tarski(sK3,sK3)),k2_tarski(sK3,sK3))
    | ~ iProver_ARSWP_99
    | k1_xboole_0 = k2_tarski(sK3,sK3) ),
    inference(resolution,[status(thm)],[c_72125,c_72398])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_73910,plain,
    ( ~ iProver_ARSWP_99
    | arAF0_sK2_0_1(k2_tarski(sK3,sK3)) = sK3
    | k1_xboole_0 = k2_tarski(sK3,sK3) ),
    inference(resolution,[status(thm)],[c_73707,c_9])).

cnf(c_260,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_258,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_73022,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_260,c_258])).

cnf(c_73920,plain,
    ( r1_tarski(arAF0_sK2_0_1(k2_tarski(sK3,sK3)),X0)
    | ~ r1_tarski(sK3,X0)
    | ~ iProver_ARSWP_99
    | k1_xboole_0 = k2_tarski(sK3,sK3) ),
    inference(resolution,[status(thm)],[c_73910,c_73022])).

cnf(c_261,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_74225,plain,
    ( ~ r2_hidden(X0,k2_tarski(sK3,sK3))
    | r2_hidden(X1,k1_xboole_0)
    | r1_tarski(arAF0_sK2_0_1(k2_tarski(sK3,sK3)),X2)
    | ~ r1_tarski(sK3,X2)
    | ~ iProver_ARSWP_99
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_73920,c_261])).

cnf(c_4982,plain,
    ( ~ r2_hidden(X0,k2_tarski(sK3,sK3))
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_11,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_14846,plain,
    ( r2_hidden(X0,k2_tarski(X1,X1))
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_11])).

cnf(c_18184,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | X0 = X1 ),
    inference(resolution,[status(thm)],[c_14846,c_9])).

cnf(c_259,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_14964,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_259,c_258])).

cnf(c_33214,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_18184,c_14964])).

cnf(c_65904,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_tarski(X2,X2))
    | X0 != X2
    | X1 != k2_tarski(X2,X2) ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_65922,plain,
    ( ~ r2_hidden(X0,k2_tarski(X0,X0))
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0
    | k1_xboole_0 != k2_tarski(X0,X0) ),
    inference(instantiation,[status(thm)],[c_65904])).

cnf(c_70660,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(sK3,k2_tarski(sK3,sK3))
    | X0 != sK3
    | k1_xboole_0 != k2_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_65922])).

cnf(c_65943,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_tarski(X3,X4))
    | X0 != X2
    | X1 != k2_tarski(X3,X4) ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_70301,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | r2_hidden(X3,k1_xboole_0)
    | X3 != X0
    | k1_xboole_0 != k2_tarski(X1,X2) ),
    inference(instantiation,[status(thm)],[c_65943])).

cnf(c_70672,plain,
    ( ~ r2_hidden(X0,k2_tarski(sK3,sK3))
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0
    | k1_xboole_0 != k2_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_70301])).

cnf(c_72685,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_259,c_258])).

cnf(c_74220,plain,
    ( r1_tarski(arAF0_sK2_0_1(k2_tarski(sK3,sK3)),X0)
    | ~ r1_tarski(sK3,X0)
    | ~ iProver_ARSWP_99
    | k2_tarski(sK3,sK3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73920,c_72685])).

cnf(c_39009,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_39002,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_39006,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_39583,plain,
    ( sK2(k2_tarski(X0,X0),X1) = X0
    | k2_tarski(X0,X0) = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(k2_tarski(X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_39002,c_39006])).

cnf(c_39007,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_39001,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_39431,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_39007,c_39001])).

cnf(c_39010,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_39866,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,k1_setfam_1(k2_tarski(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_39431,c_39010])).

cnf(c_40819,plain,
    ( sK2(k2_tarski(X0,X0),X1) = X0
    | k2_tarski(X0,X0) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X0,X0)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_39583,c_39866])).

cnf(c_70359,plain,
    ( sK2(k2_tarski(X0,X0),X0) = X0
    | k2_tarski(X0,X0) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_39009,c_40819])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,sK2(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_39003,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,sK2(X0,X1)) != iProver_top
    | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_70497,plain,
    ( k2_tarski(X0,X0) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X0,X0)) = X0
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_70359,c_39003])).

cnf(c_59,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_70909,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X0) = k1_xboole_0
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X0,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_70497,c_59])).

cnf(c_70910,plain,
    ( k2_tarski(X0,X0) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X0,X0)) = X0
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X0,X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_70909])).

cnf(c_70923,plain,
    ( k2_tarski(X0,X0) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X0,X0)) = X0
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_70910,c_39010])).

cnf(c_70931,plain,
    ( k2_tarski(X0,X0) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X0,X0)) = X0
    | r1_tarski(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_70910,c_39866])).

cnf(c_71096,plain,
    ( ~ r1_tarski(X0,X0)
    | k2_tarski(X0,X0) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_70931])).

cnf(c_71314,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0
    | k2_tarski(X0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_70923,c_59,c_70931])).

cnf(c_71315,plain,
    ( k2_tarski(X0,X0) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_71314])).

cnf(c_71331,plain,
    ( k2_tarski(sK3,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_71315,c_19])).

cnf(c_76349,plain,
    ( k2_tarski(sK3,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_74220,c_71331])).

cnf(c_76363,plain,
    ( k1_xboole_0 = k2_tarski(sK3,sK3) ),
    inference(resolution,[status(thm)],[c_76349,c_72685])).

cnf(c_83170,plain,
    ( ~ r2_hidden(X0,k2_tarski(sK3,sK3))
    | r2_hidden(X1,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_74225,c_4982,c_5290,c_33214,c_70660,c_70672,c_76363])).

cnf(c_83188,plain,
    ( r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_83170,c_8])).

cnf(c_83190,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_83188])).

cnf(c_33324,plain,
    ( X0 != X1
    | X0 = k1_setfam_1(k2_tarski(X2,X3))
    | k1_setfam_1(k2_tarski(X2,X3)) != X1 ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_33325,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_33324])).

cnf(c_14212,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_14215,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_14207,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14954,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_14215,c_14207])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k2_tarski(X1,X1))
    | k2_tarski(X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_14211,plain,
    ( k2_tarski(X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_tarski(X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_15231,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = k2_tarski(X1,X1)
    | k1_setfam_1(k2_tarski(X0,X0)) = k1_xboole_0
    | r1_tarski(X0,k2_tarski(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14954,c_14211])).

cnf(c_27055,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)) = k2_tarski(X0,X0)
    | k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14212,c_15231])).

cnf(c_14217,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_15230,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,k1_setfam_1(k2_tarski(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14954,c_14217])).

cnf(c_27205,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)) = X0
    | k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(X0,k2_tarski(X1,X1)) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27055,c_15230])).

cnf(c_28260,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_27205])).

cnf(c_9673,plain,
    ( X0 != X1
    | k1_setfam_1(k2_tarski(sK3,sK3)) != X1
    | k1_setfam_1(k2_tarski(sK3,sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_12085,plain,
    ( X0 != k1_setfam_1(X1)
    | k1_setfam_1(k2_tarski(sK3,sK3)) = X0
    | k1_setfam_1(k2_tarski(sK3,sK3)) != k1_setfam_1(X1) ),
    inference(instantiation,[status(thm)],[c_9673])).

cnf(c_12102,plain,
    ( X0 != k1_setfam_1(k2_tarski(X1,X2))
    | k1_setfam_1(k2_tarski(sK3,sK3)) = X0
    | k1_setfam_1(k2_tarski(sK3,sK3)) != k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_12085])).

cnf(c_12103,plain,
    ( k1_setfam_1(k2_tarski(sK3,sK3)) != k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0))
    | k1_setfam_1(k2_tarski(sK3,sK3)) = k1_xboole_0
    | k1_xboole_0 != k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_12102])).

cnf(c_262,plain,
    ( X0 != X1
    | X2 != X3
    | k2_tarski(X0,X2) = k2_tarski(X1,X3) ),
    theory(equality)).

cnf(c_10802,plain,
    ( k2_tarski(sK3,sK3) = k2_tarski(X0,X1)
    | sK3 != X0
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_10803,plain,
    ( k2_tarski(sK3,sK3) = k2_tarski(k1_xboole_0,k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10802])).

cnf(c_264,plain,
    ( X0 != X1
    | k1_setfam_1(X0) = k1_setfam_1(X1) ),
    theory(equality)).

cnf(c_9691,plain,
    ( k2_tarski(sK3,sK3) != X0
    | k1_setfam_1(k2_tarski(sK3,sK3)) = k1_setfam_1(X0) ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_10748,plain,
    ( k2_tarski(sK3,sK3) != k2_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(sK3,sK3)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_9691])).

cnf(c_10749,plain,
    ( k2_tarski(sK3,sK3) != k2_tarski(k1_xboole_0,k1_xboole_0)
    | k1_setfam_1(k2_tarski(sK3,sK3)) = k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_10748])).

cnf(c_5050,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k2_tarski(sK3,sK3))
    | X2 != X0
    | k2_tarski(sK3,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_5052,plain,
    ( r2_hidden(k1_xboole_0,k2_tarski(sK3,sK3))
    | ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | k2_tarski(sK3,sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5050])).

cnf(c_4984,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_tarski(sK3,sK3))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_4982])).

cnf(c_4798,plain,
    ( k1_setfam_1(k2_tarski(sK3,sK3)) != X0
    | k1_setfam_1(k2_tarski(sK3,sK3)) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_4799,plain,
    ( k1_setfam_1(k2_tarski(sK3,sK3)) = sK3
    | k1_setfam_1(k2_tarski(sK3,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4798])).

cnf(c_2173,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_2317,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2173])).

cnf(c_2318,plain,
    ( X0 != sK3
    | sK3 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2317])).

cnf(c_2319,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2318])).

cnf(c_61,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_51,plain,
    ( r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_48,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_41,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_43,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_83190,c_71331,c_33325,c_28260,c_12103,c_10803,c_10749,c_5052,c_4984,c_4799,c_2319,c_61,c_51,c_48,c_43,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:09:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.51/3.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.51/3.00  
% 19.51/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.51/3.00  
% 19.51/3.00  ------  iProver source info
% 19.51/3.00  
% 19.51/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.51/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.51/3.00  git: non_committed_changes: false
% 19.51/3.00  git: last_make_outside_of_git: false
% 19.51/3.00  
% 19.51/3.00  ------ 
% 19.51/3.00  ------ Parsing...
% 19.51/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  ------ Proving...
% 19.51/3.00  ------ Problem Properties 
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  clauses                                 19
% 19.51/3.00  conjectures                             1
% 19.51/3.00  EPR                                     3
% 19.51/3.00  Horn                                    13
% 19.51/3.00  unary                                   6
% 19.51/3.00  binary                                  4
% 19.51/3.00  lits                                    41
% 19.51/3.00  lits eq                                 12
% 19.51/3.00  fd_pure                                 0
% 19.51/3.00  fd_pseudo                               0
% 19.51/3.00  fd_cond                                 2
% 19.51/3.00  fd_pseudo_cond                          5
% 19.51/3.00  AC symbols                              0
% 19.51/3.00  
% 19.51/3.00  ------ Input Options Time Limit: Unbounded
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing...
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 19.51/3.00  Current options:
% 19.51/3.00  ------ 
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing...
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.51/3.00  
% 19.51/3.00  ------ Proving...
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  % SZS status Theorem for theBenchmark.p
% 19.51/3.00  
% 19.51/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.51/3.00  
% 19.51/3.00  fof(f7,axiom,(
% 19.51/3.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 19.51/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.51/3.00  
% 19.51/3.00  fof(f12,plain,(
% 19.51/3.00    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 19.51/3.00    inference(ennf_transformation,[],[f7])).
% 19.51/3.00  
% 19.51/3.00  fof(f13,plain,(
% 19.51/3.00    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 19.51/3.00    inference(flattening,[],[f12])).
% 19.51/3.00  
% 19.51/3.00  fof(f31,plain,(
% 19.51/3.00    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 19.51/3.00    introduced(choice_axiom,[])).
% 19.51/3.00  
% 19.51/3.00  fof(f32,plain,(
% 19.51/3.00    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 19.51/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f31])).
% 19.51/3.00  
% 19.51/3.00  fof(f52,plain,(
% 19.51/3.00    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK2(X0,X1),X0)) )),
% 19.51/3.00    inference(cnf_transformation,[],[f32])).
% 19.51/3.00  
% 19.51/3.00  fof(f2,axiom,(
% 19.51/3.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.51/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.51/3.00  
% 19.51/3.00  fof(f21,plain,(
% 19.51/3.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.51/3.00    inference(nnf_transformation,[],[f2])).
% 19.51/3.00  
% 19.51/3.00  fof(f22,plain,(
% 19.51/3.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.51/3.00    inference(flattening,[],[f21])).
% 19.51/3.00  
% 19.51/3.00  fof(f40,plain,(
% 19.51/3.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.51/3.00    inference(cnf_transformation,[],[f22])).
% 19.51/3.00  
% 19.51/3.00  fof(f9,conjecture,(
% 19.51/3.00    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 19.51/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.51/3.00  
% 19.51/3.00  fof(f10,negated_conjecture,(
% 19.51/3.00    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 19.51/3.00    inference(negated_conjecture,[],[f9])).
% 19.51/3.00  
% 19.51/3.00  fof(f16,plain,(
% 19.51/3.00    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 19.51/3.00    inference(ennf_transformation,[],[f10])).
% 19.51/3.00  
% 19.51/3.00  fof(f33,plain,(
% 19.51/3.00    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK3)) != sK3),
% 19.51/3.00    introduced(choice_axiom,[])).
% 19.51/3.00  
% 19.51/3.00  fof(f34,plain,(
% 19.51/3.00    k1_setfam_1(k1_tarski(sK3)) != sK3),
% 19.51/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f33])).
% 19.51/3.00  
% 19.51/3.00  fof(f55,plain,(
% 19.51/3.00    k1_setfam_1(k1_tarski(sK3)) != sK3),
% 19.51/3.00    inference(cnf_transformation,[],[f34])).
% 19.51/3.00  
% 19.51/3.00  fof(f4,axiom,(
% 19.51/3.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 19.51/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.51/3.00  
% 19.51/3.00  fof(f45,plain,(
% 19.51/3.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 19.51/3.00    inference(cnf_transformation,[],[f4])).
% 19.51/3.00  
% 19.51/3.00  fof(f66,plain,(
% 19.51/3.00    k1_setfam_1(k2_tarski(sK3,sK3)) != sK3),
% 19.51/3.00    inference(definition_unfolding,[],[f55,f45])).
% 19.51/3.00  
% 19.51/3.00  fof(f3,axiom,(
% 19.51/3.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 19.51/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.51/3.00  
% 19.51/3.00  fof(f23,plain,(
% 19.51/3.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 19.51/3.00    inference(nnf_transformation,[],[f3])).
% 19.51/3.00  
% 19.51/3.00  fof(f24,plain,(
% 19.51/3.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 19.51/3.00    inference(rectify,[],[f23])).
% 19.51/3.00  
% 19.51/3.00  fof(f25,plain,(
% 19.51/3.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 19.51/3.00    introduced(choice_axiom,[])).
% 19.51/3.00  
% 19.51/3.00  fof(f26,plain,(
% 19.51/3.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 19.51/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).
% 19.51/3.00  
% 19.51/3.00  fof(f42,plain,(
% 19.51/3.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 19.51/3.00    inference(cnf_transformation,[],[f26])).
% 19.51/3.00  
% 19.51/3.00  fof(f58,plain,(
% 19.51/3.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 19.51/3.00    inference(definition_unfolding,[],[f42,f45])).
% 19.51/3.00  
% 19.51/3.00  fof(f69,plain,(
% 19.51/3.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 19.51/3.00    inference(equality_resolution,[],[f58])).
% 19.51/3.00  
% 19.51/3.00  fof(f70,plain,(
% 19.51/3.00    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 19.51/3.00    inference(equality_resolution,[],[f69])).
% 19.51/3.00  
% 19.51/3.00  fof(f38,plain,(
% 19.51/3.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.51/3.00    inference(cnf_transformation,[],[f22])).
% 19.51/3.00  
% 19.51/3.00  fof(f68,plain,(
% 19.51/3.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.51/3.00    inference(equality_resolution,[],[f38])).
% 19.51/3.00  
% 19.51/3.00  fof(f8,axiom,(
% 19.51/3.00    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 19.51/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.51/3.00  
% 19.51/3.00  fof(f14,plain,(
% 19.51/3.00    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 19.51/3.00    inference(ennf_transformation,[],[f8])).
% 19.51/3.00  
% 19.51/3.00  fof(f15,plain,(
% 19.51/3.00    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 19.51/3.00    inference(flattening,[],[f14])).
% 19.51/3.00  
% 19.51/3.00  fof(f54,plain,(
% 19.51/3.00    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 19.51/3.00    inference(cnf_transformation,[],[f15])).
% 19.51/3.00  
% 19.51/3.00  fof(f41,plain,(
% 19.51/3.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 19.51/3.00    inference(cnf_transformation,[],[f26])).
% 19.51/3.00  
% 19.51/3.00  fof(f59,plain,(
% 19.51/3.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 19.51/3.00    inference(definition_unfolding,[],[f41,f45])).
% 19.51/3.00  
% 19.51/3.00  fof(f71,plain,(
% 19.51/3.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 19.51/3.00    inference(equality_resolution,[],[f59])).
% 19.51/3.00  
% 19.51/3.00  fof(f1,axiom,(
% 19.51/3.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.51/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.51/3.00  
% 19.51/3.00  fof(f11,plain,(
% 19.51/3.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 19.51/3.00    inference(ennf_transformation,[],[f1])).
% 19.51/3.00  
% 19.51/3.00  fof(f17,plain,(
% 19.51/3.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 19.51/3.00    inference(nnf_transformation,[],[f11])).
% 19.51/3.00  
% 19.51/3.00  fof(f18,plain,(
% 19.51/3.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.51/3.00    inference(rectify,[],[f17])).
% 19.51/3.00  
% 19.51/3.00  fof(f19,plain,(
% 19.51/3.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.51/3.00    introduced(choice_axiom,[])).
% 19.51/3.00  
% 19.51/3.00  fof(f20,plain,(
% 19.51/3.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.51/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 19.51/3.00  
% 19.51/3.00  fof(f35,plain,(
% 19.51/3.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 19.51/3.00    inference(cnf_transformation,[],[f20])).
% 19.51/3.00  
% 19.51/3.00  fof(f5,axiom,(
% 19.51/3.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 19.51/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.51/3.00  
% 19.51/3.00  fof(f27,plain,(
% 19.51/3.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 19.51/3.00    inference(nnf_transformation,[],[f5])).
% 19.51/3.00  
% 19.51/3.00  fof(f28,plain,(
% 19.51/3.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 19.51/3.00    inference(flattening,[],[f27])).
% 19.51/3.00  
% 19.51/3.00  fof(f47,plain,(
% 19.51/3.00    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 19.51/3.00    inference(cnf_transformation,[],[f28])).
% 19.51/3.00  
% 19.51/3.00  fof(f61,plain,(
% 19.51/3.00    ( ! [X0,X1] : (r1_tarski(X0,k2_tarski(X1,X1)) | k1_xboole_0 != X0) )),
% 19.51/3.00    inference(definition_unfolding,[],[f47,f45])).
% 19.51/3.00  
% 19.51/3.00  fof(f73,plain,(
% 19.51/3.00    ( ! [X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X1))) )),
% 19.51/3.00    inference(equality_resolution,[],[f61])).
% 19.51/3.00  
% 19.51/3.00  fof(f53,plain,(
% 19.51/3.00    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK2(X0,X1))) )),
% 19.51/3.00    inference(cnf_transformation,[],[f32])).
% 19.51/3.00  
% 19.51/3.00  fof(f46,plain,(
% 19.51/3.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 19.51/3.00    inference(cnf_transformation,[],[f28])).
% 19.51/3.00  
% 19.51/3.00  fof(f62,plain,(
% 19.51/3.00    ( ! [X0,X1] : (k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X1))) )),
% 19.51/3.00    inference(definition_unfolding,[],[f46,f45,f45])).
% 19.51/3.00  
% 19.51/3.00  cnf(c_17,plain,
% 19.51/3.00      ( r2_hidden(sK2(X0,X1),X0)
% 19.51/3.00      | r1_tarski(X1,k1_setfam_1(X0))
% 19.51/3.00      | k1_xboole_0 = X0 ),
% 19.51/3.00      inference(cnf_transformation,[],[f52]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_72125,plain,
% 19.51/3.00      ( r2_hidden(arAF0_sK2_0_1(X0),X0)
% 19.51/3.00      | r1_tarski(X1,k1_setfam_1(X0))
% 19.51/3.00      | ~ iProver_ARSWP_99
% 19.51/3.00      | k1_xboole_0 = X0 ),
% 19.51/3.00      inference(arg_filter_abstr,[status(unp)],[c_17]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_3,plain,
% 19.51/3.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 19.51/3.00      inference(cnf_transformation,[],[f40]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_19,negated_conjecture,
% 19.51/3.00      ( k1_setfam_1(k2_tarski(sK3,sK3)) != sK3 ),
% 19.51/3.00      inference(cnf_transformation,[],[f66]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_72395,plain,
% 19.51/3.00      ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK3,sK3)),sK3)
% 19.51/3.00      | ~ r1_tarski(sK3,k1_setfam_1(k2_tarski(sK3,sK3))) ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_3,c_19]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_8,plain,
% 19.51/3.00      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 19.51/3.00      inference(cnf_transformation,[],[f70]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_5290,plain,
% 19.51/3.00      ( r2_hidden(sK3,k2_tarski(sK3,sK3)) ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_8]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_5,plain,
% 19.51/3.00      ( r1_tarski(X0,X0) ),
% 19.51/3.00      inference(cnf_transformation,[],[f68]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_18,plain,
% 19.51/3.00      ( ~ r2_hidden(X0,X1)
% 19.51/3.00      | ~ r1_tarski(X0,X2)
% 19.51/3.00      | r1_tarski(k1_setfam_1(X1),X2) ),
% 19.51/3.00      inference(cnf_transformation,[],[f54]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_5120,plain,
% 19.51/3.00      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0) ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_5,c_18]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_4823,plain,
% 19.51/3.00      ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK3,sK3)),sK3)
% 19.51/3.00      | ~ r1_tarski(sK3,k1_setfam_1(k2_tarski(sK3,sK3))) ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_3,c_19]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_5416,plain,
% 19.51/3.00      ( ~ r2_hidden(sK3,k2_tarski(sK3,sK3))
% 19.51/3.00      | ~ r1_tarski(sK3,k1_setfam_1(k2_tarski(sK3,sK3))) ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_5120,c_4823]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_72398,plain,
% 19.51/3.00      ( ~ r1_tarski(sK3,k1_setfam_1(k2_tarski(sK3,sK3))) ),
% 19.51/3.00      inference(global_propositional_subsumption,
% 19.51/3.00                [status(thm)],
% 19.51/3.00                [c_72395,c_5290,c_5416]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_73707,plain,
% 19.51/3.00      ( r2_hidden(arAF0_sK2_0_1(k2_tarski(sK3,sK3)),k2_tarski(sK3,sK3))
% 19.51/3.00      | ~ iProver_ARSWP_99
% 19.51/3.00      | k1_xboole_0 = k2_tarski(sK3,sK3) ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_72125,c_72398]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_9,plain,
% 19.51/3.00      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 19.51/3.00      inference(cnf_transformation,[],[f71]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_73910,plain,
% 19.51/3.00      ( ~ iProver_ARSWP_99
% 19.51/3.00      | arAF0_sK2_0_1(k2_tarski(sK3,sK3)) = sK3
% 19.51/3.00      | k1_xboole_0 = k2_tarski(sK3,sK3) ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_73707,c_9]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_260,plain,
% 19.51/3.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.51/3.00      theory(equality) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_258,plain,( X0 = X0 ),theory(equality) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_73022,plain,
% 19.51/3.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_260,c_258]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_73920,plain,
% 19.51/3.00      ( r1_tarski(arAF0_sK2_0_1(k2_tarski(sK3,sK3)),X0)
% 19.51/3.00      | ~ r1_tarski(sK3,X0)
% 19.51/3.00      | ~ iProver_ARSWP_99
% 19.51/3.00      | k1_xboole_0 = k2_tarski(sK3,sK3) ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_73910,c_73022]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_261,plain,
% 19.51/3.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.51/3.00      theory(equality) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_74225,plain,
% 19.51/3.00      ( ~ r2_hidden(X0,k2_tarski(sK3,sK3))
% 19.51/3.00      | r2_hidden(X1,k1_xboole_0)
% 19.51/3.00      | r1_tarski(arAF0_sK2_0_1(k2_tarski(sK3,sK3)),X2)
% 19.51/3.00      | ~ r1_tarski(sK3,X2)
% 19.51/3.00      | ~ iProver_ARSWP_99
% 19.51/3.00      | X1 != X0 ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_73920,c_261]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_4982,plain,
% 19.51/3.00      ( ~ r2_hidden(X0,k2_tarski(sK3,sK3)) | X0 = sK3 ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_9]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_2,plain,
% 19.51/3.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 19.51/3.00      inference(cnf_transformation,[],[f35]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_11,plain,
% 19.51/3.00      ( r1_tarski(k1_xboole_0,k2_tarski(X0,X0)) ),
% 19.51/3.00      inference(cnf_transformation,[],[f73]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_14846,plain,
% 19.51/3.00      ( r2_hidden(X0,k2_tarski(X1,X1)) | ~ r2_hidden(X0,k1_xboole_0) ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_2,c_11]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_18184,plain,
% 19.51/3.00      ( ~ r2_hidden(X0,k1_xboole_0) | X0 = X1 ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_14846,c_9]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_259,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_14964,plain,
% 19.51/3.00      ( X0 != X1 | X1 = X0 ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_259,c_258]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_33214,plain,
% 19.51/3.00      ( ~ r2_hidden(X0,k1_xboole_0) | X1 = X0 ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_18184,c_14964]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_65904,plain,
% 19.51/3.00      ( r2_hidden(X0,X1)
% 19.51/3.00      | ~ r2_hidden(X2,k2_tarski(X2,X2))
% 19.51/3.00      | X0 != X2
% 19.51/3.00      | X1 != k2_tarski(X2,X2) ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_261]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_65922,plain,
% 19.51/3.00      ( ~ r2_hidden(X0,k2_tarski(X0,X0))
% 19.51/3.00      | r2_hidden(X1,k1_xboole_0)
% 19.51/3.00      | X1 != X0
% 19.51/3.00      | k1_xboole_0 != k2_tarski(X0,X0) ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_65904]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_70660,plain,
% 19.51/3.00      ( r2_hidden(X0,k1_xboole_0)
% 19.51/3.00      | ~ r2_hidden(sK3,k2_tarski(sK3,sK3))
% 19.51/3.00      | X0 != sK3
% 19.51/3.00      | k1_xboole_0 != k2_tarski(sK3,sK3) ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_65922]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_65943,plain,
% 19.51/3.00      ( r2_hidden(X0,X1)
% 19.51/3.00      | ~ r2_hidden(X2,k2_tarski(X3,X4))
% 19.51/3.00      | X0 != X2
% 19.51/3.00      | X1 != k2_tarski(X3,X4) ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_261]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_70301,plain,
% 19.51/3.00      ( ~ r2_hidden(X0,k2_tarski(X1,X2))
% 19.51/3.00      | r2_hidden(X3,k1_xboole_0)
% 19.51/3.00      | X3 != X0
% 19.51/3.00      | k1_xboole_0 != k2_tarski(X1,X2) ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_65943]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_70672,plain,
% 19.51/3.00      ( ~ r2_hidden(X0,k2_tarski(sK3,sK3))
% 19.51/3.00      | r2_hidden(X1,k1_xboole_0)
% 19.51/3.00      | X1 != X0
% 19.51/3.00      | k1_xboole_0 != k2_tarski(sK3,sK3) ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_70301]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_72685,plain,
% 19.51/3.00      ( X0 != X1 | X1 = X0 ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_259,c_258]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_74220,plain,
% 19.51/3.00      ( r1_tarski(arAF0_sK2_0_1(k2_tarski(sK3,sK3)),X0)
% 19.51/3.00      | ~ r1_tarski(sK3,X0)
% 19.51/3.00      | ~ iProver_ARSWP_99
% 19.51/3.00      | k2_tarski(sK3,sK3) = k1_xboole_0 ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_73920,c_72685]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_39009,plain,
% 19.51/3.00      ( r1_tarski(X0,X0) = iProver_top ),
% 19.51/3.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_39002,plain,
% 19.51/3.00      ( k1_xboole_0 = X0
% 19.51/3.00      | r2_hidden(sK2(X0,X1),X0) = iProver_top
% 19.51/3.00      | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top ),
% 19.51/3.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_39006,plain,
% 19.51/3.00      ( X0 = X1 | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
% 19.51/3.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_39583,plain,
% 19.51/3.00      ( sK2(k2_tarski(X0,X0),X1) = X0
% 19.51/3.00      | k2_tarski(X0,X0) = k1_xboole_0
% 19.51/3.00      | r1_tarski(X1,k1_setfam_1(k2_tarski(X0,X0))) = iProver_top ),
% 19.51/3.00      inference(superposition,[status(thm)],[c_39002,c_39006]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_39007,plain,
% 19.51/3.00      ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
% 19.51/3.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_39001,plain,
% 19.51/3.00      ( r2_hidden(X0,X1) != iProver_top
% 19.51/3.00      | r1_tarski(X0,X2) != iProver_top
% 19.51/3.00      | r1_tarski(k1_setfam_1(X1),X2) = iProver_top ),
% 19.51/3.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_39431,plain,
% 19.51/3.00      ( r1_tarski(X0,X1) != iProver_top
% 19.51/3.00      | r1_tarski(k1_setfam_1(k2_tarski(X0,X0)),X1) = iProver_top ),
% 19.51/3.00      inference(superposition,[status(thm)],[c_39007,c_39001]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_39010,plain,
% 19.51/3.00      ( X0 = X1
% 19.51/3.00      | r1_tarski(X1,X0) != iProver_top
% 19.51/3.00      | r1_tarski(X0,X1) != iProver_top ),
% 19.51/3.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_39866,plain,
% 19.51/3.00      ( k1_setfam_1(k2_tarski(X0,X0)) = X1
% 19.51/3.00      | r1_tarski(X0,X1) != iProver_top
% 19.51/3.00      | r1_tarski(X1,k1_setfam_1(k2_tarski(X0,X0))) != iProver_top ),
% 19.51/3.00      inference(superposition,[status(thm)],[c_39431,c_39010]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_40819,plain,
% 19.51/3.00      ( sK2(k2_tarski(X0,X0),X1) = X0
% 19.51/3.00      | k2_tarski(X0,X0) = k1_xboole_0
% 19.51/3.00      | k1_setfam_1(k2_tarski(X0,X0)) = X1
% 19.51/3.00      | r1_tarski(X0,X1) != iProver_top ),
% 19.51/3.00      inference(superposition,[status(thm)],[c_39583,c_39866]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_70359,plain,
% 19.51/3.00      ( sK2(k2_tarski(X0,X0),X0) = X0
% 19.51/3.00      | k2_tarski(X0,X0) = k1_xboole_0
% 19.51/3.00      | k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 19.51/3.00      inference(superposition,[status(thm)],[c_39009,c_40819]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_16,plain,
% 19.51/3.00      ( ~ r1_tarski(X0,sK2(X1,X0))
% 19.51/3.00      | r1_tarski(X0,k1_setfam_1(X1))
% 19.51/3.00      | k1_xboole_0 = X1 ),
% 19.51/3.00      inference(cnf_transformation,[],[f53]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_39003,plain,
% 19.51/3.00      ( k1_xboole_0 = X0
% 19.51/3.00      | r1_tarski(X1,sK2(X0,X1)) != iProver_top
% 19.51/3.00      | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top ),
% 19.51/3.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_70497,plain,
% 19.51/3.00      ( k2_tarski(X0,X0) = k1_xboole_0
% 19.51/3.00      | k1_setfam_1(k2_tarski(X0,X0)) = X0
% 19.51/3.00      | r1_tarski(X0,X0) != iProver_top
% 19.51/3.00      | r1_tarski(X0,k1_setfam_1(k2_tarski(X0,X0))) = iProver_top ),
% 19.51/3.00      inference(superposition,[status(thm)],[c_70359,c_39003]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_59,plain,
% 19.51/3.00      ( r1_tarski(X0,X0) = iProver_top ),
% 19.51/3.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_70909,plain,
% 19.51/3.00      ( k1_setfam_1(k2_tarski(X0,X0)) = X0
% 19.51/3.00      | k2_tarski(X0,X0) = k1_xboole_0
% 19.51/3.00      | r1_tarski(X0,k1_setfam_1(k2_tarski(X0,X0))) = iProver_top ),
% 19.51/3.00      inference(global_propositional_subsumption,
% 19.51/3.00                [status(thm)],
% 19.51/3.00                [c_70497,c_59]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_70910,plain,
% 19.51/3.00      ( k2_tarski(X0,X0) = k1_xboole_0
% 19.51/3.00      | k1_setfam_1(k2_tarski(X0,X0)) = X0
% 19.51/3.00      | r1_tarski(X0,k1_setfam_1(k2_tarski(X0,X0))) = iProver_top ),
% 19.51/3.00      inference(renaming,[status(thm)],[c_70909]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_70923,plain,
% 19.51/3.00      ( k2_tarski(X0,X0) = k1_xboole_0
% 19.51/3.00      | k1_setfam_1(k2_tarski(X0,X0)) = X0
% 19.51/3.00      | r1_tarski(k1_setfam_1(k2_tarski(X0,X0)),X0) != iProver_top ),
% 19.51/3.00      inference(superposition,[status(thm)],[c_70910,c_39010]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_70931,plain,
% 19.51/3.00      ( k2_tarski(X0,X0) = k1_xboole_0
% 19.51/3.00      | k1_setfam_1(k2_tarski(X0,X0)) = X0
% 19.51/3.00      | r1_tarski(X0,X0) != iProver_top ),
% 19.51/3.00      inference(superposition,[status(thm)],[c_70910,c_39866]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_71096,plain,
% 19.51/3.00      ( ~ r1_tarski(X0,X0)
% 19.51/3.00      | k2_tarski(X0,X0) = k1_xboole_0
% 19.51/3.00      | k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 19.51/3.00      inference(predicate_to_equality_rev,[status(thm)],[c_70931]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_71314,plain,
% 19.51/3.00      ( k1_setfam_1(k2_tarski(X0,X0)) = X0
% 19.51/3.00      | k2_tarski(X0,X0) = k1_xboole_0 ),
% 19.51/3.00      inference(global_propositional_subsumption,
% 19.51/3.00                [status(thm)],
% 19.51/3.00                [c_70923,c_59,c_70931]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_71315,plain,
% 19.51/3.00      ( k2_tarski(X0,X0) = k1_xboole_0
% 19.51/3.00      | k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 19.51/3.00      inference(renaming,[status(thm)],[c_71314]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_71331,plain,
% 19.51/3.00      ( k2_tarski(sK3,sK3) = k1_xboole_0 ),
% 19.51/3.00      inference(superposition,[status(thm)],[c_71315,c_19]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_76349,plain,
% 19.51/3.00      ( k2_tarski(sK3,sK3) = k1_xboole_0 ),
% 19.51/3.00      inference(global_propositional_subsumption,
% 19.51/3.00                [status(thm)],
% 19.51/3.00                [c_74220,c_71331]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_76363,plain,
% 19.51/3.00      ( k1_xboole_0 = k2_tarski(sK3,sK3) ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_76349,c_72685]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_83170,plain,
% 19.51/3.00      ( ~ r2_hidden(X0,k2_tarski(sK3,sK3)) | r2_hidden(X1,k1_xboole_0) ),
% 19.51/3.00      inference(global_propositional_subsumption,
% 19.51/3.00                [status(thm)],
% 19.51/3.00                [c_74225,c_4982,c_5290,c_33214,c_70660,c_70672,c_76363]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_83188,plain,
% 19.51/3.00      ( r2_hidden(X0,k1_xboole_0) ),
% 19.51/3.00      inference(resolution,[status(thm)],[c_83170,c_8]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_83190,plain,
% 19.51/3.00      ( r2_hidden(k1_xboole_0,k1_xboole_0) ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_83188]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_33324,plain,
% 19.51/3.00      ( X0 != X1
% 19.51/3.00      | X0 = k1_setfam_1(k2_tarski(X2,X3))
% 19.51/3.00      | k1_setfam_1(k2_tarski(X2,X3)) != X1 ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_259]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_33325,plain,
% 19.51/3.00      ( k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
% 19.51/3.00      | k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0))
% 19.51/3.00      | k1_xboole_0 != k1_xboole_0 ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_33324]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_14212,plain,
% 19.51/3.00      ( r1_tarski(k1_xboole_0,k2_tarski(X0,X0)) = iProver_top ),
% 19.51/3.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_14215,plain,
% 19.51/3.00      ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
% 19.51/3.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_14207,plain,
% 19.51/3.00      ( r2_hidden(X0,X1) != iProver_top
% 19.51/3.00      | r1_tarski(X0,X2) != iProver_top
% 19.51/3.00      | r1_tarski(k1_setfam_1(X1),X2) = iProver_top ),
% 19.51/3.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_14954,plain,
% 19.51/3.00      ( r1_tarski(X0,X1) != iProver_top
% 19.51/3.00      | r1_tarski(k1_setfam_1(k2_tarski(X0,X0)),X1) = iProver_top ),
% 19.51/3.00      inference(superposition,[status(thm)],[c_14215,c_14207]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_12,plain,
% 19.51/3.00      ( ~ r1_tarski(X0,k2_tarski(X1,X1))
% 19.51/3.00      | k2_tarski(X1,X1) = X0
% 19.51/3.00      | k1_xboole_0 = X0 ),
% 19.51/3.00      inference(cnf_transformation,[],[f62]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_14211,plain,
% 19.51/3.00      ( k2_tarski(X0,X0) = X1
% 19.51/3.00      | k1_xboole_0 = X1
% 19.51/3.00      | r1_tarski(X1,k2_tarski(X0,X0)) != iProver_top ),
% 19.51/3.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_15231,plain,
% 19.51/3.00      ( k1_setfam_1(k2_tarski(X0,X0)) = k2_tarski(X1,X1)
% 19.51/3.00      | k1_setfam_1(k2_tarski(X0,X0)) = k1_xboole_0
% 19.51/3.00      | r1_tarski(X0,k2_tarski(X1,X1)) != iProver_top ),
% 19.51/3.00      inference(superposition,[status(thm)],[c_14954,c_14211]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_27055,plain,
% 19.51/3.00      ( k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)) = k2_tarski(X0,X0)
% 19.51/3.00      | k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 19.51/3.00      inference(superposition,[status(thm)],[c_14212,c_15231]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_14217,plain,
% 19.51/3.00      ( X0 = X1
% 19.51/3.00      | r1_tarski(X1,X0) != iProver_top
% 19.51/3.00      | r1_tarski(X0,X1) != iProver_top ),
% 19.51/3.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_15230,plain,
% 19.51/3.00      ( k1_setfam_1(k2_tarski(X0,X0)) = X1
% 19.51/3.00      | r1_tarski(X0,X1) != iProver_top
% 19.51/3.00      | r1_tarski(X1,k1_setfam_1(k2_tarski(X0,X0))) != iProver_top ),
% 19.51/3.00      inference(superposition,[status(thm)],[c_14954,c_14217]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_27205,plain,
% 19.51/3.00      ( k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)) = X0
% 19.51/3.00      | k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
% 19.51/3.00      | r1_tarski(X0,k2_tarski(X1,X1)) != iProver_top
% 19.51/3.00      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 19.51/3.00      inference(superposition,[status(thm)],[c_27055,c_15230]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_28260,plain,
% 19.51/3.00      ( k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
% 19.51/3.00      | r1_tarski(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)) != iProver_top
% 19.51/3.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_27205]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_9673,plain,
% 19.51/3.00      ( X0 != X1
% 19.51/3.00      | k1_setfam_1(k2_tarski(sK3,sK3)) != X1
% 19.51/3.00      | k1_setfam_1(k2_tarski(sK3,sK3)) = X0 ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_259]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_12085,plain,
% 19.51/3.00      ( X0 != k1_setfam_1(X1)
% 19.51/3.00      | k1_setfam_1(k2_tarski(sK3,sK3)) = X0
% 19.51/3.00      | k1_setfam_1(k2_tarski(sK3,sK3)) != k1_setfam_1(X1) ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_9673]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_12102,plain,
% 19.51/3.00      ( X0 != k1_setfam_1(k2_tarski(X1,X2))
% 19.51/3.00      | k1_setfam_1(k2_tarski(sK3,sK3)) = X0
% 19.51/3.00      | k1_setfam_1(k2_tarski(sK3,sK3)) != k1_setfam_1(k2_tarski(X1,X2)) ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_12085]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_12103,plain,
% 19.51/3.00      ( k1_setfam_1(k2_tarski(sK3,sK3)) != k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0))
% 19.51/3.00      | k1_setfam_1(k2_tarski(sK3,sK3)) = k1_xboole_0
% 19.51/3.00      | k1_xboole_0 != k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)) ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_12102]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_262,plain,
% 19.51/3.00      ( X0 != X1 | X2 != X3 | k2_tarski(X0,X2) = k2_tarski(X1,X3) ),
% 19.51/3.00      theory(equality) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_10802,plain,
% 19.51/3.00      ( k2_tarski(sK3,sK3) = k2_tarski(X0,X1) | sK3 != X0 | sK3 != X1 ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_262]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_10803,plain,
% 19.51/3.00      ( k2_tarski(sK3,sK3) = k2_tarski(k1_xboole_0,k1_xboole_0)
% 19.51/3.00      | sK3 != k1_xboole_0 ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_10802]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_264,plain,
% 19.51/3.00      ( X0 != X1 | k1_setfam_1(X0) = k1_setfam_1(X1) ),
% 19.51/3.00      theory(equality) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_9691,plain,
% 19.51/3.00      ( k2_tarski(sK3,sK3) != X0
% 19.51/3.00      | k1_setfam_1(k2_tarski(sK3,sK3)) = k1_setfam_1(X0) ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_264]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_10748,plain,
% 19.51/3.00      ( k2_tarski(sK3,sK3) != k2_tarski(X0,X1)
% 19.51/3.00      | k1_setfam_1(k2_tarski(sK3,sK3)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_9691]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_10749,plain,
% 19.51/3.00      ( k2_tarski(sK3,sK3) != k2_tarski(k1_xboole_0,k1_xboole_0)
% 19.51/3.00      | k1_setfam_1(k2_tarski(sK3,sK3)) = k1_setfam_1(k2_tarski(k1_xboole_0,k1_xboole_0)) ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_10748]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_5050,plain,
% 19.51/3.00      ( ~ r2_hidden(X0,X1)
% 19.51/3.00      | r2_hidden(X2,k2_tarski(sK3,sK3))
% 19.51/3.00      | X2 != X0
% 19.51/3.00      | k2_tarski(sK3,sK3) != X1 ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_261]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_5052,plain,
% 19.51/3.00      ( r2_hidden(k1_xboole_0,k2_tarski(sK3,sK3))
% 19.51/3.00      | ~ r2_hidden(k1_xboole_0,k1_xboole_0)
% 19.51/3.00      | k2_tarski(sK3,sK3) != k1_xboole_0
% 19.51/3.00      | k1_xboole_0 != k1_xboole_0 ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_5050]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_4984,plain,
% 19.51/3.00      ( ~ r2_hidden(k1_xboole_0,k2_tarski(sK3,sK3)) | k1_xboole_0 = sK3 ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_4982]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_4798,plain,
% 19.51/3.00      ( k1_setfam_1(k2_tarski(sK3,sK3)) != X0
% 19.51/3.00      | k1_setfam_1(k2_tarski(sK3,sK3)) = sK3
% 19.51/3.00      | sK3 != X0 ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_259]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_4799,plain,
% 19.51/3.00      ( k1_setfam_1(k2_tarski(sK3,sK3)) = sK3
% 19.51/3.00      | k1_setfam_1(k2_tarski(sK3,sK3)) != k1_xboole_0
% 19.51/3.00      | sK3 != k1_xboole_0 ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_4798]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_2173,plain,
% 19.51/3.00      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_259]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_2317,plain,
% 19.51/3.00      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_2173]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_2318,plain,
% 19.51/3.00      ( X0 != sK3 | sK3 = X0 ),
% 19.51/3.00      inference(equality_resolution_simp,[status(thm)],[c_2317]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_2319,plain,
% 19.51/3.00      ( sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_2318]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_61,plain,
% 19.51/3.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_59]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_51,plain,
% 19.51/3.00      ( r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)) ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_8]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_48,plain,
% 19.51/3.00      ( ~ r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0))
% 19.51/3.00      | k1_xboole_0 = k1_xboole_0 ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_9]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_41,plain,
% 19.51/3.00      ( r1_tarski(k1_xboole_0,k2_tarski(X0,X0)) = iProver_top ),
% 19.51/3.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(c_43,plain,
% 19.51/3.00      ( r1_tarski(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 19.51/3.00      inference(instantiation,[status(thm)],[c_41]) ).
% 19.51/3.00  
% 19.51/3.00  cnf(contradiction,plain,
% 19.51/3.00      ( $false ),
% 19.51/3.00      inference(minisat,
% 19.51/3.00                [status(thm)],
% 19.51/3.00                [c_83190,c_71331,c_33325,c_28260,c_12103,c_10803,c_10749,
% 19.51/3.00                 c_5052,c_4984,c_4799,c_2319,c_61,c_51,c_48,c_43,c_19]) ).
% 19.51/3.00  
% 19.51/3.00  
% 19.51/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.51/3.00  
% 19.51/3.00  ------                               Statistics
% 19.51/3.00  
% 19.51/3.00  ------ Selected
% 19.51/3.00  
% 19.51/3.00  total_time:                             2.386
% 19.51/3.00  
%------------------------------------------------------------------------------
