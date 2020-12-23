%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:41 EST 2020

% Result     : Theorem 12.06s
% Output     : CNFRefutation 12.06s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 601 expanded)
%              Number of clauses        :   83 ( 214 expanded)
%              Number of leaves         :   12 ( 130 expanded)
%              Depth                    :   21
%              Number of atoms          :  333 (2375 expanded)
%              Number of equality atoms :  221 (1158 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f24])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f15])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK4 != sK6
        | sK3 != sK5 )
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( sK4 != sK6
      | sK3 != sK5 )
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f16,f28])).

fof(f46,plain,(
    k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f29])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f30,f42,f42])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f49,plain,
    ( sK4 != sK6
    | sK3 != sK5 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_29032,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_29033,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_29709,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK2(k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_29032,c_29033])).

cnf(c_18,negated_conjecture,
    ( k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_29030,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_32755,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_29030])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_29029,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_33445,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_32755,c_29029])).

cnf(c_34083,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_29032,c_33445])).

cnf(c_5434,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5433,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_5431,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5981,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_5431])).

cnf(c_6951,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5433,c_5981])).

cnf(c_7970,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK2(sK3),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5434,c_6951])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_130,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_139,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_130])).

cnf(c_131,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1073,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_1074,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1073])).

cnf(c_8556,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK2(sK3),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7970,c_17,c_139,c_1074])).

cnf(c_8564,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK3),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5434,c_8556])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1071,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_1072,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1071])).

cnf(c_11588,plain,
    ( r2_hidden(sK2(sK3),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8564,c_16,c_139,c_1072])).

cnf(c_6948,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_5433])).

cnf(c_5432,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7647,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6948,c_5432])).

cnf(c_11594,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_11588,c_7647])).

cnf(c_34341,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34083,c_11594])).

cnf(c_34716,plain,
    ( k4_xboole_0(sK6,X0) = k1_xboole_0
    | r2_hidden(sK2(k4_xboole_0(sK6,X0)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_29709,c_34341])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_29034,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_31041,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK2(k4_xboole_0(X0,X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_29032,c_29034])).

cnf(c_43439,plain,
    ( k4_xboole_0(sK6,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_34716,c_31041])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_44801,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK6)) = k4_xboole_0(sK6,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_43439,c_0])).

cnf(c_30799,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_29029])).

cnf(c_32759,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_29030,c_30799])).

cnf(c_33694,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_29032,c_32759])).

cnf(c_6408,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_5432])).

cnf(c_6952,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5433,c_6408])).

cnf(c_7978,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5434,c_6952])).

cnf(c_8289,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7978,c_17,c_139,c_1074])).

cnf(c_34320,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33694,c_17,c_139,c_1074,c_7978])).

cnf(c_34708,plain,
    ( k4_xboole_0(sK4,X0) = k1_xboole_0
    | r2_hidden(sK2(k4_xboole_0(sK4,X0)),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_29709,c_34320])).

cnf(c_43329,plain,
    ( k4_xboole_0(sK4,sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_34708,c_31041])).

cnf(c_44863,plain,
    ( k4_xboole_0(sK6,k1_xboole_0) = k4_xboole_0(sK4,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_44801,c_43329])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_44864,plain,
    ( sK6 = sK4 ),
    inference(demodulation,[status(thm)],[c_44863,c_11])).

cnf(c_29028,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_33446,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_32755,c_29028])).

cnf(c_34714,plain,
    ( k4_xboole_0(sK5,X0) = k1_xboole_0
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(sK2(k4_xboole_0(sK5,X0)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_29709,c_33446])).

cnf(c_8297,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK4),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5434,c_8289])).

cnf(c_10773,plain,
    ( r2_hidden(sK2(sK4),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8297,c_16,c_139,c_1072])).

cnf(c_5435,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5988,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK2(k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5434,c_5435])).

cnf(c_7648,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6948,c_5431])).

cnf(c_8585,plain,
    ( k4_xboole_0(sK5,X0) = k1_xboole_0
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(sK2(k4_xboole_0(sK5,X0)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5988,c_7648])).

cnf(c_10779,plain,
    ( k4_xboole_0(sK5,X0) = k1_xboole_0
    | r2_hidden(sK2(k4_xboole_0(sK5,X0)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_10773,c_8585])).

cnf(c_39674,plain,
    ( k4_xboole_0(sK5,X0) = k1_xboole_0
    | r2_hidden(sK2(k4_xboole_0(sK5,X0)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34714,c_10779])).

cnf(c_39686,plain,
    ( k4_xboole_0(sK5,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_39674,c_31041])).

cnf(c_41252,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k4_xboole_0(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_39686,c_0])).

cnf(c_29646,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_29028])).

cnf(c_32758,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_29030,c_29646])).

cnf(c_34707,plain,
    ( k4_xboole_0(sK3,X0) = k1_xboole_0
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(sK2(k4_xboole_0(sK3,X0)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_29709,c_32758])).

cnf(c_8578,plain,
    ( k4_xboole_0(sK3,X0) = k1_xboole_0
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(sK2(k4_xboole_0(sK3,X0)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5988,c_6951])).

cnf(c_10241,plain,
    ( k4_xboole_0(sK3,X0) = k1_xboole_0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(k4_xboole_0(sK3,X0)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5434,c_8578])).

cnf(c_37928,plain,
    ( k4_xboole_0(sK3,X0) = k1_xboole_0
    | r2_hidden(sK2(k4_xboole_0(sK3,X0)),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34707,c_16,c_139,c_1072,c_10241])).

cnf(c_37938,plain,
    ( k4_xboole_0(sK3,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_37928,c_31041])).

cnf(c_41302,plain,
    ( k4_xboole_0(sK5,k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_41252,c_37938])).

cnf(c_41303,plain,
    ( sK5 = sK3 ),
    inference(demodulation,[status(thm)],[c_41302,c_11])).

cnf(c_15,negated_conjecture,
    ( sK3 != sK5
    | sK4 != sK6 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_42919,plain,
    ( sK3 != sK3
    | sK6 != sK4 ),
    inference(demodulation,[status(thm)],[c_41303,c_15])).

cnf(c_42923,plain,
    ( sK6 != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_42919])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44864,c_42923])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:55:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 12.06/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.06/2.00  
% 12.06/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.06/2.00  
% 12.06/2.00  ------  iProver source info
% 12.06/2.00  
% 12.06/2.00  git: date: 2020-06-30 10:37:57 +0100
% 12.06/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.06/2.00  git: non_committed_changes: false
% 12.06/2.00  git: last_make_outside_of_git: false
% 12.06/2.00  
% 12.06/2.00  ------ 
% 12.06/2.00  ------ Parsing...
% 12.06/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  ------ Proving...
% 12.06/2.00  ------ Problem Properties 
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  clauses                                 19
% 12.06/2.00  conjectures                             4
% 12.06/2.00  EPR                                     3
% 12.06/2.00  Horn                                    13
% 12.06/2.00  unary                                   5
% 12.06/2.00  binary                                  9
% 12.06/2.00  lits                                    39
% 12.06/2.00  lits eq                                 12
% 12.06/2.00  fd_pure                                 0
% 12.06/2.00  fd_pseudo                               0
% 12.06/2.00  fd_cond                                 1
% 12.06/2.00  fd_pseudo_cond                          3
% 12.06/2.00  AC symbols                              0
% 12.06/2.00  
% 12.06/2.00  ------ Input Options Time Limit: Unbounded
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 12.06/2.00  Current options:
% 12.06/2.00  ------ 
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.06/2.00  
% 12.06/2.00  ------ Proving...
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  % SZS status Theorem for theBenchmark.p
% 12.06/2.00  
% 12.06/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 12.06/2.00  
% 12.06/2.00  fof(f4,axiom,(
% 12.06/2.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 12.06/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.06/2.00  
% 12.06/2.00  fof(f13,plain,(
% 12.06/2.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 12.06/2.00    inference(ennf_transformation,[],[f4])).
% 12.06/2.00  
% 12.06/2.00  fof(f24,plain,(
% 12.06/2.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 12.06/2.00    introduced(choice_axiom,[])).
% 12.06/2.00  
% 12.06/2.00  fof(f25,plain,(
% 12.06/2.00    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 12.06/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f24])).
% 12.06/2.00  
% 12.06/2.00  fof(f39,plain,(
% 12.06/2.00    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 12.06/2.00    inference(cnf_transformation,[],[f25])).
% 12.06/2.00  
% 12.06/2.00  fof(f3,axiom,(
% 12.06/2.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 12.06/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.06/2.00  
% 12.06/2.00  fof(f19,plain,(
% 12.06/2.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.06/2.00    inference(nnf_transformation,[],[f3])).
% 12.06/2.00  
% 12.06/2.00  fof(f20,plain,(
% 12.06/2.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.06/2.00    inference(flattening,[],[f19])).
% 12.06/2.00  
% 12.06/2.00  fof(f21,plain,(
% 12.06/2.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.06/2.00    inference(rectify,[],[f20])).
% 12.06/2.00  
% 12.06/2.00  fof(f22,plain,(
% 12.06/2.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 12.06/2.00    introduced(choice_axiom,[])).
% 12.06/2.00  
% 12.06/2.00  fof(f23,plain,(
% 12.06/2.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 12.06/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 12.06/2.00  
% 12.06/2.00  fof(f33,plain,(
% 12.06/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 12.06/2.00    inference(cnf_transformation,[],[f23])).
% 12.06/2.00  
% 12.06/2.00  fof(f54,plain,(
% 12.06/2.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 12.06/2.00    inference(equality_resolution,[],[f33])).
% 12.06/2.00  
% 12.06/2.00  fof(f9,conjecture,(
% 12.06/2.00    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 12.06/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.06/2.00  
% 12.06/2.00  fof(f10,negated_conjecture,(
% 12.06/2.00    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 12.06/2.00    inference(negated_conjecture,[],[f9])).
% 12.06/2.00  
% 12.06/2.00  fof(f15,plain,(
% 12.06/2.00    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 12.06/2.00    inference(ennf_transformation,[],[f10])).
% 12.06/2.00  
% 12.06/2.00  fof(f16,plain,(
% 12.06/2.00    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 12.06/2.00    inference(flattening,[],[f15])).
% 12.06/2.00  
% 12.06/2.00  fof(f28,plain,(
% 12.06/2.00    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK4 != sK6 | sK3 != sK5) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6))),
% 12.06/2.00    introduced(choice_axiom,[])).
% 12.06/2.00  
% 12.06/2.00  fof(f29,plain,(
% 12.06/2.00    (sK4 != sK6 | sK3 != sK5) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6)),
% 12.06/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f16,f28])).
% 12.06/2.00  
% 12.06/2.00  fof(f46,plain,(
% 12.06/2.00    k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6)),
% 12.06/2.00    inference(cnf_transformation,[],[f29])).
% 12.06/2.00  
% 12.06/2.00  fof(f8,axiom,(
% 12.06/2.00    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 12.06/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.06/2.00  
% 12.06/2.00  fof(f26,plain,(
% 12.06/2.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 12.06/2.00    inference(nnf_transformation,[],[f8])).
% 12.06/2.00  
% 12.06/2.00  fof(f27,plain,(
% 12.06/2.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 12.06/2.00    inference(flattening,[],[f26])).
% 12.06/2.00  
% 12.06/2.00  fof(f45,plain,(
% 12.06/2.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 12.06/2.00    inference(cnf_transformation,[],[f27])).
% 12.06/2.00  
% 12.06/2.00  fof(f44,plain,(
% 12.06/2.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 12.06/2.00    inference(cnf_transformation,[],[f27])).
% 12.06/2.00  
% 12.06/2.00  fof(f43,plain,(
% 12.06/2.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 12.06/2.00    inference(cnf_transformation,[],[f27])).
% 12.06/2.00  
% 12.06/2.00  fof(f47,plain,(
% 12.06/2.00    k1_xboole_0 != sK3),
% 12.06/2.00    inference(cnf_transformation,[],[f29])).
% 12.06/2.00  
% 12.06/2.00  fof(f48,plain,(
% 12.06/2.00    k1_xboole_0 != sK4),
% 12.06/2.00    inference(cnf_transformation,[],[f29])).
% 12.06/2.00  
% 12.06/2.00  fof(f34,plain,(
% 12.06/2.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 12.06/2.00    inference(cnf_transformation,[],[f23])).
% 12.06/2.00  
% 12.06/2.00  fof(f53,plain,(
% 12.06/2.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 12.06/2.00    inference(equality_resolution,[],[f34])).
% 12.06/2.00  
% 12.06/2.00  fof(f1,axiom,(
% 12.06/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 12.06/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.06/2.00  
% 12.06/2.00  fof(f30,plain,(
% 12.06/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 12.06/2.00    inference(cnf_transformation,[],[f1])).
% 12.06/2.00  
% 12.06/2.00  fof(f7,axiom,(
% 12.06/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 12.06/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.06/2.00  
% 12.06/2.00  fof(f42,plain,(
% 12.06/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 12.06/2.00    inference(cnf_transformation,[],[f7])).
% 12.06/2.00  
% 12.06/2.00  fof(f50,plain,(
% 12.06/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 12.06/2.00    inference(definition_unfolding,[],[f30,f42,f42])).
% 12.06/2.00  
% 12.06/2.00  fof(f6,axiom,(
% 12.06/2.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 12.06/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.06/2.00  
% 12.06/2.00  fof(f41,plain,(
% 12.06/2.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.06/2.00    inference(cnf_transformation,[],[f6])).
% 12.06/2.00  
% 12.06/2.00  fof(f49,plain,(
% 12.06/2.00    sK4 != sK6 | sK3 != sK5),
% 12.06/2.00    inference(cnf_transformation,[],[f29])).
% 12.06/2.00  
% 12.06/2.00  cnf(c_9,plain,
% 12.06/2.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 12.06/2.00      inference(cnf_transformation,[],[f39]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_29032,plain,
% 12.06/2.00      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 12.06/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_8,plain,
% 12.06/2.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 12.06/2.00      inference(cnf_transformation,[],[f54]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_29033,plain,
% 12.06/2.00      ( r2_hidden(X0,X1) = iProver_top
% 12.06/2.00      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 12.06/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_29709,plain,
% 12.06/2.00      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 12.06/2.00      | r2_hidden(sK2(k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_29032,c_29033]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_18,negated_conjecture,
% 12.06/2.00      ( k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK5,sK6) ),
% 12.06/2.00      inference(cnf_transformation,[],[f46]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_12,plain,
% 12.06/2.00      ( ~ r2_hidden(X0,X1)
% 12.06/2.00      | ~ r2_hidden(X2,X3)
% 12.06/2.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 12.06/2.00      inference(cnf_transformation,[],[f45]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_29030,plain,
% 12.06/2.00      ( r2_hidden(X0,X1) != iProver_top
% 12.06/2.00      | r2_hidden(X2,X3) != iProver_top
% 12.06/2.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 12.06/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_32755,plain,
% 12.06/2.00      ( r2_hidden(X0,sK5) != iProver_top
% 12.06/2.00      | r2_hidden(X1,sK6) != iProver_top
% 12.06/2.00      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_18,c_29030]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_13,plain,
% 12.06/2.00      ( r2_hidden(X0,X1)
% 12.06/2.00      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 12.06/2.00      inference(cnf_transformation,[],[f44]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_29029,plain,
% 12.06/2.00      ( r2_hidden(X0,X1) = iProver_top
% 12.06/2.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 12.06/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_33445,plain,
% 12.06/2.00      ( r2_hidden(X0,sK5) != iProver_top
% 12.06/2.00      | r2_hidden(X1,sK6) != iProver_top
% 12.06/2.00      | r2_hidden(X1,sK4) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_32755,c_29029]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_34083,plain,
% 12.06/2.00      ( sK5 = k1_xboole_0
% 12.06/2.00      | r2_hidden(X0,sK6) != iProver_top
% 12.06/2.00      | r2_hidden(X0,sK4) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_29032,c_33445]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_5434,plain,
% 12.06/2.00      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 12.06/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_5433,plain,
% 12.06/2.00      ( r2_hidden(X0,X1) != iProver_top
% 12.06/2.00      | r2_hidden(X2,X3) != iProver_top
% 12.06/2.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 12.06/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_14,plain,
% 12.06/2.00      ( r2_hidden(X0,X1)
% 12.06/2.00      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 12.06/2.00      inference(cnf_transformation,[],[f43]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_5431,plain,
% 12.06/2.00      ( r2_hidden(X0,X1) = iProver_top
% 12.06/2.00      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 12.06/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_5981,plain,
% 12.06/2.00      ( r2_hidden(X0,sK5) = iProver_top
% 12.06/2.00      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_18,c_5431]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_6951,plain,
% 12.06/2.00      ( r2_hidden(X0,sK5) = iProver_top
% 12.06/2.00      | r2_hidden(X0,sK3) != iProver_top
% 12.06/2.00      | r2_hidden(X1,sK4) != iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_5433,c_5981]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_7970,plain,
% 12.06/2.00      ( sK3 = k1_xboole_0
% 12.06/2.00      | r2_hidden(X0,sK4) != iProver_top
% 12.06/2.00      | r2_hidden(sK2(sK3),sK5) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_5434,c_6951]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_17,negated_conjecture,
% 12.06/2.00      ( k1_xboole_0 != sK3 ),
% 12.06/2.00      inference(cnf_transformation,[],[f47]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_130,plain,( X0 = X0 ),theory(equality) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_139,plain,
% 12.06/2.00      ( k1_xboole_0 = k1_xboole_0 ),
% 12.06/2.00      inference(instantiation,[status(thm)],[c_130]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_131,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_1073,plain,
% 12.06/2.00      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 12.06/2.00      inference(instantiation,[status(thm)],[c_131]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_1074,plain,
% 12.06/2.00      ( sK3 != k1_xboole_0
% 12.06/2.00      | k1_xboole_0 = sK3
% 12.06/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 12.06/2.00      inference(instantiation,[status(thm)],[c_1073]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_8556,plain,
% 12.06/2.00      ( r2_hidden(X0,sK4) != iProver_top
% 12.06/2.00      | r2_hidden(sK2(sK3),sK5) = iProver_top ),
% 12.06/2.00      inference(global_propositional_subsumption,
% 12.06/2.00                [status(thm)],
% 12.06/2.00                [c_7970,c_17,c_139,c_1074]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_8564,plain,
% 12.06/2.00      ( sK4 = k1_xboole_0 | r2_hidden(sK2(sK3),sK5) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_5434,c_8556]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_16,negated_conjecture,
% 12.06/2.00      ( k1_xboole_0 != sK4 ),
% 12.06/2.00      inference(cnf_transformation,[],[f48]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_1071,plain,
% 12.06/2.00      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 12.06/2.00      inference(instantiation,[status(thm)],[c_131]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_1072,plain,
% 12.06/2.00      ( sK4 != k1_xboole_0
% 12.06/2.00      | k1_xboole_0 = sK4
% 12.06/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 12.06/2.00      inference(instantiation,[status(thm)],[c_1071]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_11588,plain,
% 12.06/2.00      ( r2_hidden(sK2(sK3),sK5) = iProver_top ),
% 12.06/2.00      inference(global_propositional_subsumption,
% 12.06/2.00                [status(thm)],
% 12.06/2.00                [c_8564,c_16,c_139,c_1072]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_6948,plain,
% 12.06/2.00      ( r2_hidden(X0,sK5) != iProver_top
% 12.06/2.00      | r2_hidden(X1,sK6) != iProver_top
% 12.06/2.00      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_18,c_5433]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_5432,plain,
% 12.06/2.00      ( r2_hidden(X0,X1) = iProver_top
% 12.06/2.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 12.06/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_7647,plain,
% 12.06/2.00      ( r2_hidden(X0,sK5) != iProver_top
% 12.06/2.00      | r2_hidden(X1,sK6) != iProver_top
% 12.06/2.00      | r2_hidden(X1,sK4) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_6948,c_5432]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_11594,plain,
% 12.06/2.00      ( r2_hidden(X0,sK6) != iProver_top
% 12.06/2.00      | r2_hidden(X0,sK4) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_11588,c_7647]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_34341,plain,
% 12.06/2.00      ( r2_hidden(X0,sK6) != iProver_top
% 12.06/2.00      | r2_hidden(X0,sK4) = iProver_top ),
% 12.06/2.00      inference(global_propositional_subsumption,
% 12.06/2.00                [status(thm)],
% 12.06/2.00                [c_34083,c_11594]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_34716,plain,
% 12.06/2.00      ( k4_xboole_0(sK6,X0) = k1_xboole_0
% 12.06/2.00      | r2_hidden(sK2(k4_xboole_0(sK6,X0)),sK4) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_29709,c_34341]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_7,plain,
% 12.06/2.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 12.06/2.00      inference(cnf_transformation,[],[f53]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_29034,plain,
% 12.06/2.00      ( r2_hidden(X0,X1) != iProver_top
% 12.06/2.00      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 12.06/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_31041,plain,
% 12.06/2.00      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 12.06/2.00      | r2_hidden(sK2(k4_xboole_0(X0,X1)),X1) != iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_29032,c_29034]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_43439,plain,
% 12.06/2.00      ( k4_xboole_0(sK6,sK4) = k1_xboole_0 ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_34716,c_31041]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_0,plain,
% 12.06/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 12.06/2.00      inference(cnf_transformation,[],[f50]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_44801,plain,
% 12.06/2.00      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK6)) = k4_xboole_0(sK6,k1_xboole_0) ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_43439,c_0]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_30799,plain,
% 12.06/2.00      ( r2_hidden(X0,sK6) = iProver_top
% 12.06/2.00      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_18,c_29029]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_32759,plain,
% 12.06/2.00      ( r2_hidden(X0,sK3) != iProver_top
% 12.06/2.00      | r2_hidden(X1,sK6) = iProver_top
% 12.06/2.00      | r2_hidden(X1,sK4) != iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_29030,c_30799]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_33694,plain,
% 12.06/2.00      ( sK3 = k1_xboole_0
% 12.06/2.00      | r2_hidden(X0,sK6) = iProver_top
% 12.06/2.00      | r2_hidden(X0,sK4) != iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_29032,c_32759]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_6408,plain,
% 12.06/2.00      ( r2_hidden(X0,sK6) = iProver_top
% 12.06/2.00      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_18,c_5432]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_6952,plain,
% 12.06/2.00      ( r2_hidden(X0,sK3) != iProver_top
% 12.06/2.00      | r2_hidden(X1,sK6) = iProver_top
% 12.06/2.00      | r2_hidden(X1,sK4) != iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_5433,c_6408]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_7978,plain,
% 12.06/2.00      ( sK3 = k1_xboole_0
% 12.06/2.00      | r2_hidden(X0,sK6) = iProver_top
% 12.06/2.00      | r2_hidden(X0,sK4) != iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_5434,c_6952]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_8289,plain,
% 12.06/2.00      ( r2_hidden(X0,sK6) = iProver_top
% 12.06/2.00      | r2_hidden(X0,sK4) != iProver_top ),
% 12.06/2.00      inference(global_propositional_subsumption,
% 12.06/2.00                [status(thm)],
% 12.06/2.00                [c_7978,c_17,c_139,c_1074]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_34320,plain,
% 12.06/2.00      ( r2_hidden(X0,sK6) = iProver_top
% 12.06/2.00      | r2_hidden(X0,sK4) != iProver_top ),
% 12.06/2.00      inference(global_propositional_subsumption,
% 12.06/2.00                [status(thm)],
% 12.06/2.00                [c_33694,c_17,c_139,c_1074,c_7978]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_34708,plain,
% 12.06/2.00      ( k4_xboole_0(sK4,X0) = k1_xboole_0
% 12.06/2.00      | r2_hidden(sK2(k4_xboole_0(sK4,X0)),sK6) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_29709,c_34320]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_43329,plain,
% 12.06/2.00      ( k4_xboole_0(sK4,sK6) = k1_xboole_0 ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_34708,c_31041]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_44863,plain,
% 12.06/2.00      ( k4_xboole_0(sK6,k1_xboole_0) = k4_xboole_0(sK4,k1_xboole_0) ),
% 12.06/2.00      inference(light_normalisation,[status(thm)],[c_44801,c_43329]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_11,plain,
% 12.06/2.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 12.06/2.00      inference(cnf_transformation,[],[f41]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_44864,plain,
% 12.06/2.00      ( sK6 = sK4 ),
% 12.06/2.00      inference(demodulation,[status(thm)],[c_44863,c_11]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_29028,plain,
% 12.06/2.00      ( r2_hidden(X0,X1) = iProver_top
% 12.06/2.00      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 12.06/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_33446,plain,
% 12.06/2.00      ( r2_hidden(X0,sK5) != iProver_top
% 12.06/2.00      | r2_hidden(X0,sK3) = iProver_top
% 12.06/2.00      | r2_hidden(X1,sK6) != iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_32755,c_29028]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_34714,plain,
% 12.06/2.00      ( k4_xboole_0(sK5,X0) = k1_xboole_0
% 12.06/2.00      | r2_hidden(X1,sK6) != iProver_top
% 12.06/2.00      | r2_hidden(sK2(k4_xboole_0(sK5,X0)),sK3) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_29709,c_33446]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_8297,plain,
% 12.06/2.00      ( sK4 = k1_xboole_0 | r2_hidden(sK2(sK4),sK6) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_5434,c_8289]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_10773,plain,
% 12.06/2.00      ( r2_hidden(sK2(sK4),sK6) = iProver_top ),
% 12.06/2.00      inference(global_propositional_subsumption,
% 12.06/2.00                [status(thm)],
% 12.06/2.00                [c_8297,c_16,c_139,c_1072]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_5435,plain,
% 12.06/2.00      ( r2_hidden(X0,X1) = iProver_top
% 12.06/2.00      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 12.06/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_5988,plain,
% 12.06/2.00      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 12.06/2.00      | r2_hidden(sK2(k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_5434,c_5435]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_7648,plain,
% 12.06/2.00      ( r2_hidden(X0,sK5) != iProver_top
% 12.06/2.00      | r2_hidden(X0,sK3) = iProver_top
% 12.06/2.00      | r2_hidden(X1,sK6) != iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_6948,c_5431]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_8585,plain,
% 12.06/2.00      ( k4_xboole_0(sK5,X0) = k1_xboole_0
% 12.06/2.00      | r2_hidden(X1,sK6) != iProver_top
% 12.06/2.00      | r2_hidden(sK2(k4_xboole_0(sK5,X0)),sK3) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_5988,c_7648]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_10779,plain,
% 12.06/2.00      ( k4_xboole_0(sK5,X0) = k1_xboole_0
% 12.06/2.00      | r2_hidden(sK2(k4_xboole_0(sK5,X0)),sK3) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_10773,c_8585]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_39674,plain,
% 12.06/2.00      ( k4_xboole_0(sK5,X0) = k1_xboole_0
% 12.06/2.00      | r2_hidden(sK2(k4_xboole_0(sK5,X0)),sK3) = iProver_top ),
% 12.06/2.00      inference(global_propositional_subsumption,
% 12.06/2.00                [status(thm)],
% 12.06/2.00                [c_34714,c_10779]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_39686,plain,
% 12.06/2.00      ( k4_xboole_0(sK5,sK3) = k1_xboole_0 ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_39674,c_31041]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_41252,plain,
% 12.06/2.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k4_xboole_0(sK5,k1_xboole_0) ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_39686,c_0]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_29646,plain,
% 12.06/2.00      ( r2_hidden(X0,sK5) = iProver_top
% 12.06/2.00      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_18,c_29028]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_32758,plain,
% 12.06/2.00      ( r2_hidden(X0,sK5) = iProver_top
% 12.06/2.00      | r2_hidden(X0,sK3) != iProver_top
% 12.06/2.00      | r2_hidden(X1,sK4) != iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_29030,c_29646]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_34707,plain,
% 12.06/2.00      ( k4_xboole_0(sK3,X0) = k1_xboole_0
% 12.06/2.00      | r2_hidden(X1,sK4) != iProver_top
% 12.06/2.00      | r2_hidden(sK2(k4_xboole_0(sK3,X0)),sK5) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_29709,c_32758]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_8578,plain,
% 12.06/2.00      ( k4_xboole_0(sK3,X0) = k1_xboole_0
% 12.06/2.00      | r2_hidden(X1,sK4) != iProver_top
% 12.06/2.00      | r2_hidden(sK2(k4_xboole_0(sK3,X0)),sK5) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_5988,c_6951]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_10241,plain,
% 12.06/2.00      ( k4_xboole_0(sK3,X0) = k1_xboole_0
% 12.06/2.00      | sK4 = k1_xboole_0
% 12.06/2.00      | r2_hidden(sK2(k4_xboole_0(sK3,X0)),sK5) = iProver_top ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_5434,c_8578]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_37928,plain,
% 12.06/2.00      ( k4_xboole_0(sK3,X0) = k1_xboole_0
% 12.06/2.00      | r2_hidden(sK2(k4_xboole_0(sK3,X0)),sK5) = iProver_top ),
% 12.06/2.00      inference(global_propositional_subsumption,
% 12.06/2.00                [status(thm)],
% 12.06/2.00                [c_34707,c_16,c_139,c_1072,c_10241]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_37938,plain,
% 12.06/2.00      ( k4_xboole_0(sK3,sK5) = k1_xboole_0 ),
% 12.06/2.00      inference(superposition,[status(thm)],[c_37928,c_31041]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_41302,plain,
% 12.06/2.00      ( k4_xboole_0(sK5,k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0) ),
% 12.06/2.00      inference(light_normalisation,[status(thm)],[c_41252,c_37938]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_41303,plain,
% 12.06/2.00      ( sK5 = sK3 ),
% 12.06/2.00      inference(demodulation,[status(thm)],[c_41302,c_11]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_15,negated_conjecture,
% 12.06/2.00      ( sK3 != sK5 | sK4 != sK6 ),
% 12.06/2.00      inference(cnf_transformation,[],[f49]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_42919,plain,
% 12.06/2.00      ( sK3 != sK3 | sK6 != sK4 ),
% 12.06/2.00      inference(demodulation,[status(thm)],[c_41303,c_15]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(c_42923,plain,
% 12.06/2.00      ( sK6 != sK4 ),
% 12.06/2.00      inference(equality_resolution_simp,[status(thm)],[c_42919]) ).
% 12.06/2.00  
% 12.06/2.00  cnf(contradiction,plain,
% 12.06/2.00      ( $false ),
% 12.06/2.00      inference(minisat,[status(thm)],[c_44864,c_42923]) ).
% 12.06/2.00  
% 12.06/2.00  
% 12.06/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 12.06/2.00  
% 12.06/2.00  ------                               Statistics
% 12.06/2.00  
% 12.06/2.00  ------ Selected
% 12.06/2.00  
% 12.06/2.00  total_time:                             1.446
% 12.06/2.00  
%------------------------------------------------------------------------------
