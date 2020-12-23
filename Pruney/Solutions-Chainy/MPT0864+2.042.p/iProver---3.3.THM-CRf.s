%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:54 EST 2020

% Result     : Theorem 11.42s
% Output     : CNFRefutation 11.42s
% Verified   : 
% Statistics : Number of formulae       :  106 (1351 expanded)
%              Number of clauses        :   59 ( 406 expanded)
%              Number of leaves         :   13 ( 347 expanded)
%              Depth                    :   25
%              Number of atoms          :  305 (5170 expanded)
%              Number of equality atoms :  230 (3765 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK7(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK7(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK7(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f17,f40])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f48])).

fof(f86,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f85])).

fof(f13,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f18,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(sK9,sK10) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( k2_mcart_1(sK8) = sK8
        | k1_mcart_1(sK8) = sK8 )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK8 ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( k2_mcart_1(sK8) = sK8
      | k1_mcart_1(sK8) = sK8 )
    & k4_tarski(sK9,sK10) = sK8 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f18,f43,f42])).

fof(f76,plain,(
    k4_tarski(sK9,sK10) = sK8 ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK7(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,
    ( k2_mcart_1(sK8) = sK8
    | k1_mcart_1(sK8) = sK8 ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK7(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f82,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f61,f53])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X1 != X3
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X2,X2),k2_tarski(X3,X3)))
      | X1 != X3
      | X0 != X2 ) ),
    inference(definition_unfolding,[],[f60,f53,f53])).

fof(f90,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(k2_tarski(X2,X2),k2_tarski(X3,X3)))
      | X0 != X2 ) ),
    inference(equality_resolution,[],[f78])).

fof(f91,plain,(
    ! [X2,X3] : r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k2_tarski(X2,X2),k2_tarski(X3,X3))) ),
    inference(equality_resolution,[],[f90])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_29,plain,
    ( r2_hidden(sK7(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_53240,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK7(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_53247,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_53547,plain,
    ( k2_tarski(X0,X1) = k1_xboole_0
    | sK7(k2_tarski(X0,X1)) = X0
    | sK7(k2_tarski(X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_53240,c_53247])).

cnf(c_53820,plain,
    ( k2_tarski(X0,X1) = k1_xboole_0
    | sK7(k2_tarski(X0,X1)) = X1
    | r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_53547,c_53240])).

cnf(c_6,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_84,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_54253,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_53820,c_84])).

cnf(c_31,negated_conjecture,
    ( k4_tarski(sK9,sK10) = sK8 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X0,X2) != sK7(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_53241,plain,
    ( k4_tarski(X0,X1) != sK7(X2)
    | k1_xboole_0 = X2
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_53513,plain,
    ( sK7(X0) != sK8
    | k1_xboole_0 = X0
    | r2_hidden(sK9,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_53241])).

cnf(c_53812,plain,
    ( k2_tarski(X0,X1) = k1_xboole_0
    | sK7(k2_tarski(X0,X1)) = X0
    | sK8 != X1
    | r2_hidden(sK9,k2_tarski(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_53547,c_53513])).

cnf(c_53976,plain,
    ( k2_tarski(X0,sK8) = k1_xboole_0
    | sK7(k2_tarski(X0,sK8)) = X0
    | r2_hidden(sK9,k2_tarski(X0,sK8)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_53812])).

cnf(c_54321,plain,
    ( k2_tarski(sK9,sK8) = k1_xboole_0
    | sK7(k2_tarski(sK9,sK8)) = sK9 ),
    inference(superposition,[status(thm)],[c_54253,c_53976])).

cnf(c_30,negated_conjecture,
    ( k1_mcart_1(sK8) = sK8
    | k2_mcart_1(sK8) = sK8 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_26,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_53381,plain,
    ( k1_mcart_1(sK8) = sK9 ),
    inference(superposition,[status(thm)],[c_31,c_26])).

cnf(c_53433,plain,
    ( k2_mcart_1(sK8) = sK8
    | sK9 = sK8 ),
    inference(superposition,[status(thm)],[c_30,c_53381])).

cnf(c_25,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_53358,plain,
    ( k2_mcart_1(sK8) = sK10 ),
    inference(superposition,[status(thm)],[c_31,c_25])).

cnf(c_53435,plain,
    ( sK10 = sK8
    | sK9 = sK8 ),
    inference(demodulation,[status(thm)],[c_53433,c_53358])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X2,X0) != sK7(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_53242,plain,
    ( k4_tarski(X0,X1) != sK7(X2)
    | k1_xboole_0 = X2
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_53634,plain,
    ( sK7(X0) != sK8
    | k1_xboole_0 = X0
    | r2_hidden(sK10,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_53242])).

cnf(c_53818,plain,
    ( k2_tarski(X0,X1) = k1_xboole_0
    | sK7(k2_tarski(X0,X1)) = X1
    | sK8 != X0
    | r2_hidden(sK10,k2_tarski(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_53547,c_53634])).

cnf(c_53990,plain,
    ( k2_tarski(sK8,X0) = k1_xboole_0
    | sK7(k2_tarski(sK8,X0)) = X0
    | r2_hidden(sK10,k2_tarski(sK8,X0)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_53818])).

cnf(c_54332,plain,
    ( k2_tarski(sK8,X0) = k1_xboole_0
    | sK7(k2_tarski(sK8,X0)) = X0
    | sK9 = sK8
    | r2_hidden(sK8,k2_tarski(sK8,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_53435,c_53990])).

cnf(c_54367,plain,
    ( k2_tarski(sK8,X0) = k1_xboole_0
    | sK7(k2_tarski(sK8,X0)) = X0
    | sK9 = sK8 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_54332,c_54253])).

cnf(c_54372,plain,
    ( k2_tarski(sK8,X0) = k1_xboole_0
    | sK9 = sK8
    | sK8 != X0
    | r2_hidden(sK9,k2_tarski(sK8,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_54367,c_53513])).

cnf(c_54462,plain,
    ( k2_tarski(sK8,sK8) = k1_xboole_0
    | sK9 = sK8
    | r2_hidden(sK9,k2_tarski(sK8,sK8)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_54372])).

cnf(c_16,plain,
    ( k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_12,plain,
    ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2945,plain,
    ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2965,plain,
    ( r2_hidden(k4_tarski(X0,X1),k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16,c_2945])).

cnf(c_3019,plain,
    ( r2_hidden(sK8,k2_tarski(sK8,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_2965])).

cnf(c_54371,plain,
    ( k2_tarski(sK8,X0) = k1_xboole_0
    | sK9 = sK8
    | sK8 != X0
    | r2_hidden(sK10,k2_tarski(sK8,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_54367,c_53634])).

cnf(c_54450,plain,
    ( k2_tarski(sK8,sK8) = k1_xboole_0
    | sK9 = sK8
    | r2_hidden(sK10,k2_tarski(sK8,sK8)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_54371])).

cnf(c_54593,plain,
    ( k2_tarski(sK8,sK8) = k1_xboole_0
    | sK9 = sK8
    | r2_hidden(sK8,k2_tarski(sK8,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_53435,c_54450])).

cnf(c_54606,plain,
    ( sK9 = sK8
    | k2_tarski(sK8,sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_54462,c_3019,c_54593])).

cnf(c_54607,plain,
    ( k2_tarski(sK8,sK8) = k1_xboole_0
    | sK9 = sK8 ),
    inference(renaming,[status(thm)],[c_54606])).

cnf(c_53245,plain,
    ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_53282,plain,
    ( r2_hidden(k4_tarski(X0,X1),k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16,c_53245])).

cnf(c_53517,plain,
    ( r2_hidden(sK8,k2_tarski(sK8,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_53282])).

cnf(c_54627,plain,
    ( sK9 = sK8
    | r2_hidden(sK8,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_54607,c_53517])).

cnf(c_0,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_275,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_276,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_53238,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_54711,plain,
    ( sK9 = sK8 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_54627,c_53238])).

cnf(c_55290,plain,
    ( k2_tarski(sK8,sK8) = k1_xboole_0
    | sK7(k2_tarski(sK8,sK8)) = sK8 ),
    inference(light_normalisation,[status(thm)],[c_54321,c_54711])).

cnf(c_55295,plain,
    ( k2_tarski(sK8,sK8) = k1_xboole_0
    | r2_hidden(sK10,k2_tarski(sK8,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_55290,c_53634])).

cnf(c_54739,plain,
    ( sK7(X0) != sK8
    | k1_xboole_0 = X0
    | r2_hidden(sK8,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_54711,c_53513])).

cnf(c_55294,plain,
    ( k2_tarski(sK8,sK8) = k1_xboole_0
    | r2_hidden(sK8,k2_tarski(sK8,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_55290,c_54739])).

cnf(c_55336,plain,
    ( k2_tarski(sK8,sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_55295,c_3019,c_55294])).

cnf(c_55346,plain,
    ( r2_hidden(sK8,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_55336,c_53517])).

cnf(c_55411,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_55346,c_53238])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.42/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.42/2.00  
% 11.42/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.42/2.00  
% 11.42/2.00  ------  iProver source info
% 11.42/2.00  
% 11.42/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.42/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.42/2.00  git: non_committed_changes: false
% 11.42/2.00  git: last_make_outside_of_git: false
% 11.42/2.00  
% 11.42/2.00  ------ 
% 11.42/2.00  ------ Parsing...
% 11.42/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  ------ Proving...
% 11.42/2.00  ------ Problem Properties 
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  clauses                                 31
% 11.42/2.00  conjectures                             3
% 11.42/2.00  EPR                                     1
% 11.42/2.00  Horn                                    24
% 11.42/2.00  unary                                   12
% 11.42/2.00  binary                                  8
% 11.42/2.00  lits                                    62
% 11.42/2.00  lits eq                                 32
% 11.42/2.00  fd_pure                                 0
% 11.42/2.00  fd_pseudo                               0
% 11.42/2.00  fd_cond                                 4
% 11.42/2.00  fd_pseudo_cond                          9
% 11.42/2.00  AC symbols                              0
% 11.42/2.00  
% 11.42/2.00  ------ Input Options Time Limit: Unbounded
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing...
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 11.42/2.00  Current options:
% 11.42/2.00  ------ 
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing...
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing...
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing...
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing...
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.42/2.00  
% 11.42/2.00  ------ Proving...
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  % SZS status Theorem for theBenchmark.p
% 11.42/2.00  
% 11.42/2.00   Resolution empty clause
% 11.42/2.00  
% 11.42/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.42/2.00  
% 11.42/2.00  fof(f12,axiom,(
% 11.42/2.00    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 11.42/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.00  
% 11.42/2.00  fof(f17,plain,(
% 11.42/2.00    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 11.42/2.00    inference(ennf_transformation,[],[f12])).
% 11.42/2.00  
% 11.42/2.00  fof(f40,plain,(
% 11.42/2.00    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK7(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK7(X0),X0)))),
% 11.42/2.00    introduced(choice_axiom,[])).
% 11.42/2.00  
% 11.42/2.00  fof(f41,plain,(
% 11.42/2.00    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK7(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK7(X0),X0)) | k1_xboole_0 = X0)),
% 11.42/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f17,f40])).
% 11.42/2.00  
% 11.42/2.00  fof(f73,plain,(
% 11.42/2.00    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 11.42/2.00    inference(cnf_transformation,[],[f41])).
% 11.42/2.00  
% 11.42/2.00  fof(f3,axiom,(
% 11.42/2.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 11.42/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.00  
% 11.42/2.00  fof(f19,plain,(
% 11.42/2.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 11.42/2.00    inference(nnf_transformation,[],[f3])).
% 11.42/2.00  
% 11.42/2.00  fof(f20,plain,(
% 11.42/2.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 11.42/2.00    inference(flattening,[],[f19])).
% 11.42/2.00  
% 11.42/2.00  fof(f21,plain,(
% 11.42/2.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 11.42/2.00    inference(rectify,[],[f20])).
% 11.42/2.00  
% 11.42/2.00  fof(f22,plain,(
% 11.42/2.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.42/2.00    introduced(choice_axiom,[])).
% 11.42/2.00  
% 11.42/2.00  fof(f23,plain,(
% 11.42/2.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 11.42/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 11.42/2.00  
% 11.42/2.00  fof(f47,plain,(
% 11.42/2.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 11.42/2.00    inference(cnf_transformation,[],[f23])).
% 11.42/2.00  
% 11.42/2.00  fof(f87,plain,(
% 11.42/2.00    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 11.42/2.00    inference(equality_resolution,[],[f47])).
% 11.42/2.00  
% 11.42/2.00  fof(f48,plain,(
% 11.42/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 11.42/2.00    inference(cnf_transformation,[],[f23])).
% 11.42/2.00  
% 11.42/2.00  fof(f85,plain,(
% 11.42/2.00    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 11.42/2.00    inference(equality_resolution,[],[f48])).
% 11.42/2.00  
% 11.42/2.00  fof(f86,plain,(
% 11.42/2.00    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 11.42/2.00    inference(equality_resolution,[],[f85])).
% 11.42/2.00  
% 11.42/2.00  fof(f13,conjecture,(
% 11.42/2.00    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 11.42/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.00  
% 11.42/2.00  fof(f14,negated_conjecture,(
% 11.42/2.00    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 11.42/2.00    inference(negated_conjecture,[],[f13])).
% 11.42/2.00  
% 11.42/2.00  fof(f18,plain,(
% 11.42/2.00    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 11.42/2.00    inference(ennf_transformation,[],[f14])).
% 11.42/2.00  
% 11.42/2.00  fof(f43,plain,(
% 11.42/2.00    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK9,sK10) = X0) )),
% 11.42/2.00    introduced(choice_axiom,[])).
% 11.42/2.00  
% 11.42/2.00  fof(f42,plain,(
% 11.42/2.00    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK8) = sK8 | k1_mcart_1(sK8) = sK8) & ? [X2,X1] : k4_tarski(X1,X2) = sK8)),
% 11.42/2.00    introduced(choice_axiom,[])).
% 11.42/2.00  
% 11.42/2.00  fof(f44,plain,(
% 11.42/2.00    (k2_mcart_1(sK8) = sK8 | k1_mcart_1(sK8) = sK8) & k4_tarski(sK9,sK10) = sK8),
% 11.42/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f18,f43,f42])).
% 11.42/2.00  
% 11.42/2.00  fof(f76,plain,(
% 11.42/2.00    k4_tarski(sK9,sK10) = sK8),
% 11.42/2.00    inference(cnf_transformation,[],[f44])).
% 11.42/2.00  
% 11.42/2.00  fof(f74,plain,(
% 11.42/2.00    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK7(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 11.42/2.00    inference(cnf_transformation,[],[f41])).
% 11.42/2.00  
% 11.42/2.00  fof(f77,plain,(
% 11.42/2.00    k2_mcart_1(sK8) = sK8 | k1_mcart_1(sK8) = sK8),
% 11.42/2.00    inference(cnf_transformation,[],[f44])).
% 11.42/2.00  
% 11.42/2.00  fof(f11,axiom,(
% 11.42/2.00    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 11.42/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.00  
% 11.42/2.00  fof(f71,plain,(
% 11.42/2.00    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 11.42/2.00    inference(cnf_transformation,[],[f11])).
% 11.42/2.00  
% 11.42/2.00  fof(f72,plain,(
% 11.42/2.00    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 11.42/2.00    inference(cnf_transformation,[],[f11])).
% 11.42/2.00  
% 11.42/2.00  fof(f75,plain,(
% 11.42/2.00    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK7(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 11.42/2.00    inference(cnf_transformation,[],[f41])).
% 11.42/2.00  
% 11.42/2.00  fof(f8,axiom,(
% 11.42/2.00    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 11.42/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.00  
% 11.42/2.00  fof(f61,plain,(
% 11.42/2.00    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 11.42/2.00    inference(cnf_transformation,[],[f8])).
% 11.42/2.00  
% 11.42/2.00  fof(f4,axiom,(
% 11.42/2.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.42/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.00  
% 11.42/2.00  fof(f53,plain,(
% 11.42/2.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.42/2.00    inference(cnf_transformation,[],[f4])).
% 11.42/2.00  
% 11.42/2.00  fof(f82,plain,(
% 11.42/2.00    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2))) )),
% 11.42/2.00    inference(definition_unfolding,[],[f61,f53])).
% 11.42/2.00  
% 11.42/2.00  fof(f7,axiom,(
% 11.42/2.00    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 11.42/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.00  
% 11.42/2.00  fof(f26,plain,(
% 11.42/2.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | (X1 != X3 | X0 != X2)) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 11.42/2.00    inference(nnf_transformation,[],[f7])).
% 11.42/2.00  
% 11.42/2.00  fof(f27,plain,(
% 11.42/2.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 11.42/2.00    inference(flattening,[],[f26])).
% 11.42/2.00  
% 11.42/2.00  fof(f60,plain,(
% 11.42/2.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) )),
% 11.42/2.00    inference(cnf_transformation,[],[f27])).
% 11.42/2.00  
% 11.42/2.00  fof(f78,plain,(
% 11.42/2.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X2,X2),k2_tarski(X3,X3))) | X1 != X3 | X0 != X2) )),
% 11.42/2.00    inference(definition_unfolding,[],[f60,f53,f53])).
% 11.42/2.00  
% 11.42/2.00  fof(f90,plain,(
% 11.42/2.00    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(k2_tarski(X2,X2),k2_tarski(X3,X3))) | X0 != X2) )),
% 11.42/2.00    inference(equality_resolution,[],[f78])).
% 11.42/2.00  
% 11.42/2.00  fof(f91,plain,(
% 11.42/2.00    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k2_tarski(X2,X2),k2_tarski(X3,X3)))) )),
% 11.42/2.00    inference(equality_resolution,[],[f90])).
% 11.42/2.00  
% 11.42/2.00  fof(f1,axiom,(
% 11.42/2.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.42/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.00  
% 11.42/2.00  fof(f15,plain,(
% 11.42/2.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 11.42/2.00    inference(unused_predicate_definition_removal,[],[f1])).
% 11.42/2.00  
% 11.42/2.00  fof(f16,plain,(
% 11.42/2.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 11.42/2.00    inference(ennf_transformation,[],[f15])).
% 11.42/2.00  
% 11.42/2.00  fof(f45,plain,(
% 11.42/2.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 11.42/2.00    inference(cnf_transformation,[],[f16])).
% 11.42/2.00  
% 11.42/2.00  fof(f2,axiom,(
% 11.42/2.00    v1_xboole_0(k1_xboole_0)),
% 11.42/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.00  
% 11.42/2.00  fof(f46,plain,(
% 11.42/2.00    v1_xboole_0(k1_xboole_0)),
% 11.42/2.00    inference(cnf_transformation,[],[f2])).
% 11.42/2.00  
% 11.42/2.00  cnf(c_29,plain,
% 11.42/2.00      ( r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0 ),
% 11.42/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53240,plain,
% 11.42/2.00      ( k1_xboole_0 = X0 | r2_hidden(sK7(X0),X0) = iProver_top ),
% 11.42/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_7,plain,
% 11.42/2.00      ( ~ r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X2 ),
% 11.42/2.00      inference(cnf_transformation,[],[f87]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53247,plain,
% 11.42/2.00      ( X0 = X1 | X0 = X2 | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
% 11.42/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53547,plain,
% 11.42/2.00      ( k2_tarski(X0,X1) = k1_xboole_0
% 11.42/2.00      | sK7(k2_tarski(X0,X1)) = X0
% 11.42/2.00      | sK7(k2_tarski(X0,X1)) = X1 ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_53240,c_53247]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53820,plain,
% 11.42/2.00      ( k2_tarski(X0,X1) = k1_xboole_0
% 11.42/2.00      | sK7(k2_tarski(X0,X1)) = X1
% 11.42/2.00      | r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_53547,c_53240]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_6,plain,
% 11.42/2.00      ( r2_hidden(X0,k2_tarski(X0,X1)) ),
% 11.42/2.00      inference(cnf_transformation,[],[f86]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_84,plain,
% 11.42/2.00      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 11.42/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_54253,plain,
% 11.42/2.00      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 11.42/2.00      inference(global_propositional_subsumption,[status(thm)],[c_53820,c_84]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_31,negated_conjecture,
% 11.42/2.00      ( k4_tarski(sK9,sK10) = sK8 ),
% 11.42/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_28,plain,
% 11.42/2.00      ( ~ r2_hidden(X0,X1) | k4_tarski(X0,X2) != sK7(X1) | k1_xboole_0 = X1 ),
% 11.42/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53241,plain,
% 11.42/2.00      ( k4_tarski(X0,X1) != sK7(X2)
% 11.42/2.00      | k1_xboole_0 = X2
% 11.42/2.00      | r2_hidden(X0,X2) != iProver_top ),
% 11.42/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53513,plain,
% 11.42/2.00      ( sK7(X0) != sK8 | k1_xboole_0 = X0 | r2_hidden(sK9,X0) != iProver_top ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_31,c_53241]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53812,plain,
% 11.42/2.00      ( k2_tarski(X0,X1) = k1_xboole_0
% 11.42/2.00      | sK7(k2_tarski(X0,X1)) = X0
% 11.42/2.00      | sK8 != X1
% 11.42/2.00      | r2_hidden(sK9,k2_tarski(X0,X1)) != iProver_top ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_53547,c_53513]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53976,plain,
% 11.42/2.00      ( k2_tarski(X0,sK8) = k1_xboole_0
% 11.42/2.00      | sK7(k2_tarski(X0,sK8)) = X0
% 11.42/2.00      | r2_hidden(sK9,k2_tarski(X0,sK8)) != iProver_top ),
% 11.42/2.00      inference(equality_resolution,[status(thm)],[c_53812]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_54321,plain,
% 11.42/2.00      ( k2_tarski(sK9,sK8) = k1_xboole_0 | sK7(k2_tarski(sK9,sK8)) = sK9 ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_54253,c_53976]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_30,negated_conjecture,
% 11.42/2.00      ( k1_mcart_1(sK8) = sK8 | k2_mcart_1(sK8) = sK8 ),
% 11.42/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_26,plain,
% 11.42/2.00      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 11.42/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53381,plain,
% 11.42/2.00      ( k1_mcart_1(sK8) = sK9 ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_31,c_26]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53433,plain,
% 11.42/2.00      ( k2_mcart_1(sK8) = sK8 | sK9 = sK8 ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_30,c_53381]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_25,plain,
% 11.42/2.00      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 11.42/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53358,plain,
% 11.42/2.00      ( k2_mcart_1(sK8) = sK10 ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_31,c_25]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53435,plain,
% 11.42/2.00      ( sK10 = sK8 | sK9 = sK8 ),
% 11.42/2.00      inference(demodulation,[status(thm)],[c_53433,c_53358]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_27,plain,
% 11.42/2.00      ( ~ r2_hidden(X0,X1) | k4_tarski(X2,X0) != sK7(X1) | k1_xboole_0 = X1 ),
% 11.42/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53242,plain,
% 11.42/2.00      ( k4_tarski(X0,X1) != sK7(X2)
% 11.42/2.00      | k1_xboole_0 = X2
% 11.42/2.00      | r2_hidden(X1,X2) != iProver_top ),
% 11.42/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53634,plain,
% 11.42/2.00      ( sK7(X0) != sK8 | k1_xboole_0 = X0 | r2_hidden(sK10,X0) != iProver_top ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_31,c_53242]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53818,plain,
% 11.42/2.00      ( k2_tarski(X0,X1) = k1_xboole_0
% 11.42/2.00      | sK7(k2_tarski(X0,X1)) = X1
% 11.42/2.00      | sK8 != X0
% 11.42/2.00      | r2_hidden(sK10,k2_tarski(X0,X1)) != iProver_top ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_53547,c_53634]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53990,plain,
% 11.42/2.00      ( k2_tarski(sK8,X0) = k1_xboole_0
% 11.42/2.00      | sK7(k2_tarski(sK8,X0)) = X0
% 11.42/2.00      | r2_hidden(sK10,k2_tarski(sK8,X0)) != iProver_top ),
% 11.42/2.00      inference(equality_resolution,[status(thm)],[c_53818]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_54332,plain,
% 11.42/2.00      ( k2_tarski(sK8,X0) = k1_xboole_0
% 11.42/2.00      | sK7(k2_tarski(sK8,X0)) = X0
% 11.42/2.00      | sK9 = sK8
% 11.42/2.00      | r2_hidden(sK8,k2_tarski(sK8,X0)) != iProver_top ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_53435,c_53990]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_54367,plain,
% 11.42/2.00      ( k2_tarski(sK8,X0) = k1_xboole_0
% 11.42/2.00      | sK7(k2_tarski(sK8,X0)) = X0
% 11.42/2.00      | sK9 = sK8 ),
% 11.42/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_54332,c_54253]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_54372,plain,
% 11.42/2.00      ( k2_tarski(sK8,X0) = k1_xboole_0
% 11.42/2.00      | sK9 = sK8
% 11.42/2.00      | sK8 != X0
% 11.42/2.00      | r2_hidden(sK9,k2_tarski(sK8,X0)) != iProver_top ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_54367,c_53513]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_54462,plain,
% 11.42/2.00      ( k2_tarski(sK8,sK8) = k1_xboole_0
% 11.42/2.00      | sK9 = sK8
% 11.42/2.00      | r2_hidden(sK9,k2_tarski(sK8,sK8)) != iProver_top ),
% 11.42/2.00      inference(equality_resolution,[status(thm)],[c_54372]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_16,plain,
% 11.42/2.00      ( k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
% 11.42/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_12,plain,
% 11.42/2.00      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X1))) ),
% 11.42/2.00      inference(cnf_transformation,[],[f91]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_2945,plain,
% 11.42/2.00      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X1))) = iProver_top ),
% 11.42/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_2965,plain,
% 11.42/2.00      ( r2_hidden(k4_tarski(X0,X1),k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X1))) = iProver_top ),
% 11.42/2.00      inference(demodulation,[status(thm)],[c_16,c_2945]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_3019,plain,
% 11.42/2.00      ( r2_hidden(sK8,k2_tarski(sK8,sK8)) = iProver_top ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_31,c_2965]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_54371,plain,
% 11.42/2.00      ( k2_tarski(sK8,X0) = k1_xboole_0
% 11.42/2.00      | sK9 = sK8
% 11.42/2.00      | sK8 != X0
% 11.42/2.00      | r2_hidden(sK10,k2_tarski(sK8,X0)) != iProver_top ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_54367,c_53634]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_54450,plain,
% 11.42/2.00      ( k2_tarski(sK8,sK8) = k1_xboole_0
% 11.42/2.00      | sK9 = sK8
% 11.42/2.00      | r2_hidden(sK10,k2_tarski(sK8,sK8)) != iProver_top ),
% 11.42/2.00      inference(equality_resolution,[status(thm)],[c_54371]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_54593,plain,
% 11.42/2.00      ( k2_tarski(sK8,sK8) = k1_xboole_0
% 11.42/2.00      | sK9 = sK8
% 11.42/2.00      | r2_hidden(sK8,k2_tarski(sK8,sK8)) != iProver_top ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_53435,c_54450]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_54606,plain,
% 11.42/2.00      ( sK9 = sK8 | k2_tarski(sK8,sK8) = k1_xboole_0 ),
% 11.42/2.00      inference(global_propositional_subsumption,
% 11.42/2.00                [status(thm)],
% 11.42/2.00                [c_54462,c_3019,c_54593]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_54607,plain,
% 11.42/2.00      ( k2_tarski(sK8,sK8) = k1_xboole_0 | sK9 = sK8 ),
% 11.42/2.00      inference(renaming,[status(thm)],[c_54606]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53245,plain,
% 11.42/2.00      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X1))) = iProver_top ),
% 11.42/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53282,plain,
% 11.42/2.00      ( r2_hidden(k4_tarski(X0,X1),k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X1))) = iProver_top ),
% 11.42/2.00      inference(demodulation,[status(thm)],[c_16,c_53245]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53517,plain,
% 11.42/2.00      ( r2_hidden(sK8,k2_tarski(sK8,sK8)) = iProver_top ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_31,c_53282]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_54627,plain,
% 11.42/2.00      ( sK9 = sK8 | r2_hidden(sK8,k1_xboole_0) = iProver_top ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_54607,c_53517]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_0,negated_conjecture,
% 11.42/2.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.42/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_1,plain,
% 11.42/2.00      ( v1_xboole_0(k1_xboole_0) ),
% 11.42/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_275,plain,
% 11.42/2.00      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 11.42/2.00      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_276,plain,
% 11.42/2.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 11.42/2.00      inference(unflattening,[status(thm)],[c_275]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_53238,plain,
% 11.42/2.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.42/2.00      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_54711,plain,
% 11.42/2.00      ( sK9 = sK8 ),
% 11.42/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_54627,c_53238]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_55290,plain,
% 11.42/2.00      ( k2_tarski(sK8,sK8) = k1_xboole_0 | sK7(k2_tarski(sK8,sK8)) = sK8 ),
% 11.42/2.00      inference(light_normalisation,[status(thm)],[c_54321,c_54711]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_55295,plain,
% 11.42/2.00      ( k2_tarski(sK8,sK8) = k1_xboole_0
% 11.42/2.00      | r2_hidden(sK10,k2_tarski(sK8,sK8)) != iProver_top ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_55290,c_53634]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_54739,plain,
% 11.42/2.00      ( sK7(X0) != sK8 | k1_xboole_0 = X0 | r2_hidden(sK8,X0) != iProver_top ),
% 11.42/2.00      inference(demodulation,[status(thm)],[c_54711,c_53513]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_55294,plain,
% 11.42/2.00      ( k2_tarski(sK8,sK8) = k1_xboole_0
% 11.42/2.00      | r2_hidden(sK8,k2_tarski(sK8,sK8)) != iProver_top ),
% 11.42/2.00      inference(superposition,[status(thm)],[c_55290,c_54739]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_55336,plain,
% 11.42/2.00      ( k2_tarski(sK8,sK8) = k1_xboole_0 ),
% 11.42/2.00      inference(global_propositional_subsumption,
% 11.42/2.00                [status(thm)],
% 11.42/2.00                [c_55295,c_3019,c_55294]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_55346,plain,
% 11.42/2.00      ( r2_hidden(sK8,k1_xboole_0) = iProver_top ),
% 11.42/2.00      inference(demodulation,[status(thm)],[c_55336,c_53517]) ).
% 11.42/2.00  
% 11.42/2.00  cnf(c_55411,plain,
% 11.42/2.00      ( $false ),
% 11.42/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_55346,c_53238]) ).
% 11.42/2.00  
% 11.42/2.00  
% 11.42/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.42/2.00  
% 11.42/2.00  ------                               Statistics
% 11.42/2.00  
% 11.42/2.00  ------ Selected
% 11.42/2.00  
% 11.42/2.00  total_time:                             1.029
% 11.42/2.00  
%------------------------------------------------------------------------------
