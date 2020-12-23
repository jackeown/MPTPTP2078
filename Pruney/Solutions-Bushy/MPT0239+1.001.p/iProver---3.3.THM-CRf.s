%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0239+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:48 EST 2020

% Result     : Theorem 1.18s
% Output     : CNFRefutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 176 expanded)
%              Number of clauses        :   31 (  48 expanded)
%              Number of leaves         :    5 (  33 expanded)
%              Depth                    :   17
%              Number of atoms          :  178 ( 785 expanded)
%              Number of equality atoms :  102 ( 436 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f10])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      <=> ( X1 = X3
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <~> ( X1 = X3
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
      & ( ( X1 = X3
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
      & ( ( X1 = X3
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
        & ( ( X1 = X3
            & X0 = X2 )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) )
   => ( ( sK2 != sK4
        | sK1 != sK3
        | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),k1_tarski(sK4))) )
      & ( ( sK2 = sK4
          & sK1 = sK3 )
        | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),k1_tarski(sK4))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ( sK2 != sK4
      | sK1 != sK3
      | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),k1_tarski(sK4))) )
    & ( ( sK2 = sK4
        & sK1 = sK3 )
      | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),k1_tarski(sK4))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f14])).

fof(f24,plain,
    ( sK2 = sK4
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f15])).

fof(f23,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f7,plain,(
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
    inference(rectify,[],[f6])).

fof(f8,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f8])).

fof(f16,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,
    ( sK2 != sK4
    | sK1 != sK3
    | ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f17])).

fof(f27,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f26])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_295,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),k1_tarski(sK4)))
    | sK2 = sK4 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_291,plain,
    ( sK2 = sK4
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),k1_tarski(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),k1_tarski(sK4)))
    | sK1 = sK3 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_290,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),k1_tarski(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_367,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK3))
    | sK1 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_373,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),k1_tarski(sK4)))
    | r2_hidden(sK1,k1_tarski(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_386,plain,
    ( sK1 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_290,c_9,c_367,c_373])).

cnf(c_412,plain,
    ( sK4 = sK2
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK4))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_291,c_386])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_294,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_574,plain,
    ( sK4 = sK2
    | r2_hidden(sK2,k1_tarski(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_412,c_294])).

cnf(c_296,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_796,plain,
    ( sK4 = sK2 ),
    inference(superposition,[status(thm)],[c_574,c_296])).

cnf(c_7,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),k1_tarski(sK4)))
    | sK1 != sK3
    | sK2 != sK4 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_292,plain,
    ( sK1 != sK3
    | sK2 != sK4
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),k1_tarski(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_12,plain,
    ( sK1 != sK3
    | sK2 != sK4
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),k1_tarski(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_379,plain,
    ( sK2 != sK4
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK3),k1_tarski(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_9,c_12,c_367,c_373])).

cnf(c_389,plain,
    ( sK4 != sK2
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_386,c_379])).

cnf(c_873,plain,
    ( sK2 != sK2
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_796,c_389])).

cnf(c_875,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_873])).

cnf(c_878,plain,
    ( r2_hidden(sK1,k1_tarski(sK1)) != iProver_top
    | r2_hidden(sK2,k1_tarski(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_295,c_875])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_23,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_25,plain,
    ( r2_hidden(sK1,k1_tarski(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1140,plain,
    ( r2_hidden(sK2,k1_tarski(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_878,c_25])).

cnf(c_297,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1145,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1140,c_297])).


%------------------------------------------------------------------------------
