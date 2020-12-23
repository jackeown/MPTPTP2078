%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:39 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   62 (1692 expanded)
%              Number of clauses        :   27 ( 284 expanded)
%              Number of leaves         :   10 ( 560 expanded)
%              Depth                    :   16
%              Number of atoms          :  173 (2451 expanded)
%              Number of equality atoms :  138 (2210 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k3_relat_1(k2_enumset1(k4_tarski(X0,X0),k4_tarski(X0,X0),k4_tarski(X0,X0),k4_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f28,f24,f24])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f24])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))),k3_relat_1(k2_enumset1(k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3)))) ),
    inference(definition_unfolding,[],[f25,f35,f35])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))),k2_enumset1(X2,X2,X2,X2)) = k3_relat_1(k2_enumset1(k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)))) ),
    inference(definition_unfolding,[],[f27,f35,f35,f24])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
     => ( k2_mcart_1(X0) = X3
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
       => ( k2_mcart_1(X0) = X3
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) != X3
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( k2_mcart_1(X0) != X3
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) )
   => ( ( k2_mcart_1(sK1) != sK4
        | ( k1_mcart_1(sK1) != sK3
          & k1_mcart_1(sK1) != sK2 ) )
      & r2_hidden(sK1,k2_zfmisc_1(k2_tarski(sK2,sK3),k1_tarski(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ( k2_mcart_1(sK1) != sK4
      | ( k1_mcart_1(sK1) != sK3
        & k1_mcart_1(sK1) != sK2 ) )
    & r2_hidden(sK1,k2_zfmisc_1(k2_tarski(sK2,sK3),k1_tarski(sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f10,f16])).

fof(f32,plain,(
    r2_hidden(sK1,k2_zfmisc_1(k2_tarski(sK2,sK3),k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    r2_hidden(sK1,k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(sK2,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3))),k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(definition_unfolding,[],[f32,f35,f24])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f18,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f18,f35])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)))) ) ),
    inference(equality_resolution,[],[f41])).

fof(f33,plain,
    ( k2_mcart_1(sK1) != sK4
    | k1_mcart_1(sK1) != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,
    ( k2_mcart_1(sK1) != sK4
    | k1_mcart_1(sK1) != sK3 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_9,plain,
    ( k3_relat_1(k2_enumset1(k4_tarski(X0,X0),k4_tarski(X0,X0),k4_tarski(X0,X0),k4_tarski(X0,X0))) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))),k3_relat_1(k2_enumset1(k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3)))) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_792,plain,
    ( k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_6])).

cnf(c_7,plain,
    ( k3_relat_1(k2_enumset1(k4_tarski(k4_tarski(X0,X1),k4_tarski(X2,X1)),k4_tarski(k4_tarski(X0,X1),k4_tarski(X2,X1)),k4_tarski(k4_tarski(X0,X1),k4_tarski(X2,X1)),k4_tarski(k4_tarski(X0,X1),k4_tarski(X2,X1)))) = k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2))),k2_enumset1(X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_949,plain,
    ( k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X0),k4_tarski(X0,X0),k4_tarski(X0,X0),k4_tarski(X0,X0))),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7,c_9])).

cnf(c_951,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ),
    inference(light_normalisation,[status(thm)],[c_949,c_9])).

cnf(c_3090,plain,
    ( k2_zfmisc_1(k3_relat_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_792,c_951])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK1,k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(sK2,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3))),k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_381,plain,
    ( r2_hidden(sK1,k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(sK2,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3))),k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1276,plain,
    ( r2_hidden(sK1,k2_zfmisc_1(k3_relat_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))),k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_951,c_381])).

cnf(c_3094,plain,
    ( r2_hidden(sK1,k2_enumset1(k4_tarski(sK2,sK4),k4_tarski(sK2,sK4),k4_tarski(sK3,sK4),k4_tarski(sK3,sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3090,c_1276])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k3_relat_1(k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2))))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_382,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k3_relat_1(k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_947,plain,
    ( k4_tarski(X0,X1) = X2
    | k4_tarski(X3,X1) = X2
    | r2_hidden(X2,k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X3),k4_tarski(X0,X3),k4_tarski(X0,X3),k4_tarski(X0,X3))),k2_enumset1(X1,X1,X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_382])).

cnf(c_3119,plain,
    ( k4_tarski(X0,X1) = X2
    | k4_tarski(X3,X1) = X2
    | r2_hidden(X2,k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X3,X1),k4_tarski(X3,X1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_947,c_951,c_3090])).

cnf(c_3664,plain,
    ( k4_tarski(sK2,sK4) = sK1
    | k4_tarski(sK3,sK4) = sK1 ),
    inference(superposition,[status(thm)],[c_3094,c_3119])).

cnf(c_3682,plain,
    ( k4_tarski(sK3,sK4) = sK1
    | r2_hidden(sK1,k2_enumset1(sK1,sK1,k4_tarski(sK3,sK4),k4_tarski(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3664,c_3094])).

cnf(c_13,negated_conjecture,
    ( k1_mcart_1(sK1) != sK2
    | k2_mcart_1(sK1) != sK4 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3677,plain,
    ( k4_tarski(sK3,sK4) = sK1
    | k1_mcart_1(sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_3664,c_11])).

cnf(c_10,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3678,plain,
    ( k4_tarski(sK3,sK4) = sK1
    | k2_mcart_1(sK1) = sK4 ),
    inference(superposition,[status(thm)],[c_3664,c_10])).

cnf(c_4035,plain,
    ( k4_tarski(sK3,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3682,c_13,c_3677,c_3678])).

cnf(c_4051,plain,
    ( k2_mcart_1(sK1) = sK4 ),
    inference(superposition,[status(thm)],[c_4035,c_10])).

cnf(c_4050,plain,
    ( k1_mcart_1(sK1) = sK3 ),
    inference(superposition,[status(thm)],[c_4035,c_11])).

cnf(c_12,negated_conjecture,
    ( k1_mcart_1(sK1) != sK3
    | k2_mcart_1(sK1) != sK4 ),
    inference(cnf_transformation,[],[f34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4051,c_4050,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:45:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.65/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/0.92  
% 2.65/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.65/0.92  
% 2.65/0.92  ------  iProver source info
% 2.65/0.92  
% 2.65/0.92  git: date: 2020-06-30 10:37:57 +0100
% 2.65/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.65/0.92  git: non_committed_changes: false
% 2.65/0.92  git: last_make_outside_of_git: false
% 2.65/0.92  
% 2.65/0.92  ------ 
% 2.65/0.92  
% 2.65/0.92  ------ Input Options
% 2.65/0.92  
% 2.65/0.92  --out_options                           all
% 2.65/0.92  --tptp_safe_out                         true
% 2.65/0.92  --problem_path                          ""
% 2.65/0.92  --include_path                          ""
% 2.65/0.92  --clausifier                            res/vclausify_rel
% 2.65/0.92  --clausifier_options                    --mode clausify
% 2.65/0.92  --stdin                                 false
% 2.65/0.92  --stats_out                             all
% 2.65/0.92  
% 2.65/0.92  ------ General Options
% 2.65/0.92  
% 2.65/0.92  --fof                                   false
% 2.65/0.92  --time_out_real                         305.
% 2.65/0.92  --time_out_virtual                      -1.
% 2.65/0.92  --symbol_type_check                     false
% 2.65/0.92  --clausify_out                          false
% 2.65/0.92  --sig_cnt_out                           false
% 2.65/0.92  --trig_cnt_out                          false
% 2.65/0.92  --trig_cnt_out_tolerance                1.
% 2.65/0.92  --trig_cnt_out_sk_spl                   false
% 2.65/0.92  --abstr_cl_out                          false
% 2.65/0.92  
% 2.65/0.92  ------ Global Options
% 2.65/0.92  
% 2.65/0.92  --schedule                              default
% 2.65/0.92  --add_important_lit                     false
% 2.65/0.92  --prop_solver_per_cl                    1000
% 2.65/0.92  --min_unsat_core                        false
% 2.65/0.92  --soft_assumptions                      false
% 2.65/0.92  --soft_lemma_size                       3
% 2.65/0.92  --prop_impl_unit_size                   0
% 2.65/0.92  --prop_impl_unit                        []
% 2.65/0.92  --share_sel_clauses                     true
% 2.65/0.92  --reset_solvers                         false
% 2.65/0.92  --bc_imp_inh                            [conj_cone]
% 2.65/0.92  --conj_cone_tolerance                   3.
% 2.65/0.92  --extra_neg_conj                        none
% 2.65/0.92  --large_theory_mode                     true
% 2.65/0.92  --prolific_symb_bound                   200
% 2.65/0.92  --lt_threshold                          2000
% 2.65/0.92  --clause_weak_htbl                      true
% 2.65/0.92  --gc_record_bc_elim                     false
% 2.65/0.92  
% 2.65/0.92  ------ Preprocessing Options
% 2.65/0.92  
% 2.65/0.92  --preprocessing_flag                    true
% 2.65/0.92  --time_out_prep_mult                    0.1
% 2.65/0.92  --splitting_mode                        input
% 2.65/0.92  --splitting_grd                         true
% 2.65/0.92  --splitting_cvd                         false
% 2.65/0.92  --splitting_cvd_svl                     false
% 2.65/0.92  --splitting_nvd                         32
% 2.65/0.92  --sub_typing                            true
% 2.65/0.92  --prep_gs_sim                           true
% 2.65/0.92  --prep_unflatten                        true
% 2.65/0.92  --prep_res_sim                          true
% 2.65/0.92  --prep_upred                            true
% 2.65/0.92  --prep_sem_filter                       exhaustive
% 2.65/0.92  --prep_sem_filter_out                   false
% 2.65/0.92  --pred_elim                             true
% 2.65/0.92  --res_sim_input                         true
% 2.65/0.92  --eq_ax_congr_red                       true
% 2.65/0.92  --pure_diseq_elim                       true
% 2.65/0.92  --brand_transform                       false
% 2.65/0.92  --non_eq_to_eq                          false
% 2.65/0.92  --prep_def_merge                        true
% 2.65/0.92  --prep_def_merge_prop_impl              false
% 2.65/0.92  --prep_def_merge_mbd                    true
% 2.65/0.92  --prep_def_merge_tr_red                 false
% 2.65/0.92  --prep_def_merge_tr_cl                  false
% 2.65/0.92  --smt_preprocessing                     true
% 2.65/0.92  --smt_ac_axioms                         fast
% 2.65/0.92  --preprocessed_out                      false
% 2.65/0.92  --preprocessed_stats                    false
% 2.65/0.92  
% 2.65/0.92  ------ Abstraction refinement Options
% 2.65/0.92  
% 2.65/0.92  --abstr_ref                             []
% 2.65/0.92  --abstr_ref_prep                        false
% 2.65/0.92  --abstr_ref_until_sat                   false
% 2.65/0.92  --abstr_ref_sig_restrict                funpre
% 2.65/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/0.92  --abstr_ref_under                       []
% 2.65/0.92  
% 2.65/0.92  ------ SAT Options
% 2.65/0.92  
% 2.65/0.92  --sat_mode                              false
% 2.65/0.92  --sat_fm_restart_options                ""
% 2.65/0.92  --sat_gr_def                            false
% 2.65/0.92  --sat_epr_types                         true
% 2.65/0.92  --sat_non_cyclic_types                  false
% 2.65/0.92  --sat_finite_models                     false
% 2.65/0.92  --sat_fm_lemmas                         false
% 2.65/0.92  --sat_fm_prep                           false
% 2.65/0.92  --sat_fm_uc_incr                        true
% 2.65/0.92  --sat_out_model                         small
% 2.65/0.92  --sat_out_clauses                       false
% 2.65/0.92  
% 2.65/0.92  ------ QBF Options
% 2.65/0.92  
% 2.65/0.92  --qbf_mode                              false
% 2.65/0.92  --qbf_elim_univ                         false
% 2.65/0.92  --qbf_dom_inst                          none
% 2.65/0.92  --qbf_dom_pre_inst                      false
% 2.65/0.92  --qbf_sk_in                             false
% 2.65/0.92  --qbf_pred_elim                         true
% 2.65/0.92  --qbf_split                             512
% 2.65/0.92  
% 2.65/0.92  ------ BMC1 Options
% 2.65/0.92  
% 2.65/0.92  --bmc1_incremental                      false
% 2.65/0.92  --bmc1_axioms                           reachable_all
% 2.65/0.92  --bmc1_min_bound                        0
% 2.65/0.92  --bmc1_max_bound                        -1
% 2.65/0.92  --bmc1_max_bound_default                -1
% 2.65/0.92  --bmc1_symbol_reachability              true
% 2.65/0.92  --bmc1_property_lemmas                  false
% 2.65/0.92  --bmc1_k_induction                      false
% 2.65/0.92  --bmc1_non_equiv_states                 false
% 2.65/0.92  --bmc1_deadlock                         false
% 2.65/0.92  --bmc1_ucm                              false
% 2.65/0.92  --bmc1_add_unsat_core                   none
% 2.65/0.92  --bmc1_unsat_core_children              false
% 2.65/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/0.92  --bmc1_out_stat                         full
% 2.65/0.92  --bmc1_ground_init                      false
% 2.65/0.92  --bmc1_pre_inst_next_state              false
% 2.65/0.92  --bmc1_pre_inst_state                   false
% 2.65/0.92  --bmc1_pre_inst_reach_state             false
% 2.65/0.92  --bmc1_out_unsat_core                   false
% 2.65/0.92  --bmc1_aig_witness_out                  false
% 2.65/0.92  --bmc1_verbose                          false
% 2.65/0.92  --bmc1_dump_clauses_tptp                false
% 2.65/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.65/0.92  --bmc1_dump_file                        -
% 2.65/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.65/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.65/0.92  --bmc1_ucm_extend_mode                  1
% 2.65/0.92  --bmc1_ucm_init_mode                    2
% 2.65/0.92  --bmc1_ucm_cone_mode                    none
% 2.65/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.65/0.92  --bmc1_ucm_relax_model                  4
% 2.65/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.65/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/0.92  --bmc1_ucm_layered_model                none
% 2.65/0.92  --bmc1_ucm_max_lemma_size               10
% 2.65/0.92  
% 2.65/0.92  ------ AIG Options
% 2.65/0.92  
% 2.65/0.92  --aig_mode                              false
% 2.65/0.92  
% 2.65/0.92  ------ Instantiation Options
% 2.65/0.92  
% 2.65/0.92  --instantiation_flag                    true
% 2.65/0.92  --inst_sos_flag                         false
% 2.65/0.92  --inst_sos_phase                        true
% 2.65/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/0.92  --inst_lit_sel_side                     num_symb
% 2.65/0.92  --inst_solver_per_active                1400
% 2.65/0.92  --inst_solver_calls_frac                1.
% 2.65/0.92  --inst_passive_queue_type               priority_queues
% 2.65/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/0.92  --inst_passive_queues_freq              [25;2]
% 2.65/0.92  --inst_dismatching                      true
% 2.65/0.92  --inst_eager_unprocessed_to_passive     true
% 2.65/0.92  --inst_prop_sim_given                   true
% 2.65/0.92  --inst_prop_sim_new                     false
% 2.65/0.92  --inst_subs_new                         false
% 2.65/0.92  --inst_eq_res_simp                      false
% 2.65/0.92  --inst_subs_given                       false
% 2.65/0.92  --inst_orphan_elimination               true
% 2.65/0.92  --inst_learning_loop_flag               true
% 2.65/0.92  --inst_learning_start                   3000
% 2.65/0.92  --inst_learning_factor                  2
% 2.65/0.92  --inst_start_prop_sim_after_learn       3
% 2.65/0.92  --inst_sel_renew                        solver
% 2.65/0.92  --inst_lit_activity_flag                true
% 2.65/0.92  --inst_restr_to_given                   false
% 2.65/0.92  --inst_activity_threshold               500
% 2.65/0.92  --inst_out_proof                        true
% 2.65/0.92  
% 2.65/0.92  ------ Resolution Options
% 2.65/0.92  
% 2.65/0.92  --resolution_flag                       true
% 2.65/0.92  --res_lit_sel                           adaptive
% 2.65/0.92  --res_lit_sel_side                      none
% 2.65/0.92  --res_ordering                          kbo
% 2.65/0.92  --res_to_prop_solver                    active
% 2.65/0.92  --res_prop_simpl_new                    false
% 2.65/0.92  --res_prop_simpl_given                  true
% 2.65/0.92  --res_passive_queue_type                priority_queues
% 2.65/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/0.92  --res_passive_queues_freq               [15;5]
% 2.65/0.92  --res_forward_subs                      full
% 2.65/0.92  --res_backward_subs                     full
% 2.65/0.92  --res_forward_subs_resolution           true
% 2.65/0.92  --res_backward_subs_resolution          true
% 2.65/0.92  --res_orphan_elimination                true
% 2.65/0.92  --res_time_limit                        2.
% 2.65/0.92  --res_out_proof                         true
% 2.65/0.92  
% 2.65/0.92  ------ Superposition Options
% 2.65/0.92  
% 2.65/0.92  --superposition_flag                    true
% 2.65/0.92  --sup_passive_queue_type                priority_queues
% 2.65/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.65/0.92  --demod_completeness_check              fast
% 2.65/0.92  --demod_use_ground                      true
% 2.65/0.92  --sup_to_prop_solver                    passive
% 2.65/0.92  --sup_prop_simpl_new                    true
% 2.65/0.92  --sup_prop_simpl_given                  true
% 2.65/0.92  --sup_fun_splitting                     false
% 2.65/0.92  --sup_smt_interval                      50000
% 2.65/0.92  
% 2.65/0.92  ------ Superposition Simplification Setup
% 2.65/0.92  
% 2.65/0.92  --sup_indices_passive                   []
% 2.65/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.92  --sup_full_bw                           [BwDemod]
% 2.65/0.92  --sup_immed_triv                        [TrivRules]
% 2.65/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.92  --sup_immed_bw_main                     []
% 2.65/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.92  
% 2.65/0.92  ------ Combination Options
% 2.65/0.92  
% 2.65/0.92  --comb_res_mult                         3
% 2.65/0.92  --comb_sup_mult                         2
% 2.65/0.92  --comb_inst_mult                        10
% 2.65/0.92  
% 2.65/0.92  ------ Debug Options
% 2.65/0.92  
% 2.65/0.92  --dbg_backtrace                         false
% 2.65/0.92  --dbg_dump_prop_clauses                 false
% 2.65/0.92  --dbg_dump_prop_clauses_file            -
% 2.65/0.92  --dbg_out_stat                          false
% 2.65/0.92  ------ Parsing...
% 2.65/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.65/0.92  
% 2.65/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.65/0.92  
% 2.65/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.65/0.92  
% 2.65/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.65/0.92  ------ Proving...
% 2.65/0.92  ------ Problem Properties 
% 2.65/0.92  
% 2.65/0.92  
% 2.65/0.92  clauses                                 15
% 2.65/0.92  conjectures                             3
% 2.65/0.92  EPR                                     0
% 2.65/0.92  Horn                                    13
% 2.65/0.92  unary                                   9
% 2.65/0.92  binary                                  2
% 2.65/0.92  lits                                    26
% 2.65/0.92  lits eq                                 19
% 2.65/0.92  fd_pure                                 0
% 2.65/0.92  fd_pseudo                               0
% 2.65/0.92  fd_cond                                 0
% 2.65/0.92  fd_pseudo_cond                          3
% 2.65/0.92  AC symbols                              0
% 2.65/0.92  
% 2.65/0.92  ------ Schedule dynamic 5 is on 
% 2.65/0.92  
% 2.65/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.65/0.92  
% 2.65/0.92  
% 2.65/0.92  ------ 
% 2.65/0.92  Current options:
% 2.65/0.92  ------ 
% 2.65/0.92  
% 2.65/0.92  ------ Input Options
% 2.65/0.92  
% 2.65/0.92  --out_options                           all
% 2.65/0.92  --tptp_safe_out                         true
% 2.65/0.92  --problem_path                          ""
% 2.65/0.92  --include_path                          ""
% 2.65/0.92  --clausifier                            res/vclausify_rel
% 2.65/0.92  --clausifier_options                    --mode clausify
% 2.65/0.92  --stdin                                 false
% 2.65/0.92  --stats_out                             all
% 2.65/0.92  
% 2.65/0.92  ------ General Options
% 2.65/0.92  
% 2.65/0.92  --fof                                   false
% 2.65/0.92  --time_out_real                         305.
% 2.65/0.92  --time_out_virtual                      -1.
% 2.65/0.92  --symbol_type_check                     false
% 2.65/0.92  --clausify_out                          false
% 2.65/0.92  --sig_cnt_out                           false
% 2.65/0.92  --trig_cnt_out                          false
% 2.65/0.92  --trig_cnt_out_tolerance                1.
% 2.65/0.92  --trig_cnt_out_sk_spl                   false
% 2.65/0.92  --abstr_cl_out                          false
% 2.65/0.92  
% 2.65/0.92  ------ Global Options
% 2.65/0.92  
% 2.65/0.92  --schedule                              default
% 2.65/0.92  --add_important_lit                     false
% 2.65/0.92  --prop_solver_per_cl                    1000
% 2.65/0.92  --min_unsat_core                        false
% 2.65/0.92  --soft_assumptions                      false
% 2.65/0.92  --soft_lemma_size                       3
% 2.65/0.92  --prop_impl_unit_size                   0
% 2.65/0.92  --prop_impl_unit                        []
% 2.65/0.92  --share_sel_clauses                     true
% 2.65/0.92  --reset_solvers                         false
% 2.65/0.92  --bc_imp_inh                            [conj_cone]
% 2.65/0.92  --conj_cone_tolerance                   3.
% 2.65/0.92  --extra_neg_conj                        none
% 2.65/0.92  --large_theory_mode                     true
% 2.65/0.92  --prolific_symb_bound                   200
% 2.65/0.92  --lt_threshold                          2000
% 2.65/0.92  --clause_weak_htbl                      true
% 2.65/0.92  --gc_record_bc_elim                     false
% 2.65/0.92  
% 2.65/0.92  ------ Preprocessing Options
% 2.65/0.92  
% 2.65/0.92  --preprocessing_flag                    true
% 2.65/0.92  --time_out_prep_mult                    0.1
% 2.65/0.92  --splitting_mode                        input
% 2.65/0.92  --splitting_grd                         true
% 2.65/0.92  --splitting_cvd                         false
% 2.65/0.92  --splitting_cvd_svl                     false
% 2.65/0.92  --splitting_nvd                         32
% 2.65/0.92  --sub_typing                            true
% 2.65/0.92  --prep_gs_sim                           true
% 2.65/0.92  --prep_unflatten                        true
% 2.65/0.92  --prep_res_sim                          true
% 2.65/0.92  --prep_upred                            true
% 2.65/0.92  --prep_sem_filter                       exhaustive
% 2.65/0.92  --prep_sem_filter_out                   false
% 2.65/0.92  --pred_elim                             true
% 2.65/0.92  --res_sim_input                         true
% 2.65/0.92  --eq_ax_congr_red                       true
% 2.65/0.92  --pure_diseq_elim                       true
% 2.65/0.92  --brand_transform                       false
% 2.65/0.92  --non_eq_to_eq                          false
% 2.65/0.92  --prep_def_merge                        true
% 2.65/0.92  --prep_def_merge_prop_impl              false
% 2.65/0.92  --prep_def_merge_mbd                    true
% 2.65/0.92  --prep_def_merge_tr_red                 false
% 2.65/0.92  --prep_def_merge_tr_cl                  false
% 2.65/0.92  --smt_preprocessing                     true
% 2.65/0.92  --smt_ac_axioms                         fast
% 2.65/0.92  --preprocessed_out                      false
% 2.65/0.92  --preprocessed_stats                    false
% 2.65/0.92  
% 2.65/0.92  ------ Abstraction refinement Options
% 2.65/0.92  
% 2.65/0.92  --abstr_ref                             []
% 2.65/0.92  --abstr_ref_prep                        false
% 2.65/0.92  --abstr_ref_until_sat                   false
% 2.65/0.92  --abstr_ref_sig_restrict                funpre
% 2.65/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/0.92  --abstr_ref_under                       []
% 2.65/0.92  
% 2.65/0.92  ------ SAT Options
% 2.65/0.92  
% 2.65/0.92  --sat_mode                              false
% 2.65/0.92  --sat_fm_restart_options                ""
% 2.65/0.92  --sat_gr_def                            false
% 2.65/0.92  --sat_epr_types                         true
% 2.65/0.92  --sat_non_cyclic_types                  false
% 2.65/0.92  --sat_finite_models                     false
% 2.65/0.92  --sat_fm_lemmas                         false
% 2.65/0.92  --sat_fm_prep                           false
% 2.65/0.92  --sat_fm_uc_incr                        true
% 2.65/0.92  --sat_out_model                         small
% 2.65/0.92  --sat_out_clauses                       false
% 2.65/0.92  
% 2.65/0.92  ------ QBF Options
% 2.65/0.92  
% 2.65/0.92  --qbf_mode                              false
% 2.65/0.92  --qbf_elim_univ                         false
% 2.65/0.92  --qbf_dom_inst                          none
% 2.65/0.92  --qbf_dom_pre_inst                      false
% 2.65/0.92  --qbf_sk_in                             false
% 2.65/0.92  --qbf_pred_elim                         true
% 2.65/0.92  --qbf_split                             512
% 2.65/0.92  
% 2.65/0.92  ------ BMC1 Options
% 2.65/0.92  
% 2.65/0.92  --bmc1_incremental                      false
% 2.65/0.92  --bmc1_axioms                           reachable_all
% 2.65/0.92  --bmc1_min_bound                        0
% 2.65/0.92  --bmc1_max_bound                        -1
% 2.65/0.92  --bmc1_max_bound_default                -1
% 2.65/0.92  --bmc1_symbol_reachability              true
% 2.65/0.92  --bmc1_property_lemmas                  false
% 2.65/0.92  --bmc1_k_induction                      false
% 2.65/0.92  --bmc1_non_equiv_states                 false
% 2.65/0.92  --bmc1_deadlock                         false
% 2.65/0.92  --bmc1_ucm                              false
% 2.65/0.92  --bmc1_add_unsat_core                   none
% 2.65/0.92  --bmc1_unsat_core_children              false
% 2.65/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/0.92  --bmc1_out_stat                         full
% 2.65/0.92  --bmc1_ground_init                      false
% 2.65/0.92  --bmc1_pre_inst_next_state              false
% 2.65/0.92  --bmc1_pre_inst_state                   false
% 2.65/0.92  --bmc1_pre_inst_reach_state             false
% 2.65/0.92  --bmc1_out_unsat_core                   false
% 2.65/0.92  --bmc1_aig_witness_out                  false
% 2.65/0.92  --bmc1_verbose                          false
% 2.65/0.92  --bmc1_dump_clauses_tptp                false
% 2.65/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.65/0.92  --bmc1_dump_file                        -
% 2.65/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.65/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.65/0.92  --bmc1_ucm_extend_mode                  1
% 2.65/0.92  --bmc1_ucm_init_mode                    2
% 2.65/0.92  --bmc1_ucm_cone_mode                    none
% 2.65/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.65/0.92  --bmc1_ucm_relax_model                  4
% 2.65/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.65/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/0.92  --bmc1_ucm_layered_model                none
% 2.65/0.92  --bmc1_ucm_max_lemma_size               10
% 2.65/0.92  
% 2.65/0.92  ------ AIG Options
% 2.65/0.92  
% 2.65/0.92  --aig_mode                              false
% 2.65/0.92  
% 2.65/0.92  ------ Instantiation Options
% 2.65/0.92  
% 2.65/0.92  --instantiation_flag                    true
% 2.65/0.92  --inst_sos_flag                         false
% 2.65/0.92  --inst_sos_phase                        true
% 2.65/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/0.92  --inst_lit_sel_side                     none
% 2.65/0.92  --inst_solver_per_active                1400
% 2.65/0.92  --inst_solver_calls_frac                1.
% 2.65/0.92  --inst_passive_queue_type               priority_queues
% 2.65/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/0.92  --inst_passive_queues_freq              [25;2]
% 2.65/0.92  --inst_dismatching                      true
% 2.65/0.92  --inst_eager_unprocessed_to_passive     true
% 2.65/0.92  --inst_prop_sim_given                   true
% 2.65/0.92  --inst_prop_sim_new                     false
% 2.65/0.92  --inst_subs_new                         false
% 2.65/0.92  --inst_eq_res_simp                      false
% 2.65/0.92  --inst_subs_given                       false
% 2.65/0.92  --inst_orphan_elimination               true
% 2.65/0.92  --inst_learning_loop_flag               true
% 2.65/0.92  --inst_learning_start                   3000
% 2.65/0.92  --inst_learning_factor                  2
% 2.65/0.92  --inst_start_prop_sim_after_learn       3
% 2.65/0.92  --inst_sel_renew                        solver
% 2.65/0.92  --inst_lit_activity_flag                true
% 2.65/0.92  --inst_restr_to_given                   false
% 2.65/0.92  --inst_activity_threshold               500
% 2.65/0.92  --inst_out_proof                        true
% 2.65/0.92  
% 2.65/0.92  ------ Resolution Options
% 2.65/0.92  
% 2.65/0.92  --resolution_flag                       false
% 2.65/0.92  --res_lit_sel                           adaptive
% 2.65/0.92  --res_lit_sel_side                      none
% 2.65/0.92  --res_ordering                          kbo
% 2.65/0.92  --res_to_prop_solver                    active
% 2.65/0.92  --res_prop_simpl_new                    false
% 2.65/0.92  --res_prop_simpl_given                  true
% 2.65/0.92  --res_passive_queue_type                priority_queues
% 2.65/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/0.92  --res_passive_queues_freq               [15;5]
% 2.65/0.92  --res_forward_subs                      full
% 2.65/0.92  --res_backward_subs                     full
% 2.65/0.92  --res_forward_subs_resolution           true
% 2.65/0.92  --res_backward_subs_resolution          true
% 2.65/0.92  --res_orphan_elimination                true
% 2.65/0.92  --res_time_limit                        2.
% 2.65/0.92  --res_out_proof                         true
% 2.65/0.92  
% 2.65/0.92  ------ Superposition Options
% 2.65/0.92  
% 2.65/0.92  --superposition_flag                    true
% 2.65/0.92  --sup_passive_queue_type                priority_queues
% 2.65/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.65/0.92  --demod_completeness_check              fast
% 2.65/0.92  --demod_use_ground                      true
% 2.65/0.92  --sup_to_prop_solver                    passive
% 2.65/0.92  --sup_prop_simpl_new                    true
% 2.65/0.92  --sup_prop_simpl_given                  true
% 2.65/0.92  --sup_fun_splitting                     false
% 2.65/0.92  --sup_smt_interval                      50000
% 2.65/0.92  
% 2.65/0.92  ------ Superposition Simplification Setup
% 2.65/0.92  
% 2.65/0.92  --sup_indices_passive                   []
% 2.65/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.92  --sup_full_bw                           [BwDemod]
% 2.65/0.92  --sup_immed_triv                        [TrivRules]
% 2.65/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.92  --sup_immed_bw_main                     []
% 2.65/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.92  
% 2.65/0.92  ------ Combination Options
% 2.65/0.92  
% 2.65/0.92  --comb_res_mult                         3
% 2.65/0.92  --comb_sup_mult                         2
% 2.65/0.92  --comb_inst_mult                        10
% 2.65/0.92  
% 2.65/0.92  ------ Debug Options
% 2.65/0.92  
% 2.65/0.92  --dbg_backtrace                         false
% 2.65/0.92  --dbg_dump_prop_clauses                 false
% 2.65/0.92  --dbg_dump_prop_clauses_file            -
% 2.65/0.92  --dbg_out_stat                          false
% 2.65/0.92  
% 2.65/0.92  
% 2.65/0.92  
% 2.65/0.92  
% 2.65/0.92  ------ Proving...
% 2.65/0.92  
% 2.65/0.92  
% 2.65/0.92  % SZS status Theorem for theBenchmark.p
% 2.65/0.92  
% 2.65/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 2.65/0.92  
% 2.65/0.92  fof(f5,axiom,(
% 2.65/0.92    ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0)))),
% 2.65/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.92  
% 2.65/0.92  fof(f28,plain,(
% 2.65/0.92    ( ! [X0] : (k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0)))) )),
% 2.65/0.92    inference(cnf_transformation,[],[f5])).
% 2.65/0.92  
% 2.65/0.92  fof(f2,axiom,(
% 2.65/0.92    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 2.65/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.92  
% 2.65/0.92  fof(f24,plain,(
% 2.65/0.92    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 2.65/0.92    inference(cnf_transformation,[],[f2])).
% 2.65/0.92  
% 2.65/0.92  fof(f45,plain,(
% 2.65/0.92    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k3_relat_1(k2_enumset1(k4_tarski(X0,X0),k4_tarski(X0,X0),k4_tarski(X0,X0),k4_tarski(X0,X0)))) )),
% 2.65/0.92    inference(definition_unfolding,[],[f28,f24,f24])).
% 2.65/0.92  
% 2.65/0.92  fof(f3,axiom,(
% 2.65/0.92    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 2.65/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.92  
% 2.65/0.92  fof(f25,plain,(
% 2.65/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 2.65/0.92    inference(cnf_transformation,[],[f3])).
% 2.65/0.92  
% 2.65/0.92  fof(f6,axiom,(
% 2.65/0.92    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 2.65/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.92  
% 2.65/0.92  fof(f29,plain,(
% 2.65/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 2.65/0.92    inference(cnf_transformation,[],[f6])).
% 2.65/0.92  
% 2.65/0.92  fof(f35,plain,(
% 2.65/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)))) )),
% 2.65/0.92    inference(definition_unfolding,[],[f29,f24])).
% 2.65/0.92  
% 2.65/0.92  fof(f42,plain,(
% 2.65/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))),k3_relat_1(k2_enumset1(k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3))))) )),
% 2.65/0.92    inference(definition_unfolding,[],[f25,f35,f35])).
% 2.65/0.92  
% 2.65/0.92  fof(f4,axiom,(
% 2.65/0.92    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 2.65/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.92  
% 2.65/0.92  fof(f27,plain,(
% 2.65/0.92    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 2.65/0.92    inference(cnf_transformation,[],[f4])).
% 2.65/0.92  
% 2.65/0.92  fof(f43,plain,(
% 2.65/0.92    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))),k2_enumset1(X2,X2,X2,X2)) = k3_relat_1(k2_enumset1(k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)),k4_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))))) )),
% 2.65/0.92    inference(definition_unfolding,[],[f27,f35,f35,f24])).
% 2.65/0.92  
% 2.65/0.92  fof(f8,conjecture,(
% 2.65/0.92    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 2.65/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.92  
% 2.65/0.92  fof(f9,negated_conjecture,(
% 2.65/0.92    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 2.65/0.92    inference(negated_conjecture,[],[f8])).
% 2.65/0.92  
% 2.65/0.92  fof(f10,plain,(
% 2.65/0.92    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))))),
% 2.65/0.92    inference(ennf_transformation,[],[f9])).
% 2.65/0.92  
% 2.65/0.92  fof(f16,plain,(
% 2.65/0.92    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))) => ((k2_mcart_1(sK1) != sK4 | (k1_mcart_1(sK1) != sK3 & k1_mcart_1(sK1) != sK2)) & r2_hidden(sK1,k2_zfmisc_1(k2_tarski(sK2,sK3),k1_tarski(sK4))))),
% 2.65/0.92    introduced(choice_axiom,[])).
% 2.65/0.92  
% 2.65/0.92  fof(f17,plain,(
% 2.65/0.92    (k2_mcart_1(sK1) != sK4 | (k1_mcart_1(sK1) != sK3 & k1_mcart_1(sK1) != sK2)) & r2_hidden(sK1,k2_zfmisc_1(k2_tarski(sK2,sK3),k1_tarski(sK4)))),
% 2.65/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f10,f16])).
% 2.65/0.92  
% 2.65/0.92  fof(f32,plain,(
% 2.65/0.92    r2_hidden(sK1,k2_zfmisc_1(k2_tarski(sK2,sK3),k1_tarski(sK4)))),
% 2.65/0.92    inference(cnf_transformation,[],[f17])).
% 2.65/0.92  
% 2.65/0.92  fof(f46,plain,(
% 2.65/0.92    r2_hidden(sK1,k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(sK2,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3))),k2_enumset1(sK4,sK4,sK4,sK4)))),
% 2.65/0.92    inference(definition_unfolding,[],[f32,f35,f24])).
% 2.65/0.92  
% 2.65/0.92  fof(f1,axiom,(
% 2.65/0.92    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.65/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.92  
% 2.65/0.92  fof(f11,plain,(
% 2.65/0.92    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.65/0.92    inference(nnf_transformation,[],[f1])).
% 2.65/0.92  
% 2.65/0.92  fof(f12,plain,(
% 2.65/0.92    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.65/0.93    inference(flattening,[],[f11])).
% 2.65/0.93  
% 2.65/0.93  fof(f13,plain,(
% 2.65/0.93    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.65/0.93    inference(rectify,[],[f12])).
% 2.65/0.93  
% 2.65/0.93  fof(f14,plain,(
% 2.65/0.93    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.65/0.93    introduced(choice_axiom,[])).
% 2.65/0.93  
% 2.65/0.93  fof(f15,plain,(
% 2.65/0.93    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.65/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).
% 2.65/0.93  
% 2.65/0.93  fof(f18,plain,(
% 2.65/0.93    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.65/0.93    inference(cnf_transformation,[],[f15])).
% 2.65/0.93  
% 2.65/0.93  fof(f41,plain,(
% 2.65/0.93    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) != X2) )),
% 2.65/0.93    inference(definition_unfolding,[],[f18,f35])).
% 2.65/0.93  
% 2.65/0.93  fof(f51,plain,(
% 2.65/0.93    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))))) )),
% 2.65/0.93    inference(equality_resolution,[],[f41])).
% 2.65/0.93  
% 2.65/0.93  fof(f33,plain,(
% 2.65/0.93    k2_mcart_1(sK1) != sK4 | k1_mcart_1(sK1) != sK2),
% 2.65/0.93    inference(cnf_transformation,[],[f17])).
% 2.65/0.93  
% 2.65/0.93  fof(f7,axiom,(
% 2.65/0.93    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 2.65/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.93  
% 2.65/0.93  fof(f30,plain,(
% 2.65/0.93    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 2.65/0.93    inference(cnf_transformation,[],[f7])).
% 2.65/0.93  
% 2.65/0.93  fof(f31,plain,(
% 2.65/0.93    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 2.65/0.93    inference(cnf_transformation,[],[f7])).
% 2.65/0.93  
% 2.65/0.93  fof(f34,plain,(
% 2.65/0.93    k2_mcart_1(sK1) != sK4 | k1_mcart_1(sK1) != sK3),
% 2.65/0.93    inference(cnf_transformation,[],[f17])).
% 2.65/0.93  
% 2.65/0.93  cnf(c_9,plain,
% 2.65/0.93      ( k3_relat_1(k2_enumset1(k4_tarski(X0,X0),k4_tarski(X0,X0),k4_tarski(X0,X0),k4_tarski(X0,X0))) = k2_enumset1(X0,X0,X0,X0) ),
% 2.65/0.93      inference(cnf_transformation,[],[f45]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_6,plain,
% 2.65/0.93      ( k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))),k3_relat_1(k2_enumset1(k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3)))) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
% 2.65/0.93      inference(cnf_transformation,[],[f42]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_792,plain,
% 2.65/0.93      ( k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)) ),
% 2.65/0.93      inference(superposition,[status(thm)],[c_9,c_6]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_7,plain,
% 2.65/0.93      ( k3_relat_1(k2_enumset1(k4_tarski(k4_tarski(X0,X1),k4_tarski(X2,X1)),k4_tarski(k4_tarski(X0,X1),k4_tarski(X2,X1)),k4_tarski(k4_tarski(X0,X1),k4_tarski(X2,X1)),k4_tarski(k4_tarski(X0,X1),k4_tarski(X2,X1)))) = k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2))),k2_enumset1(X1,X1,X1,X1)) ),
% 2.65/0.93      inference(cnf_transformation,[],[f43]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_949,plain,
% 2.65/0.93      ( k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X0),k4_tarski(X0,X0),k4_tarski(X0,X0),k4_tarski(X0,X0))),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) ),
% 2.65/0.93      inference(superposition,[status(thm)],[c_7,c_9]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_951,plain,
% 2.65/0.93      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ),
% 2.65/0.93      inference(light_normalisation,[status(thm)],[c_949,c_9]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_3090,plain,
% 2.65/0.93      ( k2_zfmisc_1(k3_relat_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)) ),
% 2.65/0.93      inference(light_normalisation,[status(thm)],[c_792,c_951]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_14,negated_conjecture,
% 2.65/0.93      ( r2_hidden(sK1,k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(sK2,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3))),k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 2.65/0.93      inference(cnf_transformation,[],[f46]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_381,plain,
% 2.65/0.93      ( r2_hidden(sK1,k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(sK2,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3),k4_tarski(sK2,sK3))),k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
% 2.65/0.93      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_1276,plain,
% 2.65/0.93      ( r2_hidden(sK1,k2_zfmisc_1(k3_relat_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))),k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
% 2.65/0.93      inference(demodulation,[status(thm)],[c_951,c_381]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_3094,plain,
% 2.65/0.93      ( r2_hidden(sK1,k2_enumset1(k4_tarski(sK2,sK4),k4_tarski(sK2,sK4),k4_tarski(sK3,sK4),k4_tarski(sK3,sK4))) = iProver_top ),
% 2.65/0.93      inference(demodulation,[status(thm)],[c_3090,c_1276]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_5,plain,
% 2.65/0.93      ( ~ r2_hidden(X0,k3_relat_1(k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2))))
% 2.65/0.93      | X0 = X1
% 2.65/0.93      | X0 = X2 ),
% 2.65/0.93      inference(cnf_transformation,[],[f51]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_382,plain,
% 2.65/0.93      ( X0 = X1
% 2.65/0.93      | X0 = X2
% 2.65/0.93      | r2_hidden(X0,k3_relat_1(k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)))) != iProver_top ),
% 2.65/0.93      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_947,plain,
% 2.65/0.93      ( k4_tarski(X0,X1) = X2
% 2.65/0.93      | k4_tarski(X3,X1) = X2
% 2.65/0.93      | r2_hidden(X2,k2_zfmisc_1(k3_relat_1(k2_enumset1(k4_tarski(X0,X3),k4_tarski(X0,X3),k4_tarski(X0,X3),k4_tarski(X0,X3))),k2_enumset1(X1,X1,X1,X1))) != iProver_top ),
% 2.65/0.93      inference(superposition,[status(thm)],[c_7,c_382]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_3119,plain,
% 2.65/0.93      ( k4_tarski(X0,X1) = X2
% 2.65/0.93      | k4_tarski(X3,X1) = X2
% 2.65/0.93      | r2_hidden(X2,k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X3,X1),k4_tarski(X3,X1))) != iProver_top ),
% 2.65/0.93      inference(demodulation,[status(thm)],[c_947,c_951,c_3090]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_3664,plain,
% 2.65/0.93      ( k4_tarski(sK2,sK4) = sK1 | k4_tarski(sK3,sK4) = sK1 ),
% 2.65/0.93      inference(superposition,[status(thm)],[c_3094,c_3119]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_3682,plain,
% 2.65/0.93      ( k4_tarski(sK3,sK4) = sK1
% 2.65/0.93      | r2_hidden(sK1,k2_enumset1(sK1,sK1,k4_tarski(sK3,sK4),k4_tarski(sK3,sK4))) = iProver_top ),
% 2.65/0.93      inference(superposition,[status(thm)],[c_3664,c_3094]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_13,negated_conjecture,
% 2.65/0.93      ( k1_mcart_1(sK1) != sK2 | k2_mcart_1(sK1) != sK4 ),
% 2.65/0.93      inference(cnf_transformation,[],[f33]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_11,plain,
% 2.65/0.93      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 2.65/0.93      inference(cnf_transformation,[],[f30]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_3677,plain,
% 2.65/0.93      ( k4_tarski(sK3,sK4) = sK1 | k1_mcart_1(sK1) = sK2 ),
% 2.65/0.93      inference(superposition,[status(thm)],[c_3664,c_11]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_10,plain,
% 2.65/0.93      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 2.65/0.93      inference(cnf_transformation,[],[f31]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_3678,plain,
% 2.65/0.93      ( k4_tarski(sK3,sK4) = sK1 | k2_mcart_1(sK1) = sK4 ),
% 2.65/0.93      inference(superposition,[status(thm)],[c_3664,c_10]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_4035,plain,
% 2.65/0.93      ( k4_tarski(sK3,sK4) = sK1 ),
% 2.65/0.93      inference(global_propositional_subsumption,
% 2.65/0.93                [status(thm)],
% 2.65/0.93                [c_3682,c_13,c_3677,c_3678]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_4051,plain,
% 2.65/0.93      ( k2_mcart_1(sK1) = sK4 ),
% 2.65/0.93      inference(superposition,[status(thm)],[c_4035,c_10]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_4050,plain,
% 2.65/0.93      ( k1_mcart_1(sK1) = sK3 ),
% 2.65/0.93      inference(superposition,[status(thm)],[c_4035,c_11]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(c_12,negated_conjecture,
% 2.65/0.93      ( k1_mcart_1(sK1) != sK3 | k2_mcart_1(sK1) != sK4 ),
% 2.65/0.93      inference(cnf_transformation,[],[f34]) ).
% 2.65/0.93  
% 2.65/0.93  cnf(contradiction,plain,
% 2.65/0.93      ( $false ),
% 2.65/0.93      inference(minisat,[status(thm)],[c_4051,c_4050,c_12]) ).
% 2.65/0.93  
% 2.65/0.93  
% 2.65/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 2.65/0.93  
% 2.65/0.93  ------                               Statistics
% 2.65/0.93  
% 2.65/0.93  ------ General
% 2.65/0.93  
% 2.65/0.93  abstr_ref_over_cycles:                  0
% 2.65/0.93  abstr_ref_under_cycles:                 0
% 2.65/0.93  gc_basic_clause_elim:                   0
% 2.65/0.93  forced_gc_time:                         0
% 2.65/0.93  parsing_time:                           0.01
% 2.65/0.93  unif_index_cands_time:                  0.
% 2.65/0.93  unif_index_add_time:                    0.
% 2.65/0.93  orderings_time:                         0.
% 2.65/0.93  out_proof_time:                         0.007
% 2.65/0.93  total_time:                             0.19
% 2.65/0.93  num_of_symbols:                         43
% 2.65/0.93  num_of_terms:                           6953
% 2.65/0.93  
% 2.65/0.93  ------ Preprocessing
% 2.65/0.93  
% 2.65/0.93  num_of_splits:                          0
% 2.65/0.93  num_of_split_atoms:                     0
% 2.65/0.93  num_of_reused_defs:                     0
% 2.65/0.93  num_eq_ax_congr_red:                    6
% 2.65/0.93  num_of_sem_filtered_clauses:            1
% 2.65/0.93  num_of_subtypes:                        0
% 2.65/0.93  monotx_restored_types:                  0
% 2.65/0.93  sat_num_of_epr_types:                   0
% 2.65/0.93  sat_num_of_non_cyclic_types:            0
% 2.65/0.93  sat_guarded_non_collapsed_types:        0
% 2.65/0.93  num_pure_diseq_elim:                    0
% 2.65/0.93  simp_replaced_by:                       0
% 2.65/0.93  res_preprocessed:                       64
% 2.65/0.93  prep_upred:                             0
% 2.65/0.93  prep_unflattend:                        11
% 2.65/0.93  smt_new_axioms:                         0
% 2.65/0.93  pred_elim_cands:                        1
% 2.65/0.93  pred_elim:                              0
% 2.65/0.93  pred_elim_cl:                           0
% 2.65/0.93  pred_elim_cycles:                       1
% 2.65/0.93  merged_defs:                            0
% 2.65/0.93  merged_defs_ncl:                        0
% 2.65/0.93  bin_hyper_res:                          0
% 2.65/0.93  prep_cycles:                            3
% 2.65/0.93  pred_elim_time:                         0.003
% 2.65/0.93  splitting_time:                         0.
% 2.65/0.93  sem_filter_time:                        0.
% 2.65/0.93  monotx_time:                            0.
% 2.65/0.93  subtype_inf_time:                       0.
% 2.65/0.93  
% 2.65/0.93  ------ Problem properties
% 2.65/0.93  
% 2.65/0.93  clauses:                                15
% 2.65/0.93  conjectures:                            3
% 2.65/0.93  epr:                                    0
% 2.65/0.93  horn:                                   13
% 2.65/0.93  ground:                                 3
% 2.65/0.93  unary:                                  9
% 2.65/0.93  binary:                                 2
% 2.65/0.93  lits:                                   26
% 2.65/0.93  lits_eq:                                19
% 2.65/0.93  fd_pure:                                0
% 2.65/0.93  fd_pseudo:                              0
% 2.65/0.93  fd_cond:                                0
% 2.65/0.93  fd_pseudo_cond:                         3
% 2.65/0.93  ac_symbols:                             0
% 2.65/0.93  
% 2.65/0.93  ------ Propositional Solver
% 2.65/0.93  
% 2.65/0.93  prop_solver_calls:                      23
% 2.65/0.93  prop_fast_solver_calls:                 368
% 2.65/0.93  smt_solver_calls:                       0
% 2.65/0.93  smt_fast_solver_calls:                  0
% 2.65/0.93  prop_num_of_clauses:                    1874
% 2.65/0.93  prop_preprocess_simplified:             4660
% 2.65/0.93  prop_fo_subsumed:                       1
% 2.65/0.93  prop_solver_time:                       0.
% 2.65/0.93  smt_solver_time:                        0.
% 2.65/0.93  smt_fast_solver_time:                   0.
% 2.65/0.93  prop_fast_solver_time:                  0.
% 2.65/0.93  prop_unsat_core_time:                   0.
% 2.65/0.93  
% 2.65/0.93  ------ QBF
% 2.65/0.93  
% 2.65/0.93  qbf_q_res:                              0
% 2.65/0.93  qbf_num_tautologies:                    0
% 2.65/0.93  qbf_prep_cycles:                        0
% 2.65/0.93  
% 2.65/0.93  ------ BMC1
% 2.65/0.93  
% 2.65/0.93  bmc1_current_bound:                     -1
% 2.65/0.93  bmc1_last_solved_bound:                 -1
% 2.65/0.93  bmc1_unsat_core_size:                   -1
% 2.65/0.93  bmc1_unsat_core_parents_size:           -1
% 2.65/0.93  bmc1_merge_next_fun:                    0
% 2.65/0.93  bmc1_unsat_core_clauses_time:           0.
% 2.65/0.93  
% 2.65/0.93  ------ Instantiation
% 2.65/0.93  
% 2.65/0.93  inst_num_of_clauses:                    516
% 2.65/0.93  inst_num_in_passive:                    314
% 2.65/0.93  inst_num_in_active:                     203
% 2.65/0.93  inst_num_in_unprocessed:                0
% 2.65/0.93  inst_num_of_loops:                      210
% 2.65/0.93  inst_num_of_learning_restarts:          0
% 2.65/0.93  inst_num_moves_active_passive:          6
% 2.65/0.93  inst_lit_activity:                      0
% 2.65/0.93  inst_lit_activity_moves:                0
% 2.65/0.93  inst_num_tautologies:                   0
% 2.65/0.93  inst_num_prop_implied:                  0
% 2.65/0.93  inst_num_existing_simplified:           0
% 2.65/0.93  inst_num_eq_res_simplified:             0
% 2.65/0.93  inst_num_child_elim:                    0
% 2.65/0.93  inst_num_of_dismatching_blockings:      172
% 2.65/0.93  inst_num_of_non_proper_insts:           482
% 2.65/0.93  inst_num_of_duplicates:                 0
% 2.65/0.93  inst_inst_num_from_inst_to_res:         0
% 2.65/0.93  inst_dismatching_checking_time:         0.
% 2.65/0.93  
% 2.65/0.93  ------ Resolution
% 2.65/0.93  
% 2.65/0.93  res_num_of_clauses:                     0
% 2.65/0.93  res_num_in_passive:                     0
% 2.65/0.93  res_num_in_active:                      0
% 2.65/0.93  res_num_of_loops:                       67
% 2.65/0.93  res_forward_subset_subsumed:            94
% 2.65/0.93  res_backward_subset_subsumed:           2
% 2.65/0.93  res_forward_subsumed:                   0
% 2.65/0.93  res_backward_subsumed:                  0
% 2.65/0.93  res_forward_subsumption_resolution:     0
% 2.65/0.93  res_backward_subsumption_resolution:    0
% 2.65/0.93  res_clause_to_clause_subsumption:       242
% 2.65/0.93  res_orphan_elimination:                 0
% 2.65/0.93  res_tautology_del:                      27
% 2.65/0.93  res_num_eq_res_simplified:              0
% 2.65/0.93  res_num_sel_changes:                    0
% 2.65/0.93  res_moves_from_active_to_pass:          0
% 2.65/0.93  
% 2.65/0.93  ------ Superposition
% 2.65/0.93  
% 2.65/0.93  sup_time_total:                         0.
% 2.65/0.93  sup_time_generating:                    0.
% 2.65/0.93  sup_time_sim_full:                      0.
% 2.65/0.93  sup_time_sim_immed:                     0.
% 2.65/0.93  
% 2.65/0.93  sup_num_of_clauses:                     90
% 2.65/0.93  sup_num_in_active:                      27
% 2.65/0.93  sup_num_in_passive:                     63
% 2.65/0.93  sup_num_of_loops:                       40
% 2.65/0.93  sup_fw_superposition:                   69
% 2.65/0.93  sup_bw_superposition:                   52
% 2.65/0.93  sup_immediate_simplified:               11
% 2.65/0.93  sup_given_eliminated:                   1
% 2.65/0.93  comparisons_done:                       0
% 2.65/0.93  comparisons_avoided:                    4
% 2.65/0.93  
% 2.65/0.93  ------ Simplifications
% 2.65/0.93  
% 2.65/0.93  
% 2.65/0.93  sim_fw_subset_subsumed:                 0
% 2.65/0.93  sim_bw_subset_subsumed:                 7
% 2.65/0.93  sim_fw_subsumed:                        5
% 2.65/0.93  sim_bw_subsumed:                        0
% 2.65/0.93  sim_fw_subsumption_res:                 0
% 2.65/0.93  sim_bw_subsumption_res:                 0
% 2.65/0.93  sim_tautology_del:                      0
% 2.65/0.93  sim_eq_tautology_del:                   4
% 2.65/0.93  sim_eq_res_simp:                        0
% 2.65/0.93  sim_fw_demodulated:                     13
% 2.65/0.93  sim_bw_demodulated:                     15
% 2.65/0.93  sim_light_normalised:                   13
% 2.65/0.93  sim_joinable_taut:                      0
% 2.65/0.93  sim_joinable_simp:                      0
% 2.65/0.93  sim_ac_normalised:                      0
% 2.65/0.93  sim_smt_subsumption:                    0
% 2.65/0.93  
%------------------------------------------------------------------------------
