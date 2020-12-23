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
% DateTime   : Thu Dec  3 11:31:53 EST 2020

% Result     : Theorem 8.07s
% Output     : CNFRefutation 8.07s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 434 expanded)
%              Number of clauses        :   46 ( 106 expanded)
%              Number of leaves         :   12 ( 129 expanded)
%              Depth                    :   16
%              Number of atoms          :  303 (1787 expanded)
%              Number of equality atoms :  158 ( 949 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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

fof(f8,plain,(
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
    inference(rectify,[],[f7])).

fof(f9,plain,(
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

fof(f10,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) = X0
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = X1
      | sK0(X0,X1) = X0
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f11])).

fof(f15,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
        & r2_hidden(sK5(X0,X1,X8),X1)
        & r2_hidden(sK4(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK1(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK1(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK1(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2)
              & r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
                & r2_hidden(sK5(X0,X1,X8),X1)
                & r2_hidden(sK4(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f12,f15,f14,f13])).

fof(f25,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f40,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f4,conjecture,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ? [X0,X1] : k1_tarski(k4_tarski(X0,X1)) != k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,
    ( ? [X0,X1] : k1_tarski(k4_tarski(X0,X1)) != k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1))
   => k1_tarski(k4_tarski(sK6,sK7)) != k2_zfmisc_1(k1_tarski(sK6),k1_tarski(sK7)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    k1_tarski(k4_tarski(sK6,sK7)) != k2_zfmisc_1(k1_tarski(sK6),k1_tarski(sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f6,f17])).

fof(f32,plain,(
    k1_tarski(k4_tarski(sK6,sK7)) != k2_zfmisc_1(k1_tarski(sK6),k1_tarski(sK7)) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) != k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)) ),
    inference(definition_unfolding,[],[f32,f23,f23,f23])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f38,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f35])).

fof(f39,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f38])).

fof(f27,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f27])).

fof(f42,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) != X0
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = X1
      | sK0(X0,X1) != X0
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f26,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f24,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK4(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | sK0(X0,X1) = X0
    | k2_tarski(X0,X0) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_369,plain,
    ( sK0(X0,X1) = X0
    | k2_tarski(X0,X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_360,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_367,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_609,plain,
    ( sK5(X0,k2_tarski(X1,X1),X2) = X1
    | r2_hidden(X2,k2_zfmisc_1(X0,k2_tarski(X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_360,c_367])).

cnf(c_1022,plain,
    ( sK5(X0,k2_tarski(X1,X1),sK0(X2,k2_zfmisc_1(X0,k2_tarski(X1,X1)))) = X1
    | k2_zfmisc_1(X0,k2_tarski(X1,X1)) = k2_tarski(X2,X2)
    | sK0(X2,k2_zfmisc_1(X0,k2_tarski(X1,X1))) = X2 ),
    inference(superposition,[status(thm)],[c_369,c_609])).

cnf(c_12,negated_conjecture,
    ( k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) != k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_30595,plain,
    ( sK5(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7),sK0(X0,k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))) = sK7
    | sK0(X0,k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) = X0
    | k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) != k2_tarski(X0,X0) ),
    inference(superposition,[status(thm)],[c_1022,c_12])).

cnf(c_33278,plain,
    ( sK5(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))) = sK7
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) = k4_tarski(sK6,sK7) ),
    inference(equality_resolution,[status(thm)],[c_30595])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_41,plain,
    ( r2_hidden(sK6,k2_tarski(sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_473,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_tarski(X2,X2))
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(k2_tarski(X2,X2),X1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_544,plain,
    ( ~ r2_hidden(X0,k2_tarski(X0,X0))
    | ~ r2_hidden(X1,k2_tarski(X1,X1))
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_7153,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))
    | ~ r2_hidden(sK7,k2_tarski(sK7,sK7))
    | ~ r2_hidden(sK6,k2_tarski(sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_146,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_847,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | X2 != X0
    | sK0(X0,X1) = X2
    | k2_tarski(X0,X0) = X1 ),
    inference(resolution,[status(thm)],[c_1,c_146])).

cnf(c_4688,plain,
    ( r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))
    | X0 != k4_tarski(sK6,sK7)
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) = X0 ),
    inference(resolution,[status(thm)],[c_847,c_12])).

cnf(c_148,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_145,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_872,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_148,c_145])).

cnf(c_5643,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))),X1)
    | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))
    | X0 != k4_tarski(sK6,sK7) ),
    inference(resolution,[status(thm)],[c_4688,c_872])).

cnf(c_5736,plain,
    ( ~ r2_hidden(k4_tarski(sK6,sK7),X0)
    | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))),X0)
    | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) ),
    inference(resolution,[status(thm)],[c_5643,c_145])).

cnf(c_7377,plain,
    ( ~ r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))
    | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) ),
    inference(factoring,[status(thm)],[c_5736])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | sK0(X0,X1) != X0
    | k2_tarski(X0,X0) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16516,plain,
    ( ~ r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) != k4_tarski(sK6,sK7)
    | k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) = k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_28026,plain,
    ( r2_hidden(sK7,k2_tarski(sK7,sK7)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_34802,plain,
    ( sK5(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_33278,c_12,c_41,c_7153,c_7377,c_16516,c_28026])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK4(X1,X2,X0),sK5(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_361,plain,
    ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X2
    | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1020,plain,
    ( k4_tarski(sK4(X0,X1,sK0(X2,k2_zfmisc_1(X0,X1))),sK5(X0,X1,sK0(X2,k2_zfmisc_1(X0,X1)))) = sK0(X2,k2_zfmisc_1(X0,X1))
    | k2_zfmisc_1(X0,X1) = k2_tarski(X2,X2)
    | sK0(X2,k2_zfmisc_1(X0,X1)) = X2 ),
    inference(superposition,[status(thm)],[c_369,c_361])).

cnf(c_34840,plain,
    ( k4_tarski(sK4(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))),sK7) = sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))
    | k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)) = k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7))
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) = k4_tarski(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_34802,c_1020])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_359,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_510,plain,
    ( sK4(k2_tarski(X0,X0),X1,X2) = X0
    | r2_hidden(X2,k2_zfmisc_1(k2_tarski(X0,X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_359,c_367])).

cnf(c_1021,plain,
    ( sK4(k2_tarski(X0,X0),X1,sK0(X2,k2_zfmisc_1(k2_tarski(X0,X0),X1))) = X0
    | k2_zfmisc_1(k2_tarski(X0,X0),X1) = k2_tarski(X2,X2)
    | sK0(X2,k2_zfmisc_1(k2_tarski(X0,X0),X1)) = X2 ),
    inference(superposition,[status(thm)],[c_369,c_510])).

cnf(c_19562,plain,
    ( sK4(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7),sK0(X0,k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))) = sK6
    | sK0(X0,k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) = X0
    | k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) != k2_tarski(X0,X0) ),
    inference(superposition,[status(thm)],[c_1021,c_12])).

cnf(c_21246,plain,
    ( sK4(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))) = sK6
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) = k4_tarski(sK6,sK7) ),
    inference(equality_resolution,[status(thm)],[c_19562])).

cnf(c_28249,plain,
    ( sK4(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21246,c_12,c_41,c_7153,c_7377,c_16516,c_28026])).

cnf(c_34844,plain,
    ( k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)) = k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7))
    | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) = k4_tarski(sK6,sK7) ),
    inference(light_normalisation,[status(thm)],[c_34840,c_28249])).

cnf(c_539,plain,
    ( k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) = k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_145])).

cnf(c_471,plain,
    ( k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)) != X0
    | k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) != X0
    | k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) = k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)) ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_538,plain,
    ( k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)) != k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7))
    | k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) = k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))
    | k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) != k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_471])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34844,c_28026,c_16516,c_7377,c_7153,c_539,c_538,c_41,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:46:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 8.07/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.07/1.48  
% 8.07/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.07/1.48  
% 8.07/1.48  ------  iProver source info
% 8.07/1.48  
% 8.07/1.48  git: date: 2020-06-30 10:37:57 +0100
% 8.07/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.07/1.48  git: non_committed_changes: false
% 8.07/1.48  git: last_make_outside_of_git: false
% 8.07/1.48  
% 8.07/1.48  ------ 
% 8.07/1.48  ------ Parsing...
% 8.07/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.07/1.48  
% 8.07/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 8.07/1.48  
% 8.07/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.07/1.48  
% 8.07/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.07/1.48  ------ Proving...
% 8.07/1.48  ------ Problem Properties 
% 8.07/1.48  
% 8.07/1.48  
% 8.07/1.48  clauses                                 13
% 8.07/1.48  conjectures                             1
% 8.07/1.48  EPR                                     0
% 8.07/1.48  Horn                                    9
% 8.07/1.48  unary                                   2
% 8.07/1.48  binary                                  4
% 8.07/1.48  lits                                    33
% 8.07/1.48  lits eq                                 13
% 8.07/1.48  fd_pure                                 0
% 8.07/1.48  fd_pseudo                               0
% 8.07/1.48  fd_cond                                 0
% 8.07/1.48  fd_pseudo_cond                          6
% 8.07/1.48  AC symbols                              0
% 8.07/1.48  
% 8.07/1.48  ------ Input Options Time Limit: Unbounded
% 8.07/1.48  
% 8.07/1.48  
% 8.07/1.48  ------ 
% 8.07/1.48  Current options:
% 8.07/1.48  ------ 
% 8.07/1.48  
% 8.07/1.48  
% 8.07/1.48  
% 8.07/1.48  
% 8.07/1.48  ------ Proving...
% 8.07/1.48  
% 8.07/1.48  
% 8.07/1.48  % SZS status Theorem for theBenchmark.p
% 8.07/1.48  
% 8.07/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 8.07/1.48  
% 8.07/1.48  fof(f1,axiom,(
% 8.07/1.48    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 8.07/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.48  
% 8.07/1.48  fof(f7,plain,(
% 8.07/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 8.07/1.48    inference(nnf_transformation,[],[f1])).
% 8.07/1.48  
% 8.07/1.48  fof(f8,plain,(
% 8.07/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 8.07/1.48    inference(rectify,[],[f7])).
% 8.07/1.48  
% 8.07/1.48  fof(f9,plain,(
% 8.07/1.48    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 8.07/1.48    introduced(choice_axiom,[])).
% 8.07/1.48  
% 8.07/1.48  fof(f10,plain,(
% 8.07/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 8.07/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).
% 8.07/1.48  
% 8.07/1.48  fof(f21,plain,(
% 8.07/1.48    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)) )),
% 8.07/1.48    inference(cnf_transformation,[],[f10])).
% 8.07/1.48  
% 8.07/1.48  fof(f2,axiom,(
% 8.07/1.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 8.07/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.48  
% 8.07/1.48  fof(f23,plain,(
% 8.07/1.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 8.07/1.48    inference(cnf_transformation,[],[f2])).
% 8.07/1.48  
% 8.07/1.48  fof(f34,plain,(
% 8.07/1.48    ( ! [X0,X1] : (k2_tarski(X0,X0) = X1 | sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)) )),
% 8.07/1.48    inference(definition_unfolding,[],[f21,f23])).
% 8.07/1.48  
% 8.07/1.48  fof(f3,axiom,(
% 8.07/1.48    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 8.07/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.48  
% 8.07/1.48  fof(f11,plain,(
% 8.07/1.48    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 8.07/1.48    inference(nnf_transformation,[],[f3])).
% 8.07/1.48  
% 8.07/1.48  fof(f12,plain,(
% 8.07/1.48    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 8.07/1.48    inference(rectify,[],[f11])).
% 8.07/1.48  
% 8.07/1.48  fof(f15,plain,(
% 8.07/1.48    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)))),
% 8.07/1.48    introduced(choice_axiom,[])).
% 8.07/1.48  
% 8.07/1.48  fof(f14,plain,(
% 8.07/1.48    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)))) )),
% 8.07/1.48    introduced(choice_axiom,[])).
% 8.07/1.48  
% 8.07/1.48  fof(f13,plain,(
% 8.07/1.48    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK1(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 8.07/1.48    introduced(choice_axiom,[])).
% 8.07/1.48  
% 8.07/1.48  fof(f16,plain,(
% 8.07/1.48    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK1(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 & r2_hidden(sK5(X0,X1,X8),X1) & r2_hidden(sK4(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 8.07/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f12,f15,f14,f13])).
% 8.07/1.48  
% 8.07/1.48  fof(f25,plain,(
% 8.07/1.48    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 8.07/1.48    inference(cnf_transformation,[],[f16])).
% 8.07/1.48  
% 8.07/1.48  fof(f44,plain,(
% 8.07/1.48    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 8.07/1.48    inference(equality_resolution,[],[f25])).
% 8.07/1.48  
% 8.07/1.48  fof(f19,plain,(
% 8.07/1.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 8.07/1.48    inference(cnf_transformation,[],[f10])).
% 8.07/1.48  
% 8.07/1.48  fof(f36,plain,(
% 8.07/1.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 8.07/1.48    inference(definition_unfolding,[],[f19,f23])).
% 8.07/1.48  
% 8.07/1.48  fof(f40,plain,(
% 8.07/1.48    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 8.07/1.48    inference(equality_resolution,[],[f36])).
% 8.07/1.48  
% 8.07/1.48  fof(f4,conjecture,(
% 8.07/1.48    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1))),
% 8.07/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.07/1.48  
% 8.07/1.48  fof(f5,negated_conjecture,(
% 8.07/1.48    ~! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1))),
% 8.07/1.48    inference(negated_conjecture,[],[f4])).
% 8.07/1.48  
% 8.07/1.48  fof(f6,plain,(
% 8.07/1.48    ? [X0,X1] : k1_tarski(k4_tarski(X0,X1)) != k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1))),
% 8.07/1.48    inference(ennf_transformation,[],[f5])).
% 8.07/1.48  
% 8.07/1.48  fof(f17,plain,(
% 8.07/1.48    ? [X0,X1] : k1_tarski(k4_tarski(X0,X1)) != k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) => k1_tarski(k4_tarski(sK6,sK7)) != k2_zfmisc_1(k1_tarski(sK6),k1_tarski(sK7))),
% 8.07/1.48    introduced(choice_axiom,[])).
% 8.07/1.48  
% 8.07/1.48  fof(f18,plain,(
% 8.07/1.48    k1_tarski(k4_tarski(sK6,sK7)) != k2_zfmisc_1(k1_tarski(sK6),k1_tarski(sK7))),
% 8.07/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f6,f17])).
% 8.07/1.48  
% 8.07/1.48  fof(f32,plain,(
% 8.07/1.48    k1_tarski(k4_tarski(sK6,sK7)) != k2_zfmisc_1(k1_tarski(sK6),k1_tarski(sK7))),
% 8.07/1.48    inference(cnf_transformation,[],[f18])).
% 8.07/1.48  
% 8.07/1.48  fof(f37,plain,(
% 8.07/1.48    k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) != k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))),
% 8.07/1.48    inference(definition_unfolding,[],[f32,f23,f23,f23])).
% 8.07/1.48  
% 8.07/1.48  fof(f20,plain,(
% 8.07/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 8.07/1.48    inference(cnf_transformation,[],[f10])).
% 8.07/1.48  
% 8.07/1.48  fof(f35,plain,(
% 8.07/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 8.07/1.48    inference(definition_unfolding,[],[f20,f23])).
% 8.07/1.48  
% 8.07/1.48  fof(f38,plain,(
% 8.07/1.48    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 8.07/1.48    inference(equality_resolution,[],[f35])).
% 8.07/1.48  
% 8.07/1.48  fof(f39,plain,(
% 8.07/1.48    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 8.07/1.48    inference(equality_resolution,[],[f38])).
% 8.07/1.48  
% 8.07/1.48  fof(f27,plain,(
% 8.07/1.48    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 8.07/1.48    inference(cnf_transformation,[],[f16])).
% 8.07/1.48  
% 8.07/1.48  fof(f41,plain,(
% 8.07/1.48    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 8.07/1.48    inference(equality_resolution,[],[f27])).
% 8.07/1.48  
% 8.07/1.48  fof(f42,plain,(
% 8.07/1.48    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 8.07/1.48    inference(equality_resolution,[],[f41])).
% 8.07/1.48  
% 8.07/1.48  fof(f22,plain,(
% 8.07/1.48    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) )),
% 8.07/1.48    inference(cnf_transformation,[],[f10])).
% 8.07/1.48  
% 8.07/1.48  fof(f33,plain,(
% 8.07/1.48    ( ! [X0,X1] : (k2_tarski(X0,X0) = X1 | sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) )),
% 8.07/1.48    inference(definition_unfolding,[],[f22,f23])).
% 8.07/1.48  
% 8.07/1.48  fof(f26,plain,(
% 8.07/1.48    ( ! [X2,X0,X8,X1] : (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 8.07/1.48    inference(cnf_transformation,[],[f16])).
% 8.07/1.48  
% 8.07/1.48  fof(f43,plain,(
% 8.07/1.48    ( ! [X0,X8,X1] : (k4_tarski(sK4(X0,X1,X8),sK5(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 8.07/1.48    inference(equality_resolution,[],[f26])).
% 8.07/1.48  
% 8.07/1.48  fof(f24,plain,(
% 8.07/1.48    ( ! [X2,X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 8.07/1.48    inference(cnf_transformation,[],[f16])).
% 8.07/1.48  
% 8.07/1.48  fof(f45,plain,(
% 8.07/1.48    ( ! [X0,X8,X1] : (r2_hidden(sK4(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 8.07/1.48    inference(equality_resolution,[],[f24])).
% 8.07/1.48  
% 8.07/1.48  cnf(c_1,plain,
% 8.07/1.48      ( r2_hidden(sK0(X0,X1),X1)
% 8.07/1.48      | sK0(X0,X1) = X0
% 8.07/1.48      | k2_tarski(X0,X0) = X1 ),
% 8.07/1.48      inference(cnf_transformation,[],[f34]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_369,plain,
% 8.07/1.48      ( sK0(X0,X1) = X0
% 8.07/1.48      | k2_tarski(X0,X0) = X1
% 8.07/1.48      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 8.07/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_10,plain,
% 8.07/1.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 8.07/1.48      | r2_hidden(sK5(X1,X2,X0),X2) ),
% 8.07/1.48      inference(cnf_transformation,[],[f44]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_360,plain,
% 8.07/1.48      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 8.07/1.48      | r2_hidden(sK5(X1,X2,X0),X2) = iProver_top ),
% 8.07/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_3,plain,
% 8.07/1.48      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 8.07/1.48      inference(cnf_transformation,[],[f40]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_367,plain,
% 8.07/1.48      ( X0 = X1 | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
% 8.07/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_609,plain,
% 8.07/1.48      ( sK5(X0,k2_tarski(X1,X1),X2) = X1
% 8.07/1.48      | r2_hidden(X2,k2_zfmisc_1(X0,k2_tarski(X1,X1))) != iProver_top ),
% 8.07/1.48      inference(superposition,[status(thm)],[c_360,c_367]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_1022,plain,
% 8.07/1.48      ( sK5(X0,k2_tarski(X1,X1),sK0(X2,k2_zfmisc_1(X0,k2_tarski(X1,X1)))) = X1
% 8.07/1.48      | k2_zfmisc_1(X0,k2_tarski(X1,X1)) = k2_tarski(X2,X2)
% 8.07/1.48      | sK0(X2,k2_zfmisc_1(X0,k2_tarski(X1,X1))) = X2 ),
% 8.07/1.48      inference(superposition,[status(thm)],[c_369,c_609]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_12,negated_conjecture,
% 8.07/1.48      ( k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) != k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)) ),
% 8.07/1.48      inference(cnf_transformation,[],[f37]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_30595,plain,
% 8.07/1.48      ( sK5(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7),sK0(X0,k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))) = sK7
% 8.07/1.48      | sK0(X0,k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) = X0
% 8.07/1.48      | k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) != k2_tarski(X0,X0) ),
% 8.07/1.48      inference(superposition,[status(thm)],[c_1022,c_12]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_33278,plain,
% 8.07/1.48      ( sK5(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))) = sK7
% 8.07/1.48      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) = k4_tarski(sK6,sK7) ),
% 8.07/1.48      inference(equality_resolution,[status(thm)],[c_30595]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_2,plain,
% 8.07/1.48      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 8.07/1.48      inference(cnf_transformation,[],[f39]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_41,plain,
% 8.07/1.48      ( r2_hidden(sK6,k2_tarski(sK6,sK6)) ),
% 8.07/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_8,plain,
% 8.07/1.48      ( ~ r2_hidden(X0,X1)
% 8.07/1.48      | ~ r2_hidden(X2,X3)
% 8.07/1.48      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 8.07/1.48      inference(cnf_transformation,[],[f42]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_473,plain,
% 8.07/1.48      ( ~ r2_hidden(X0,X1)
% 8.07/1.48      | ~ r2_hidden(X2,k2_tarski(X2,X2))
% 8.07/1.48      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(k2_tarski(X2,X2),X1)) ),
% 8.07/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_544,plain,
% 8.07/1.48      ( ~ r2_hidden(X0,k2_tarski(X0,X0))
% 8.07/1.48      | ~ r2_hidden(X1,k2_tarski(X1,X1))
% 8.07/1.48      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X0,X0))) ),
% 8.07/1.48      inference(instantiation,[status(thm)],[c_473]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_7153,plain,
% 8.07/1.48      ( r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))
% 8.07/1.48      | ~ r2_hidden(sK7,k2_tarski(sK7,sK7))
% 8.07/1.48      | ~ r2_hidden(sK6,k2_tarski(sK6,sK6)) ),
% 8.07/1.48      inference(instantiation,[status(thm)],[c_544]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_146,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_847,plain,
% 8.07/1.48      ( r2_hidden(sK0(X0,X1),X1)
% 8.07/1.48      | X2 != X0
% 8.07/1.48      | sK0(X0,X1) = X2
% 8.07/1.48      | k2_tarski(X0,X0) = X1 ),
% 8.07/1.48      inference(resolution,[status(thm)],[c_1,c_146]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_4688,plain,
% 8.07/1.48      ( r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))
% 8.07/1.48      | X0 != k4_tarski(sK6,sK7)
% 8.07/1.48      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) = X0 ),
% 8.07/1.48      inference(resolution,[status(thm)],[c_847,c_12]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_148,plain,
% 8.07/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 8.07/1.48      theory(equality) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_145,plain,( X0 = X0 ),theory(equality) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_872,plain,
% 8.07/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 8.07/1.48      inference(resolution,[status(thm)],[c_148,c_145]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_5643,plain,
% 8.07/1.48      ( ~ r2_hidden(X0,X1)
% 8.07/1.48      | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))),X1)
% 8.07/1.48      | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))
% 8.07/1.48      | X0 != k4_tarski(sK6,sK7) ),
% 8.07/1.48      inference(resolution,[status(thm)],[c_4688,c_872]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_5736,plain,
% 8.07/1.48      ( ~ r2_hidden(k4_tarski(sK6,sK7),X0)
% 8.07/1.48      | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))),X0)
% 8.07/1.48      | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) ),
% 8.07/1.48      inference(resolution,[status(thm)],[c_5643,c_145]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_7377,plain,
% 8.07/1.48      ( ~ r2_hidden(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))
% 8.07/1.48      | r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) ),
% 8.07/1.48      inference(factoring,[status(thm)],[c_5736]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_0,plain,
% 8.07/1.48      ( ~ r2_hidden(sK0(X0,X1),X1)
% 8.07/1.48      | sK0(X0,X1) != X0
% 8.07/1.48      | k2_tarski(X0,X0) = X1 ),
% 8.07/1.48      inference(cnf_transformation,[],[f33]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_16516,plain,
% 8.07/1.48      ( ~ r2_hidden(sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))
% 8.07/1.48      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) != k4_tarski(sK6,sK7)
% 8.07/1.48      | k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) = k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)) ),
% 8.07/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_28026,plain,
% 8.07/1.48      ( r2_hidden(sK7,k2_tarski(sK7,sK7)) ),
% 8.07/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_34802,plain,
% 8.07/1.48      ( sK5(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))) = sK7 ),
% 8.07/1.48      inference(global_propositional_subsumption,
% 8.07/1.48                [status(thm)],
% 8.07/1.48                [c_33278,c_12,c_41,c_7153,c_7377,c_16516,c_28026]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_9,plain,
% 8.07/1.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 8.07/1.48      | k4_tarski(sK4(X1,X2,X0),sK5(X1,X2,X0)) = X0 ),
% 8.07/1.48      inference(cnf_transformation,[],[f43]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_361,plain,
% 8.07/1.48      ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X2
% 8.07/1.48      | r2_hidden(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 8.07/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_1020,plain,
% 8.07/1.48      ( k4_tarski(sK4(X0,X1,sK0(X2,k2_zfmisc_1(X0,X1))),sK5(X0,X1,sK0(X2,k2_zfmisc_1(X0,X1)))) = sK0(X2,k2_zfmisc_1(X0,X1))
% 8.07/1.48      | k2_zfmisc_1(X0,X1) = k2_tarski(X2,X2)
% 8.07/1.48      | sK0(X2,k2_zfmisc_1(X0,X1)) = X2 ),
% 8.07/1.48      inference(superposition,[status(thm)],[c_369,c_361]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_34840,plain,
% 8.07/1.48      ( k4_tarski(sK4(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))),sK7) = sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))
% 8.07/1.48      | k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)) = k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7))
% 8.07/1.48      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) = k4_tarski(sK6,sK7) ),
% 8.07/1.48      inference(superposition,[status(thm)],[c_34802,c_1020]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_11,plain,
% 8.07/1.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 8.07/1.48      | r2_hidden(sK4(X1,X2,X0),X1) ),
% 8.07/1.48      inference(cnf_transformation,[],[f45]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_359,plain,
% 8.07/1.48      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 8.07/1.48      | r2_hidden(sK4(X1,X2,X0),X1) = iProver_top ),
% 8.07/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_510,plain,
% 8.07/1.48      ( sK4(k2_tarski(X0,X0),X1,X2) = X0
% 8.07/1.48      | r2_hidden(X2,k2_zfmisc_1(k2_tarski(X0,X0),X1)) != iProver_top ),
% 8.07/1.48      inference(superposition,[status(thm)],[c_359,c_367]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_1021,plain,
% 8.07/1.48      ( sK4(k2_tarski(X0,X0),X1,sK0(X2,k2_zfmisc_1(k2_tarski(X0,X0),X1))) = X0
% 8.07/1.48      | k2_zfmisc_1(k2_tarski(X0,X0),X1) = k2_tarski(X2,X2)
% 8.07/1.48      | sK0(X2,k2_zfmisc_1(k2_tarski(X0,X0),X1)) = X2 ),
% 8.07/1.48      inference(superposition,[status(thm)],[c_369,c_510]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_19562,plain,
% 8.07/1.48      ( sK4(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7),sK0(X0,k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))) = sK6
% 8.07/1.48      | sK0(X0,k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) = X0
% 8.07/1.48      | k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) != k2_tarski(X0,X0) ),
% 8.07/1.48      inference(superposition,[status(thm)],[c_1021,c_12]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_21246,plain,
% 8.07/1.48      ( sK4(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))) = sK6
% 8.07/1.48      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) = k4_tarski(sK6,sK7) ),
% 8.07/1.48      inference(equality_resolution,[status(thm)],[c_19562]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_28249,plain,
% 8.07/1.48      ( sK4(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7),sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)))) = sK6 ),
% 8.07/1.48      inference(global_propositional_subsumption,
% 8.07/1.48                [status(thm)],
% 8.07/1.48                [c_21246,c_12,c_41,c_7153,c_7377,c_16516,c_28026]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_34844,plain,
% 8.07/1.48      ( k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)) = k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7))
% 8.07/1.48      | sK0(k4_tarski(sK6,sK7),k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))) = k4_tarski(sK6,sK7) ),
% 8.07/1.48      inference(light_normalisation,[status(thm)],[c_34840,c_28249]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_539,plain,
% 8.07/1.48      ( k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) = k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) ),
% 8.07/1.48      inference(instantiation,[status(thm)],[c_145]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_471,plain,
% 8.07/1.48      ( k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)) != X0
% 8.07/1.48      | k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) != X0
% 8.07/1.48      | k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) = k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)) ),
% 8.07/1.48      inference(instantiation,[status(thm)],[c_146]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(c_538,plain,
% 8.07/1.48      ( k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7)) != k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7))
% 8.07/1.48      | k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) = k2_zfmisc_1(k2_tarski(sK6,sK6),k2_tarski(sK7,sK7))
% 8.07/1.48      | k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) != k2_tarski(k4_tarski(sK6,sK7),k4_tarski(sK6,sK7)) ),
% 8.07/1.48      inference(instantiation,[status(thm)],[c_471]) ).
% 8.07/1.48  
% 8.07/1.48  cnf(contradiction,plain,
% 8.07/1.48      ( $false ),
% 8.07/1.48      inference(minisat,
% 8.07/1.48                [status(thm)],
% 8.07/1.48                [c_34844,c_28026,c_16516,c_7377,c_7153,c_539,c_538,c_41,
% 8.07/1.48                 c_12]) ).
% 8.07/1.48  
% 8.07/1.48  
% 8.07/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 8.07/1.48  
% 8.07/1.48  ------                               Statistics
% 8.07/1.48  
% 8.07/1.48  ------ Selected
% 8.07/1.48  
% 8.07/1.48  total_time:                             0.998
% 8.07/1.48  
%------------------------------------------------------------------------------
