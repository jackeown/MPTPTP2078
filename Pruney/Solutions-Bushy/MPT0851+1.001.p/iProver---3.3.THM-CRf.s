%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0851+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:15 EST 2020

% Result     : Theorem 0.72s
% Output     : CNFRefutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   37 (  37 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 ( 123 expanded)
%              Number of equality atoms :  122 ( 122 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k2_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X5 ) ) ) ),
    inference(rectify,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X5
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k2_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X5
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X3
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X3
          & k4_tarski(X2,X3) = X0 )
     => ( sK3(X0,X1) != X1
        & k4_tarski(sK2(X0,X1),sK3(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ( sK3(X0,X1) != X1
              & k4_tarski(sK2(X0,X1),sK3(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f16])).

fof(f23,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X5
      | k4_tarski(X4,X5) != X0
      | k2_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X5
      | k2_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f23])).

fof(f34,plain,(
    ! [X6,X4,X7,X5] :
      ( k2_mcart_1(k4_tarski(X4,X5)) = X5
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k1_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X4
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f7])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X2
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X2
          & k4_tarski(X2,X3) = X0 )
     => ( sK0(X0,X1) != X1
        & k4_tarski(sK0(X0,X1),sK1(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ( sK0(X0,X1) != X1
              & k4_tarski(sK0(X0,X1),sK1(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f20,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X4
      | k4_tarski(X4,X5) != X0
      | k1_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X4
      | k1_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f20])).

fof(f30,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_mcart_1(k4_tarski(X4,X5)) = X4
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f29])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_mcart_1(k4_tarski(X0,X1)) = X1
        & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) != X1
      | k1_mcart_1(k4_tarski(X0,X1)) != X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k2_mcart_1(k4_tarski(X0,X1)) != X1
        | k1_mcart_1(k4_tarski(X0,X1)) != X0 )
   => ( k2_mcart_1(k4_tarski(sK4,sK5)) != sK5
      | k1_mcart_1(k4_tarski(sK4,sK5)) != sK4 ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( k2_mcart_1(k4_tarski(sK4,sK5)) != sK5
    | k1_mcart_1(k4_tarski(sK4,sK5)) != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f9,f18])).

fof(f26,plain,
    ( k2_mcart_1(k4_tarski(sK4,sK5)) != sK5
    | k1_mcart_1(k4_tarski(sK4,sK5)) != sK4 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_22,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_104,plain,
    ( k4_tarski(sK4,sK5) = k4_tarski(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_5,plain,
    ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
    | k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_74,plain,
    ( k4_tarski(sK4,sK5) != k4_tarski(X0,X1)
    | k2_mcart_1(k4_tarski(sK4,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_103,plain,
    ( k4_tarski(sK4,sK5) != k4_tarski(sK4,sK5)
    | k2_mcart_1(k4_tarski(sK4,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_2,plain,
    ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
    | k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_84,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[status(thm)],[c_2])).

cnf(c_6,negated_conjecture,
    ( k2_mcart_1(k4_tarski(sK4,sK5)) != sK5
    | k1_mcart_1(k4_tarski(sK4,sK5)) != sK4 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_89,plain,
    ( k2_mcart_1(k4_tarski(sK4,sK5)) != sK5
    | sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_84,c_6])).

cnf(c_90,plain,
    ( k2_mcart_1(k4_tarski(sK4,sK5)) != sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_89])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_104,c_103,c_90])).


%------------------------------------------------------------------------------
