%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0929+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:27 EST 2020

% Result     : Theorem 0.84s
% Output     : CNFRefutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   46 (  82 expanded)
%              Number of clauses        :   11 (  17 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :   16
%              Number of atoms          :  160 ( 307 expanded)
%              Number of equality atoms :  159 ( 306 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k2_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X5 ) ) ) ),
    inference(rectify,[],[f6])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X5
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X3
          & k4_tarski(X2,X3) = X0 )
     => ( sK3(X0,X1) != X1
        & k4_tarski(sK2(X0,X1),sK3(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f20])).

fof(f31,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X5
      | k4_tarski(X4,X5) != X0
      | k2_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X5
      | k2_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f31])).

fof(f43,plain,(
    ! [X6,X4,X7,X5] :
      ( k2_mcart_1(k4_tarski(X4,X5)) = X5
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f42])).

fof(f5,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f5])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X2
          & k4_tarski(X2,X3) = X0 )
     => ( sK0(X0,X1) != X1
        & k4_tarski(sK0(X0,X1),sK1(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f28,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X4
      | k4_tarski(X4,X5) != X0
      | k1_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X4
      | k1_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f28])).

fof(f39,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_mcart_1(k4_tarski(X4,X5)) = X4
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f38])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X4
      & k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X3
      & k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X1
      & k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X4
        & k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X3
        & k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X1
        & k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X4
      | k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X3
      | k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X1
      | k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X4
        | k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X3
        | k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X1
        | k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X0 )
   => ( k20_mcart_1(k4_tarski(sK9,k4_tarski(sK7,sK8))) != sK8
      | k19_mcart_1(k4_tarski(sK9,k4_tarski(sK7,sK8))) != sK7
      | k18_mcart_1(k4_tarski(k4_tarski(sK4,sK5),sK6)) != sK5
      | k17_mcart_1(k4_tarski(k4_tarski(sK4,sK5),sK6)) != sK4 ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k20_mcart_1(k4_tarski(sK9,k4_tarski(sK7,sK8))) != sK8
    | k19_mcart_1(k4_tarski(sK9,k4_tarski(sK7,sK8))) != sK7
    | k18_mcart_1(k4_tarski(k4_tarski(sK4,sK5),sK6)) != sK5
    | k17_mcart_1(k4_tarski(k4_tarski(sK4,sK5),sK6)) != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f13,f22])).

fof(f34,plain,
    ( k20_mcart_1(k4_tarski(sK9,k4_tarski(sK7,sK8))) != sK8
    | k19_mcart_1(k4_tarski(sK9,k4_tarski(sK7,sK8))) != sK7
    | k18_mcart_1(k4_tarski(k4_tarski(sK4,sK5),sK6)) != sK5
    | k17_mcart_1(k4_tarski(k4_tarski(sK4,sK5),sK6)) != sK4 ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] : k2_mcart_1(k2_mcart_1(X0)) = k20_mcart_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_mcart_1(k2_mcart_1(X0)) = k20_mcart_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k1_mcart_1(k2_mcart_1(X0)) = k19_mcart_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k1_mcart_1(k2_mcart_1(X0)) = k19_mcart_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k18_mcart_1(X0) = k2_mcart_1(k1_mcart_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k18_mcart_1(X0) = k2_mcart_1(k1_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k17_mcart_1(X0) = k1_mcart_1(k1_mcart_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k17_mcart_1(X0) = k1_mcart_1(k1_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f35,plain,
    ( k2_mcart_1(k2_mcart_1(k4_tarski(sK9,k4_tarski(sK7,sK8)))) != sK8
    | k1_mcart_1(k2_mcart_1(k4_tarski(sK9,k4_tarski(sK7,sK8)))) != sK7
    | k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK4,sK5),sK6))) != sK5
    | k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK4,sK5),sK6))) != sK4 ),
    inference(definition_unfolding,[],[f34,f27,f26,f25,f24])).

cnf(c_5,plain,
    ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
    | k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_263,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(equality_resolution,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
    | k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_87,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[status(thm)],[c_2])).

cnf(c_6,negated_conjecture,
    ( k2_mcart_1(k2_mcart_1(k4_tarski(sK9,k4_tarski(sK7,sK8)))) != sK8
    | k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK4,sK5),sK6))) != sK5
    | k1_mcart_1(k2_mcart_1(k4_tarski(sK9,k4_tarski(sK7,sK8)))) != sK7
    | k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK4,sK5),sK6))) != sK4 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_92,plain,
    ( k2_mcart_1(k4_tarski(sK4,sK5)) != sK5
    | k2_mcart_1(k2_mcart_1(k4_tarski(sK9,k4_tarski(sK7,sK8)))) != sK8
    | k1_mcart_1(k4_tarski(sK4,sK5)) != sK4
    | k1_mcart_1(k2_mcart_1(k4_tarski(sK9,k4_tarski(sK7,sK8)))) != sK7 ),
    inference(demodulation,[status(thm)],[c_87,c_6])).

cnf(c_97,plain,
    ( k2_mcart_1(k4_tarski(sK4,sK5)) != sK5
    | k2_mcart_1(k2_mcart_1(k4_tarski(sK9,k4_tarski(sK7,sK8)))) != sK8
    | k1_mcart_1(k2_mcart_1(k4_tarski(sK9,k4_tarski(sK7,sK8)))) != sK7
    | sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_92,c_87])).

cnf(c_98,plain,
    ( k2_mcart_1(k4_tarski(sK4,sK5)) != sK5
    | k2_mcart_1(k2_mcart_1(k4_tarski(sK9,k4_tarski(sK7,sK8)))) != sK8
    | k1_mcart_1(k2_mcart_1(k4_tarski(sK9,k4_tarski(sK7,sK8)))) != sK7 ),
    inference(equality_resolution_simp,[status(thm)],[c_97])).

cnf(c_356,plain,
    ( k2_mcart_1(k4_tarski(sK4,sK5)) != sK5
    | k2_mcart_1(k4_tarski(sK7,sK8)) != sK8
    | k1_mcart_1(k4_tarski(sK7,sK8)) != sK7 ),
    inference(demodulation,[status(thm)],[c_263,c_98])).

cnf(c_360,plain,
    ( sK5 != sK5
    | sK8 != sK8
    | sK7 != sK7 ),
    inference(demodulation,[status(thm)],[c_356,c_87,c_263])).

cnf(c_361,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_360])).


%------------------------------------------------------------------------------
