%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0851+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:54 EST 2020

% Result     : Theorem 27.35s
% Output     : CNFRefutation 27.35s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :   14
%              Number of atoms          :  119 ( 119 expanded)
%              Number of equality atoms :  118 ( 118 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1273,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k2_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1326,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X5 ) ) ) ),
    inference(rectify,[],[f1273])).

fof(f2619,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X5
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f1326])).

fof(f3541,plain,(
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
    inference(nnf_transformation,[],[f2619])).

fof(f3542,plain,(
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
    inference(rectify,[],[f3541])).

fof(f3543,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X3
          & k4_tarski(X2,X3) = X0 )
     => ( sK339(X0,X1) != X1
        & k4_tarski(sK338(X0,X1),sK339(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f3544,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ( sK339(X0,X1) != X1
              & k4_tarski(sK338(X0,X1),sK339(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK338,sK339])],[f3542,f3543])).

fof(f5832,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X5
      | k4_tarski(X4,X5) != X0
      | k2_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f3544])).

fof(f6876,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X5
      | k2_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f5832])).

fof(f6877,plain,(
    ! [X6,X4,X7,X5] :
      ( k2_mcart_1(k4_tarski(X4,X5)) = X5
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f6876])).

fof(f1298,conjecture,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1299,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_mcart_1(k4_tarski(X0,X1)) = X1
        & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    inference(negated_conjecture,[],[f1298])).

fof(f2630,plain,(
    ? [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) != X1
      | k1_mcart_1(k4_tarski(X0,X1)) != X0 ) ),
    inference(ennf_transformation,[],[f1299])).

fof(f3637,plain,
    ( ? [X0,X1] :
        ( k2_mcart_1(k4_tarski(X0,X1)) != X1
        | k1_mcart_1(k4_tarski(X0,X1)) != X0 )
   => ( k2_mcart_1(k4_tarski(sK381,sK382)) != sK382
      | k1_mcart_1(k4_tarski(sK381,sK382)) != sK381 ) ),
    introduced(choice_axiom,[])).

fof(f3638,plain,
    ( k2_mcart_1(k4_tarski(sK381,sK382)) != sK382
    | k1_mcart_1(k4_tarski(sK381,sK382)) != sK381 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK381,sK382])],[f2630,f3637])).

fof(f5913,plain,
    ( k2_mcart_1(k4_tarski(sK381,sK382)) != sK382
    | k1_mcart_1(k4_tarski(sK381,sK382)) != sK381 ),
    inference(cnf_transformation,[],[f3638])).

fof(f1272,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1325,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f1272])).

fof(f2618,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f1325])).

fof(f3537,plain,(
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
    inference(nnf_transformation,[],[f2618])).

fof(f3538,plain,(
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
    inference(rectify,[],[f3537])).

fof(f3539,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X2
          & k4_tarski(X2,X3) = X0 )
     => ( sK336(X0,X1) != X1
        & k4_tarski(sK336(X0,X1),sK337(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f3540,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ( sK336(X0,X1) != X1
              & k4_tarski(sK336(X0,X1),sK337(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK336,sK337])],[f3538,f3539])).

fof(f5829,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X4
      | k4_tarski(X4,X5) != X0
      | k1_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f3540])).

fof(f6872,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X4
      | k1_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f5829])).

fof(f6873,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_mcart_1(k4_tarski(X4,X5)) = X4
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f6872])).

cnf(c_2180,plain,
    ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
    | k2_mcart_1(k4_tarski(X2,X3)) = X3 ),
    inference(cnf_transformation,[],[f6877])).

cnf(c_87297,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(equality_resolution,[status(thm)],[c_2180])).

cnf(c_2259,negated_conjecture,
    ( k2_mcart_1(k4_tarski(sK381,sK382)) != sK382
    | k1_mcart_1(k4_tarski(sK381,sK382)) != sK381 ),
    inference(cnf_transformation,[],[f5913])).

cnf(c_2177,plain,
    ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
    | k1_mcart_1(k4_tarski(X2,X3)) = X2 ),
    inference(cnf_transformation,[],[f6873])).

cnf(c_87208,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[status(thm)],[c_2177])).

cnf(c_87299,plain,
    ( k2_mcart_1(k4_tarski(sK381,sK382)) != sK382
    | sK381 != sK381 ),
    inference(demodulation,[status(thm)],[c_2259,c_87208])).

cnf(c_87300,plain,
    ( k2_mcart_1(k4_tarski(sK381,sK382)) != sK382 ),
    inference(equality_resolution_simp,[status(thm)],[c_87299])).

cnf(c_87502,plain,
    ( sK382 != sK382 ),
    inference(demodulation,[status(thm)],[c_87297,c_87300])).

cnf(c_87503,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_87502])).

%------------------------------------------------------------------------------
