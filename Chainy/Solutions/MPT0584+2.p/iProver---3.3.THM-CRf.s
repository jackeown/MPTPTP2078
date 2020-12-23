%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0584+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:46 EST 2020

% Result     : Theorem 39.10s
% Output     : CNFRefutation 39.10s
% Verified   : 
% Statistics : Number of formulae       :   34 (  84 expanded)
%              Number of clauses        :   17 (  22 expanded)
%              Number of leaves         :    5 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :   88 ( 356 expanded)
%              Number of equality atoms :   44 ( 165 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f775,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2,X3] :
              ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & r1_tarski(X2,X3) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f776,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2,X3] :
                ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                  & r1_tarski(X2,X3) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f775])).

fof(f1429,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f776])).

fof(f1430,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1429])).

fof(f1969,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
          & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
          & r1_tarski(X2,X3) )
     => ( k7_relat_1(X0,sK162) != k7_relat_1(X1,sK162)
        & k7_relat_1(X0,sK163) = k7_relat_1(X1,sK163)
        & r1_tarski(sK162,sK163) ) ) ),
    introduced(choice_axiom,[])).

fof(f1968,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
     => ( ? [X3,X2] :
            ( k7_relat_1(sK161,X2) != k7_relat_1(X0,X2)
            & k7_relat_1(sK161,X3) = k7_relat_1(X0,X3)
            & r1_tarski(X2,X3) )
        & v1_relat_1(sK161) ) ) ),
    introduced(choice_axiom,[])).

fof(f1967,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & r1_tarski(X2,X3) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( k7_relat_1(sK160,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(sK160,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK160) ) ),
    introduced(choice_axiom,[])).

fof(f1970,plain,
    ( k7_relat_1(sK160,sK162) != k7_relat_1(sK161,sK162)
    & k7_relat_1(sK160,sK163) = k7_relat_1(sK161,sK163)
    & r1_tarski(sK162,sK163)
    & v1_relat_1(sK161)
    & v1_relat_1(sK160) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK160,sK161,sK162,sK163])],[f1430,f1969,f1968,f1967])).

fof(f3189,plain,(
    v1_relat_1(sK160) ),
    inference(cnf_transformation,[],[f1970])).

fof(f3191,plain,(
    r1_tarski(sK162,sK163) ),
    inference(cnf_transformation,[],[f1970])).

fof(f693,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1330,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f693])).

fof(f1331,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1330])).

fof(f3095,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1331])).

fof(f3190,plain,(
    v1_relat_1(sK161) ),
    inference(cnf_transformation,[],[f1970])).

fof(f3192,plain,(
    k7_relat_1(sK160,sK163) = k7_relat_1(sK161,sK163) ),
    inference(cnf_transformation,[],[f1970])).

fof(f3193,plain,(
    k7_relat_1(sK160,sK162) != k7_relat_1(sK161,sK162) ),
    inference(cnf_transformation,[],[f1970])).

cnf(c_1192,negated_conjecture,
    ( v1_relat_1(sK160) ),
    inference(cnf_transformation,[],[f3189])).

cnf(c_52558,plain,
    ( v1_relat_1(sK160) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1192])).

cnf(c_1190,negated_conjecture,
    ( r1_tarski(sK162,sK163) ),
    inference(cnf_transformation,[],[f3191])).

cnf(c_52560,plain,
    ( r1_tarski(sK162,sK163) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1190])).

cnf(c_1094,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f3095])).

cnf(c_52643,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X2)
    | r1_tarski(X2,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1094])).

cnf(c_136030,plain,
    ( k7_relat_1(k7_relat_1(X0,sK163),sK162) = k7_relat_1(X0,sK162)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_52560,c_52643])).

cnf(c_138099,plain,
    ( k7_relat_1(k7_relat_1(sK160,sK163),sK162) = k7_relat_1(sK160,sK162) ),
    inference(superposition,[status(thm)],[c_52558,c_136030])).

cnf(c_1191,negated_conjecture,
    ( v1_relat_1(sK161) ),
    inference(cnf_transformation,[],[f3190])).

cnf(c_52559,plain,
    ( v1_relat_1(sK161) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1191])).

cnf(c_138098,plain,
    ( k7_relat_1(k7_relat_1(sK161,sK163),sK162) = k7_relat_1(sK161,sK162) ),
    inference(superposition,[status(thm)],[c_52559,c_136030])).

cnf(c_1189,negated_conjecture,
    ( k7_relat_1(sK160,sK163) = k7_relat_1(sK161,sK163) ),
    inference(cnf_transformation,[],[f3192])).

cnf(c_138116,plain,
    ( k7_relat_1(k7_relat_1(sK160,sK163),sK162) = k7_relat_1(sK161,sK162) ),
    inference(light_normalisation,[status(thm)],[c_138098,c_1189])).

cnf(c_139293,plain,
    ( k7_relat_1(sK161,sK162) = k7_relat_1(sK160,sK162) ),
    inference(demodulation,[status(thm)],[c_138099,c_138116])).

cnf(c_1188,negated_conjecture,
    ( k7_relat_1(sK160,sK162) != k7_relat_1(sK161,sK162) ),
    inference(cnf_transformation,[],[f3193])).

cnf(c_140078,plain,
    ( k7_relat_1(sK160,sK162) != k7_relat_1(sK160,sK162) ),
    inference(demodulation,[status(thm)],[c_139293,c_1188])).

cnf(c_140079,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_140078])).

%------------------------------------------------------------------------------
