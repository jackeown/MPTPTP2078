%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0933+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:27 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   38 (  89 expanded)
%              Number of clauses        :   21 (  25 expanded)
%              Number of leaves         :    4 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  100 ( 434 expanded)
%              Number of equality atoms :   56 ( 226 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( k2_mcart_1(X0) = k2_mcart_1(X2)
            & k1_mcart_1(X0) = k1_mcart_1(X2)
            & r2_hidden(X0,X1)
            & r2_hidden(X2,X1) )
         => X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( ( k2_mcart_1(X0) = k2_mcart_1(X2)
              & k1_mcart_1(X0) = k1_mcart_1(X2)
              & r2_hidden(X0,X1)
              & r2_hidden(X2,X1) )
           => X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X0 != X2
          & k2_mcart_1(X0) = k2_mcart_1(X2)
          & k1_mcart_1(X0) = k1_mcart_1(X2)
          & r2_hidden(X0,X1)
          & r2_hidden(X2,X1) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X0 != X2
          & k2_mcart_1(X0) = k2_mcart_1(X2)
          & k1_mcart_1(X0) = k1_mcart_1(X2)
          & r2_hidden(X0,X1)
          & r2_hidden(X2,X1) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X0 != X2
          & k2_mcart_1(X0) = k2_mcart_1(X2)
          & k1_mcart_1(X0) = k1_mcart_1(X2)
          & r2_hidden(X0,X1)
          & r2_hidden(X2,X1) )
     => ( sK2 != X0
        & k2_mcart_1(sK2) = k2_mcart_1(X0)
        & k1_mcart_1(sK2) = k1_mcart_1(X0)
        & r2_hidden(X0,X1)
        & r2_hidden(sK2,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X0 != X2
            & k2_mcart_1(X0) = k2_mcart_1(X2)
            & k1_mcart_1(X0) = k1_mcart_1(X2)
            & r2_hidden(X0,X1)
            & r2_hidden(X2,X1) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( sK0 != X2
          & k2_mcart_1(sK0) = k2_mcart_1(X2)
          & k1_mcart_1(sK0) = k1_mcart_1(X2)
          & r2_hidden(sK0,sK1)
          & r2_hidden(X2,sK1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( sK0 != sK2
    & k2_mcart_1(sK0) = k2_mcart_1(sK2)
    & k1_mcart_1(sK0) = k1_mcart_1(sK2)
    & r2_hidden(sK0,sK1)
    & r2_hidden(sK2,sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9,f8])).

fof(f13,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f5,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f4])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    k1_mcart_1(sK0) = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    k2_mcart_1(sK0) = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

cnf(c_5,negated_conjecture,
    ( r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_6,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_49,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_50,plain,
    ( ~ r2_hidden(X0,sK1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_49])).

cnf(c_69,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_50])).

cnf(c_70,plain,
    ( k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_69])).

cnf(c_81,plain,
    ( k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) = sK2 ),
    inference(subtyping,[status(esa)],[c_70])).

cnf(c_4,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_64,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | sK1 != sK1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_50])).

cnf(c_65,plain,
    ( k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) = sK0 ),
    inference(unflattening,[status(thm)],[c_64])).

cnf(c_82,plain,
    ( k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) = sK0 ),
    inference(subtyping,[status(esa)],[c_65])).

cnf(c_3,negated_conjecture,
    ( k1_mcart_1(sK0) = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_83,negated_conjecture,
    ( k1_mcart_1(sK0) = k1_mcart_1(sK2) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2,negated_conjecture,
    ( k2_mcart_1(sK0) = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_84,negated_conjecture,
    ( k2_mcart_1(sK0) = k2_mcart_1(sK2) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_101,plain,
    ( sK2 = sK0 ),
    inference(light_normalisation,[status(thm)],[c_81,c_82,c_83,c_84])).

cnf(c_1,negated_conjecture,
    ( sK0 != sK2 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_85,negated_conjecture,
    ( sK0 != sK2 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_104,plain,
    ( sK0 != sK0 ),
    inference(demodulation,[status(thm)],[c_101,c_85])).

cnf(c_105,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_104])).


%------------------------------------------------------------------------------
