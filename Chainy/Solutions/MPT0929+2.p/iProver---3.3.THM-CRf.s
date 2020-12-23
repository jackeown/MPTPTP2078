%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0929+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:57 EST 2020

% Result     : Theorem 23.67s
% Output     : CNFRefutation 23.67s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  57 expanded)
%              Number of equality atoms :   54 (  56 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1406,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X4
      & k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X3
      & k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X1
      & k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1407,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X4
        & k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X3
        & k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X1
        & k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X0 ) ),
    inference(negated_conjecture,[],[f1406])).

fof(f2832,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X4
      | k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X3
      | k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X1
      | k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X0 ) ),
    inference(ennf_transformation,[],[f1407])).

fof(f3936,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X4
        | k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X3
        | k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X1
        | k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X0 )
   => ( k20_mcart_1(k4_tarski(sK461,k4_tarski(sK459,sK460))) != sK460
      | k19_mcart_1(k4_tarski(sK461,k4_tarski(sK459,sK460))) != sK459
      | k18_mcart_1(k4_tarski(k4_tarski(sK456,sK457),sK458)) != sK457
      | k17_mcart_1(k4_tarski(k4_tarski(sK456,sK457),sK458)) != sK456 ) ),
    introduced(choice_axiom,[])).

fof(f3937,plain,
    ( k20_mcart_1(k4_tarski(sK461,k4_tarski(sK459,sK460))) != sK460
    | k19_mcart_1(k4_tarski(sK461,k4_tarski(sK459,sK460))) != sK459
    | k18_mcart_1(k4_tarski(k4_tarski(sK456,sK457),sK458)) != sK457
    | k17_mcart_1(k4_tarski(k4_tarski(sK456,sK457),sK458)) != sK456 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK456,sK457,sK458,sK459,sK460,sK461])],[f2832,f3936])).

fof(f6470,plain,
    ( k20_mcart_1(k4_tarski(sK461,k4_tarski(sK459,sK460))) != sK460
    | k19_mcart_1(k4_tarski(sK461,k4_tarski(sK459,sK460))) != sK459
    | k18_mcart_1(k4_tarski(k4_tarski(sK456,sK457),sK458)) != sK457
    | k17_mcart_1(k4_tarski(k4_tarski(sK456,sK457),sK458)) != sK456 ),
    inference(cnf_transformation,[],[f3937])).

fof(f1277,axiom,(
    ! [X0] : k2_mcart_1(k2_mcart_1(X0)) = k20_mcart_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6139,plain,(
    ! [X0] : k2_mcart_1(k2_mcart_1(X0)) = k20_mcart_1(X0) ),
    inference(cnf_transformation,[],[f1277])).

fof(f1276,axiom,(
    ! [X0] : k1_mcart_1(k2_mcart_1(X0)) = k19_mcart_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6138,plain,(
    ! [X0] : k1_mcart_1(k2_mcart_1(X0)) = k19_mcart_1(X0) ),
    inference(cnf_transformation,[],[f1276])).

fof(f1275,axiom,(
    ! [X0] : k18_mcart_1(X0) = k2_mcart_1(k1_mcart_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6137,plain,(
    ! [X0] : k18_mcart_1(X0) = k2_mcart_1(k1_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f1275])).

fof(f1274,axiom,(
    ! [X0] : k17_mcart_1(X0) = k1_mcart_1(k1_mcart_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6136,plain,(
    ! [X0] : k17_mcart_1(X0) = k1_mcart_1(k1_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f1274])).

fof(f7416,plain,
    ( k2_mcart_1(k2_mcart_1(k4_tarski(sK461,k4_tarski(sK459,sK460)))) != sK460
    | k1_mcart_1(k2_mcart_1(k4_tarski(sK461,k4_tarski(sK459,sK460)))) != sK459
    | k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK456,sK457),sK458))) != sK457
    | k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK456,sK457),sK458))) != sK456 ),
    inference(definition_unfolding,[],[f6470,f6139,f6138,f6137,f6136])).

fof(f1396,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6426,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f1396])).

fof(f6425,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1396])).

cnf(c_2507,negated_conjecture,
    ( k2_mcart_1(k2_mcart_1(k4_tarski(sK461,k4_tarski(sK459,sK460)))) != sK460
    | k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK456,sK457),sK458))) != sK457
    | k1_mcart_1(k2_mcart_1(k4_tarski(sK461,k4_tarski(sK459,sK460)))) != sK459
    | k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK456,sK457),sK458))) != sK456 ),
    inference(cnf_transformation,[],[f7416])).

cnf(c_2462,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f6426])).

cnf(c_2463,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6425])).

cnf(c_83843,plain,
    ( sK457 != sK457
    | sK456 != sK456
    | sK460 != sK460
    | sK459 != sK459 ),
    inference(demodulation,[status(thm)],[c_2507,c_2462,c_2463])).

cnf(c_83844,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_83843])).

%------------------------------------------------------------------------------
