%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0389+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:38 EST 2020

% Result     : Theorem 55.15s
% Output     : CNFRefutation 55.15s
% Verified   : 
% Statistics : Number of formulae       :   46 (  67 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 197 expanded)
%              Number of equality atoms :   26 (  48 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f554,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f916,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f554])).

fof(f2119,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f916])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f577,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f946,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f577])).

fof(f947,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f946])).

fof(f948,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f949,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f947,f948])).

fof(f1249,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f949])).

fof(f558,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f921,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f558])).

fof(f922,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f921])).

fof(f1237,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK96(X0,X1))
        & r2_hidden(sK96(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1238,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK96(X0,X1))
        & r2_hidden(sK96(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK96])],[f922,f1237])).

fof(f2124,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK96(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1238])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1248,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2594,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | o_0_0_xboole_0 = X0
      | ~ r1_tarski(X1,sK96(X0,X1)) ) ),
    inference(definition_unfolding,[],[f2124,f1248])).

fof(f2123,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK96(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1238])).

fof(f2595,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | o_0_0_xboole_0 = X0
      | r2_hidden(sK96(X0,X1),X0) ) ),
    inference(definition_unfolding,[],[f2123,f1248])).

fof(f559,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f560,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f559])).

fof(f923,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f560])).

fof(f924,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f923])).

fof(f1239,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK98),k1_setfam_1(sK97))
      & k1_xboole_0 != sK97
      & r1_tarski(sK97,sK98) ) ),
    introduced(choice_axiom,[])).

fof(f1240,plain,
    ( ~ r1_tarski(k1_setfam_1(sK98),k1_setfam_1(sK97))
    & k1_xboole_0 != sK97
    & r1_tarski(sK97,sK98) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK97,sK98])],[f924,f1239])).

fof(f2127,plain,(
    ~ r1_tarski(k1_setfam_1(sK98),k1_setfam_1(sK97)) ),
    inference(cnf_transformation,[],[f1240])).

fof(f2126,plain,(
    k1_xboole_0 != sK97 ),
    inference(cnf_transformation,[],[f1240])).

fof(f2596,plain,(
    o_0_0_xboole_0 != sK97 ),
    inference(definition_unfolding,[],[f2126,f1248])).

fof(f2125,plain,(
    r1_tarski(sK97,sK98) ),
    inference(cnf_transformation,[],[f1240])).

cnf(c_864,plain,
    ( r1_tarski(k1_setfam_1(X0),X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f2119])).

cnf(c_139997,plain,
    ( r1_tarski(k1_setfam_1(sK98),sK96(sK97,k1_setfam_1(sK98)))
    | ~ r2_hidden(sK96(sK97,k1_setfam_1(sK98)),sK98) ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f1249])).

cnf(c_45974,plain,
    ( ~ r1_tarski(sK97,X0)
    | r2_hidden(sK96(sK97,k1_setfam_1(sK98)),X0)
    | ~ r2_hidden(sK96(sK97,k1_setfam_1(sK98)),sK97) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_128429,plain,
    ( ~ r1_tarski(sK97,sK98)
    | ~ r2_hidden(sK96(sK97,k1_setfam_1(sK98)),sK97)
    | r2_hidden(sK96(sK97,k1_setfam_1(sK98)),sK98) ),
    inference(instantiation,[status(thm)],[c_45974])).

cnf(c_868,plain,
    ( ~ r1_tarski(X0,sK96(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f2594])).

cnf(c_29346,plain,
    ( ~ r1_tarski(X0,sK96(sK97,X0))
    | r1_tarski(X0,k1_setfam_1(sK97))
    | o_0_0_xboole_0 = sK97 ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_39844,plain,
    ( ~ r1_tarski(k1_setfam_1(sK98),sK96(sK97,k1_setfam_1(sK98)))
    | r1_tarski(k1_setfam_1(sK98),k1_setfam_1(sK97))
    | o_0_0_xboole_0 = sK97 ),
    inference(instantiation,[status(thm)],[c_29346])).

cnf(c_869,plain,
    ( r1_tarski(X0,k1_setfam_1(X1))
    | r2_hidden(sK96(X1,X0),X1)
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f2595])).

cnf(c_29351,plain,
    ( r1_tarski(X0,k1_setfam_1(sK97))
    | r2_hidden(sK96(sK97,X0),sK97)
    | o_0_0_xboole_0 = sK97 ),
    inference(instantiation,[status(thm)],[c_869])).

cnf(c_38840,plain,
    ( r1_tarski(k1_setfam_1(sK98),k1_setfam_1(sK97))
    | r2_hidden(sK96(sK97,k1_setfam_1(sK98)),sK97)
    | o_0_0_xboole_0 = sK97 ),
    inference(instantiation,[status(thm)],[c_29351])).

cnf(c_870,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(sK98),k1_setfam_1(sK97)) ),
    inference(cnf_transformation,[],[f2127])).

cnf(c_871,negated_conjecture,
    ( o_0_0_xboole_0 != sK97 ),
    inference(cnf_transformation,[],[f2596])).

cnf(c_872,negated_conjecture,
    ( r1_tarski(sK97,sK98) ),
    inference(cnf_transformation,[],[f2125])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_139997,c_128429,c_39844,c_38840,c_870,c_871,c_872])).

%------------------------------------------------------------------------------
