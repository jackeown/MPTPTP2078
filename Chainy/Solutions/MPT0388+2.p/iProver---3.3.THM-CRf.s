%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0388+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:38 EST 2020

% Result     : Theorem 23.62s
% Output     : CNFRefutation 23.62s
% Verified   : 
% Statistics : Number of formulae       :   53 (  89 expanded)
%              Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  230 ( 442 expanded)
%              Number of equality atoms :   62 ( 114 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f576,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f943,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f576])).

fof(f944,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f943])).

fof(f945,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f946,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f944,f945])).

fof(f1244,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f946])).

fof(f558,conjecture,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f559,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r1_tarski(X1,X2) )
       => ( r1_tarski(X1,k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f558])).

fof(f920,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X1,k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f559])).

fof(f921,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X1,k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f920])).

fof(f1234,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X1,k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & ! [X2] :
            ( r1_tarski(X1,X2)
            | ~ r2_hidden(X2,X0) ) )
   => ( ~ r1_tarski(sK97,k1_setfam_1(sK96))
      & k1_xboole_0 != sK96
      & ! [X2] :
          ( r1_tarski(sK97,X2)
          | ~ r2_hidden(X2,sK96) ) ) ),
    introduced(choice_axiom,[])).

fof(f1235,plain,
    ( ~ r1_tarski(sK97,k1_setfam_1(sK96))
    & k1_xboole_0 != sK96
    & ! [X2] :
        ( r1_tarski(sK97,X2)
        | ~ r2_hidden(X2,sK96) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK96,sK97])],[f921,f1234])).

fof(f2118,plain,(
    ! [X2] :
      ( r1_tarski(sK97,X2)
      | ~ r2_hidden(X2,sK96) ) ),
    inference(cnf_transformation,[],[f1235])).

fof(f544,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f910,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f544])).

fof(f1223,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f910])).

fof(f1224,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f1223])).

fof(f1227,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK93(X0,X5))
        & r2_hidden(sK93(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1226,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK92(X0,X1))
        & r2_hidden(sK92(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1225,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK91(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK91(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK91(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK91(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1228,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK91(X0,X1),sK92(X0,X1))
                  & r2_hidden(sK92(X0,X1),X0) )
                | ~ r2_hidden(sK91(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK91(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK91(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK93(X0,X5))
                    & r2_hidden(sK93(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK91,sK92,sK93])],[f1224,f1227,f1226,f1225])).

fof(f2097,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK93(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1228])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1243,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2582,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK93(X0,X5))
      | k1_setfam_1(X0) != X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f2097,f1243])).

fof(f2726,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X5,sK93(X0,X5))
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f2582])).

fof(f2096,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK93(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1228])).

fof(f2583,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK93(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f2096,f1243])).

fof(f2727,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK93(X0,X5),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f2583])).

fof(f1245,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f946])).

fof(f1246,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f946])).

fof(f2120,plain,(
    ~ r1_tarski(sK97,k1_setfam_1(sK96)) ),
    inference(cnf_transformation,[],[f1235])).

fof(f2119,plain,(
    k1_xboole_0 != sK96 ),
    inference(cnf_transformation,[],[f1235])).

fof(f2587,plain,(
    o_0_0_xboole_0 != sK96 ),
    inference(definition_unfolding,[],[f2119,f1243])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f1244])).

cnf(c_48804,plain,
    ( ~ r1_tarski(sK97,X0)
    | r2_hidden(sK11(sK97,k1_setfam_1(sK96)),X0)
    | ~ r2_hidden(sK11(sK97,k1_setfam_1(sK96)),sK97) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_79327,plain,
    ( ~ r1_tarski(sK97,sK93(sK96,sK11(sK97,k1_setfam_1(sK96))))
    | r2_hidden(sK11(sK97,k1_setfam_1(sK96)),sK93(sK96,sK11(sK97,k1_setfam_1(sK96))))
    | ~ r2_hidden(sK11(sK97,k1_setfam_1(sK96)),sK97) ),
    inference(instantiation,[status(thm)],[c_48804])).

cnf(c_870,negated_conjecture,
    ( r1_tarski(sK97,X0)
    | ~ r2_hidden(X0,sK96) ),
    inference(cnf_transformation,[],[f2118])).

cnf(c_67619,plain,
    ( r1_tarski(sK97,sK93(sK96,sK11(sK97,k1_setfam_1(sK96))))
    | ~ r2_hidden(sK93(sK96,sK11(sK97,k1_setfam_1(sK96))),sK96) ),
    inference(instantiation,[status(thm)],[c_870])).

cnf(c_850,plain,
    ( ~ r2_hidden(X0,sK93(X1,X0))
    | r2_hidden(X0,k1_setfam_1(X1))
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f2726])).

cnf(c_45006,plain,
    ( ~ r2_hidden(X0,sK93(sK96,X0))
    | r2_hidden(X0,k1_setfam_1(sK96))
    | o_0_0_xboole_0 = sK96 ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_51348,plain,
    ( ~ r2_hidden(sK11(sK97,k1_setfam_1(sK96)),sK93(sK96,sK11(sK97,k1_setfam_1(sK96))))
    | r2_hidden(sK11(sK97,k1_setfam_1(sK96)),k1_setfam_1(sK96))
    | o_0_0_xboole_0 = sK96 ),
    inference(instantiation,[status(thm)],[c_45006])).

cnf(c_851,plain,
    ( r2_hidden(X0,k1_setfam_1(X1))
    | r2_hidden(sK93(X1,X0),X1)
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f2727])).

cnf(c_45011,plain,
    ( r2_hidden(X0,k1_setfam_1(sK96))
    | r2_hidden(sK93(sK96,X0),sK96)
    | o_0_0_xboole_0 = sK96 ),
    inference(instantiation,[status(thm)],[c_851])).

cnf(c_50618,plain,
    ( r2_hidden(sK93(sK96,sK11(sK97,k1_setfam_1(sK96))),sK96)
    | r2_hidden(sK11(sK97,k1_setfam_1(sK96)),k1_setfam_1(sK96))
    | o_0_0_xboole_0 = sK96 ),
    inference(instantiation,[status(thm)],[c_45011])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK11(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1245])).

cnf(c_43738,plain,
    ( r1_tarski(sK97,k1_setfam_1(sK96))
    | r2_hidden(sK11(sK97,k1_setfam_1(sK96)),sK97) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK11(X0,X1),X1) ),
    inference(cnf_transformation,[],[f1246])).

cnf(c_43730,plain,
    ( r1_tarski(sK97,k1_setfam_1(sK96))
    | ~ r2_hidden(sK11(sK97,k1_setfam_1(sK96)),k1_setfam_1(sK96)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_868,negated_conjecture,
    ( ~ r1_tarski(sK97,k1_setfam_1(sK96)) ),
    inference(cnf_transformation,[],[f2120])).

cnf(c_869,negated_conjecture,
    ( o_0_0_xboole_0 != sK96 ),
    inference(cnf_transformation,[],[f2587])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_79327,c_67619,c_51348,c_50618,c_43738,c_43730,c_868,c_869])).

%------------------------------------------------------------------------------
