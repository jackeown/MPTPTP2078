%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0399+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:39 EST 2020

% Result     : Theorem 43.27s
% Output     : CNFRefutation 43.27s
% Verified   : 
% Statistics : Number of formulae       :   46 (  57 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 128 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f682,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f1476,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f682])).

fof(f545,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f928,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f545])).

fof(f1260,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f928])).

fof(f1261,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f1260])).

fof(f1263,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK95(X1,X4))
        & r2_hidden(sK95(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f1262,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK94(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK94(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1264,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK94(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK94(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK95(X1,X4))
              & r2_hidden(sK95(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK94,sK95])],[f1261,f1263,f1262])).

fof(f2147,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK95(X1,X4),X1)
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f1264])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f603,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f1013,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK22(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1014,plain,(
    ! [X0] :
      ( r2_hidden(sK22(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f603,f1013])).

fof(f1345,plain,(
    ! [X0] :
      ( r2_hidden(sK22(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1014])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1287,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2227,plain,(
    ! [X0] :
      ( r2_hidden(sK22(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f1345,f1287])).

fof(f476,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2036,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f476])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1973,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f2196,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f1973,f1287])).

fof(f2613,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2036,f2196])).

fof(f561,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f562,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f561])).

fof(f937,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f562])).

fof(f1275,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK100
      & r1_setfam_1(sK100,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f1276,plain,
    ( k1_xboole_0 != sK100
    & r1_setfam_1(sK100,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK100])],[f937,f1275])).

fof(f2171,plain,(
    k1_xboole_0 != sK100 ),
    inference(cnf_transformation,[],[f1276])).

fof(f2654,plain,(
    o_0_0_xboole_0 != sK100 ),
    inference(definition_unfolding,[],[f2171,f1287])).

fof(f2170,plain,(
    r1_setfam_1(sK100,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1276])).

fof(f2655,plain,(
    r1_setfam_1(sK100,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2170,f1287])).

cnf(c_195,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f1476])).

cnf(c_87020,plain,
    ( ~ r2_hidden(sK95(X0,sK22(sK100)),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_87102,plain,
    ( ~ r2_hidden(sK95(o_0_0_xboole_0,sK22(sK100)),o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_87020])).

cnf(c_856,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(sK95(X1,X2),X1) ),
    inference(cnf_transformation,[],[f2147])).

cnf(c_36552,plain,
    ( ~ r1_setfam_1(sK100,X0)
    | r2_hidden(sK95(X0,sK22(sK100)),X0)
    | ~ r2_hidden(sK22(sK100),sK100) ),
    inference(instantiation,[status(thm)],[c_856])).

cnf(c_36559,plain,
    ( ~ r1_setfam_1(sK100,o_0_0_xboole_0)
    | r2_hidden(sK95(o_0_0_xboole_0,sK22(sK100)),o_0_0_xboole_0)
    | ~ r2_hidden(sK22(sK100),sK100) ),
    inference(instantiation,[status(thm)],[c_36552])).

cnf(c_66,plain,
    ( r2_hidden(sK22(X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f2227])).

cnf(c_28999,plain,
    ( r2_hidden(sK22(sK100),sK100)
    | o_0_0_xboole_0 = sK100 ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_743,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2613])).

cnf(c_876,negated_conjecture,
    ( o_0_0_xboole_0 != sK100 ),
    inference(cnf_transformation,[],[f2654])).

cnf(c_877,negated_conjecture,
    ( r1_setfam_1(sK100,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2655])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_87102,c_36559,c_28999,c_743,c_876,c_877])).

%------------------------------------------------------------------------------
