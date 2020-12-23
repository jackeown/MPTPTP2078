%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0386+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:38 EST 2020

% Result     : Theorem 19.54s
% Output     : CNFRefutation 19.54s
% Verified   : 
% Statistics : Number of formulae       :   64 (  77 expanded)
%              Number of clauses        :   24 (  24 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  256 ( 298 expanded)
%              Number of equality atoms :   54 (  56 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f908,plain,(
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

fof(f1218,plain,(
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
    inference(nnf_transformation,[],[f908])).

fof(f1219,plain,(
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
    inference(rectify,[],[f1218])).

fof(f1222,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK93(X0,X5))
        & r2_hidden(sK93(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1221,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK92(X0,X1))
        & r2_hidden(sK92(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1220,plain,(
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

fof(f1223,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK91,sK92,sK93])],[f1219,f1222,f1221,f1220])).

fof(f2090,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1223])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1238,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2576,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f2090,f1238])).

fof(f2718,plain,(
    ! [X0,X7,X5] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,k1_setfam_1(X0))
      | o_0_0_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f2576])).

fof(f131,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1407,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f131])).

fof(f2233,plain,(
    ! [X0] : r1_xboole_0(X0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f1407,f1238])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f576,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f1274,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f576])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f561,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f580,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f561])).

fof(f971,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK19(X0,X1),X1)
        & r2_hidden(sK19(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f972,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK19(X0,X1),X1)
          & r2_hidden(sK19(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f580,f971])).

fof(f1287,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f972])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f574,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f938,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f574])).

fof(f939,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f938])).

fof(f940,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f941,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f939,f940])).

fof(f1240,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f941])).

fof(f1241,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f941])).

fof(f554,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f555,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f554])).

fof(f913,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),X0)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f555])).

fof(f1229,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),X0)
        & r2_hidden(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK97),sK96)
      & r2_hidden(sK96,sK97) ) ),
    introduced(choice_axiom,[])).

fof(f1230,plain,
    ( ~ r1_tarski(k1_setfam_1(sK97),sK96)
    & r2_hidden(sK96,sK97) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK96,sK97])],[f913,f1229])).

fof(f2110,plain,(
    ~ r1_tarski(k1_setfam_1(sK97),sK96) ),
    inference(cnf_transformation,[],[f1230])).

fof(f2109,plain,(
    r2_hidden(sK96,sK97) ),
    inference(cnf_transformation,[],[f1230])).

cnf(c_852,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f2718])).

cnf(c_46678,plain,
    ( ~ r2_hidden(X0,sK97)
    | r2_hidden(sK11(k1_setfam_1(sK97),sK96),X0)
    | ~ r2_hidden(sK11(k1_setfam_1(sK97),sK96),k1_setfam_1(sK97))
    | o_0_0_xboole_0 = sK97 ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_69584,plain,
    ( ~ r2_hidden(sK11(k1_setfam_1(sK97),sK96),k1_setfam_1(sK97))
    | r2_hidden(sK11(k1_setfam_1(sK97),sK96),sK96)
    | ~ r2_hidden(sK96,sK97)
    | o_0_0_xboole_0 = sK97 ),
    inference(instantiation,[status(thm)],[c_46678])).

cnf(c_175,plain,
    ( r1_xboole_0(X0,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2233])).

cnf(c_65551,plain,
    ( r1_xboole_0(sK97,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_175])).

cnf(c_44,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1274])).

cnf(c_57726,plain,
    ( r1_xboole_0(X0,sK97)
    | ~ r1_xboole_0(sK97,X0) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_57728,plain,
    ( ~ r1_xboole_0(sK97,o_0_0_xboole_0)
    | r1_xboole_0(o_0_0_xboole_0,sK97) ),
    inference(instantiation,[status(thm)],[c_57726])).

cnf(c_25517,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_49669,plain,
    ( sK96 = sK96 ),
    inference(instantiation,[status(thm)],[c_25517])).

cnf(c_25522,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_42876,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK96,sK97)
    | X0 != sK96
    | X1 != sK97 ),
    inference(instantiation,[status(thm)],[c_25522])).

cnf(c_49668,plain,
    ( r2_hidden(sK96,X0)
    | ~ r2_hidden(sK96,sK97)
    | X0 != sK97
    | sK96 != sK96 ),
    inference(instantiation,[status(thm)],[c_42876])).

cnf(c_49671,plain,
    ( ~ r2_hidden(sK96,sK97)
    | r2_hidden(sK96,o_0_0_xboole_0)
    | sK96 != sK96
    | o_0_0_xboole_0 != sK97 ),
    inference(instantiation,[status(thm)],[c_49668])).

cnf(c_55,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f1287])).

cnf(c_40378,plain,
    ( ~ r1_xboole_0(X0,sK97)
    | ~ r2_hidden(sK96,X0)
    | ~ r2_hidden(sK96,sK97) ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_40380,plain,
    ( ~ r1_xboole_0(o_0_0_xboole_0,sK97)
    | ~ r2_hidden(sK96,sK97)
    | ~ r2_hidden(sK96,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_40378])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK11(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1240])).

cnf(c_39966,plain,
    ( r1_tarski(k1_setfam_1(sK97),sK96)
    | r2_hidden(sK11(k1_setfam_1(sK97),sK96),k1_setfam_1(sK97)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK11(X0,X1),X1) ),
    inference(cnf_transformation,[],[f1241])).

cnf(c_39958,plain,
    ( r1_tarski(k1_setfam_1(sK97),sK96)
    | ~ r2_hidden(sK11(k1_setfam_1(sK97),sK96),sK96) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_864,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(sK97),sK96) ),
    inference(cnf_transformation,[],[f2110])).

cnf(c_865,negated_conjecture,
    ( r2_hidden(sK96,sK97) ),
    inference(cnf_transformation,[],[f2109])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_69584,c_65551,c_57728,c_49669,c_49671,c_40380,c_39966,c_39958,c_864,c_865])).

%------------------------------------------------------------------------------
