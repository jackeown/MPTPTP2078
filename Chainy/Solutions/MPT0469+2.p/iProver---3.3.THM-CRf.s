%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0469+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:40 EST 2020

% Result     : Theorem 27.13s
% Output     : CNFRefutation 27.13s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 198 expanded)
%              Number of clauses        :   31 (  54 expanded)
%              Number of leaves         :   20 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  253 ( 538 expanded)
%              Number of equality atoms :  112 ( 262 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f640,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1141,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f640])).

fof(f1584,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f1141])).

fof(f1585,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f1584])).

fof(f1587,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK126(X4),sK127(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f1586,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK125(X0)
        & r2_hidden(sK125(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1588,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK125(X0)
          & r2_hidden(sK125(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK126(X4),sK127(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK125,sK126,sK127])],[f1585,f1587,f1586])).

fof(f2634,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK125(X0),X0) ) ),
    inference(cnf_transformation,[],[f1588])).

fof(f643,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1597,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f643])).

fof(f1598,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f1597])).

fof(f1601,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK134(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1600,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK133(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1599,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK132(X0,X1),X3),X0)
          | ~ r2_hidden(sK132(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK132(X0,X1),X4),X0)
          | r2_hidden(sK132(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1602,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK132(X0,X1),X3),X0)
            | ~ r2_hidden(sK132(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK132(X0,X1),sK133(X0,X1)),X0)
            | r2_hidden(sK132(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK134(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK132,sK133,sK134])],[f1598,f1601,f1600,f1599])).

fof(f2643,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK134(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1602])).

fof(f3404,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK134(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f2643])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1375,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f1376,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f1375])).

fof(f2089,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f1376])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1634,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3004,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f2089,f1634,f1634])).

fof(f3309,plain,(
    ! [X0] : o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f3004])).

fof(f369,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2158,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f369])).

fof(f700,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1208,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f700])).

fof(f1209,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1208])).

fof(f1625,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK147(X0),sK148(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1626,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK147(X0),sK148(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK147,sK148])],[f1209,f1625])).

fof(f2718,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK147(X0),sK148(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1626])).

fof(f3239,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | r2_hidden(k4_tarski(sK147(X0),sK148(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f2718,f1634])).

fof(f644,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1603,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f644])).

fof(f1604,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f1603])).

fof(f1607,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK137(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1606,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK136(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1605,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK135(X0,X1)),X0)
          | ~ r2_hidden(sK135(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK135(X0,X1)),X0)
          | r2_hidden(sK135(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1608,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK135(X0,X1)),X0)
            | ~ r2_hidden(sK135(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK136(X0,X1),sK135(X0,X1)),X0)
            | r2_hidden(sK135(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK137(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK135,sK136,sK137])],[f1604,f1607,f1606,f1605])).

fof(f2647,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK137(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1608])).

fof(f3406,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK137(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f2647])).

fof(f592,axiom,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2575,plain,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f592])).

fof(f3199,plain,(
    ! [X0] : r1_setfam_1(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f2575,f1634])).

fof(f593,axiom,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1084,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f593])).

fof(f2576,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f1084])).

fof(f3200,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_setfam_1(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f2576,f1634,f1634])).

fof(f701,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f702,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f701])).

fof(f1210,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f702])).

fof(f2719,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1210])).

fof(f3240,plain,
    ( o_0_0_xboole_0 != k2_relat_1(o_0_0_xboole_0)
    | o_0_0_xboole_0 != k1_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2719,f1634,f1634,f1634,f1634])).

cnf(c_993,plain,
    ( r2_hidden(sK125(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f2634])).

cnf(c_46192,plain,
    ( r2_hidden(sK125(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_993])).

cnf(c_1005,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK134(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f3404])).

cnf(c_46182,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK134(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1005])).

cnf(c_448,plain,
    ( k2_zfmisc_1(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3309])).

cnf(c_519,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2158])).

cnf(c_46466,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_61292,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_448,c_46466])).

cnf(c_96570,plain,
    ( r2_hidden(X0,k1_relat_1(o_0_0_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_46182,c_61292])).

cnf(c_97033,plain,
    ( v1_relat_1(k1_relat_1(o_0_0_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_46192,c_96570])).

cnf(c_1077,plain,
    ( r2_hidden(k4_tarski(sK147(X0),sK148(X0)),X0)
    | ~ v1_relat_1(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3239])).

cnf(c_46123,plain,
    ( o_0_0_xboole_0 = X0
    | r2_hidden(k4_tarski(sK147(X0),sK148(X0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1077])).

cnf(c_97037,plain,
    ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | v1_relat_1(k1_relat_1(o_0_0_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_46123,c_96570])).

cnf(c_97052,plain,
    ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_97033,c_97037])).

cnf(c_1009,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK137(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f3406])).

cnf(c_46178,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK137(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1009])).

cnf(c_89988,plain,
    ( r2_hidden(X0,k2_relat_1(o_0_0_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_46178,c_61292])).

cnf(c_90843,plain,
    ( v1_relat_1(k2_relat_1(o_0_0_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_46192,c_89988])).

cnf(c_90845,plain,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | v1_relat_1(k2_relat_1(o_0_0_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_46123,c_89988])).

cnf(c_90854,plain,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_90843,c_90845])).

cnf(c_30093,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_76295,plain,
    ( k2_relat_1(o_0_0_xboole_0) != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_30093])).

cnf(c_76306,plain,
    ( k2_relat_1(o_0_0_xboole_0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_76295])).

cnf(c_55037,plain,
    ( k1_relat_1(o_0_0_xboole_0) != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_30093])).

cnf(c_55038,plain,
    ( k1_relat_1(o_0_0_xboole_0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_55037])).

cnf(c_934,plain,
    ( r1_setfam_1(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3199])).

cnf(c_1470,plain,
    ( r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_935,plain,
    ( ~ r1_setfam_1(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3200])).

cnf(c_1467,plain,
    ( ~ r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_1078,negated_conjecture,
    ( o_0_0_xboole_0 != k2_relat_1(o_0_0_xboole_0)
    | o_0_0_xboole_0 != k1_relat_1(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3240])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_97052,c_90854,c_76306,c_55038,c_1470,c_1467,c_1078])).

%------------------------------------------------------------------------------
