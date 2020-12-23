%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0212+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:27 EST 2020

% Result     : Theorem 8.06s
% Output     : CNFRefutation 8.06s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 122 expanded)
%              Number of clauses        :   36 (  36 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  352 ( 528 expanded)
%              Number of equality atoms :  201 ( 316 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f639,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f513,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f969,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f639,f513])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f477,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f175])).

fof(f478,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f477])).

fof(f479,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK20(X0,X1) != X0
          | ~ r2_hidden(sK20(X0,X1),X1) )
        & ( sK20(X0,X1) = X0
          | r2_hidden(sK20(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f480,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK20(X0,X1) != X0
            | ~ r2_hidden(sK20(X0,X1),X1) )
          & ( sK20(X0,X1) = X0
            | r2_hidden(sK20(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f478,f479])).

fof(f739,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK20(X0,X1) = X0
      | r2_hidden(sK20(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f480])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f457,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f458,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f457])).

fof(f574,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f458])).

fof(f284,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f502,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f284])).

fof(f503,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f502])).

fof(f504,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK24(X0,X1),X0)
          | ~ r2_hidden(sK24(X0,X1),X1) )
        & ( r1_tarski(sK24(X0,X1),X0)
          | r2_hidden(sK24(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f505,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK24(X0,X1),X0)
            | ~ r2_hidden(sK24(X0,X1),X1) )
          & ( r1_tarski(sK24(X0,X1),X0)
            | r2_hidden(sK24(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f503,f504])).

fof(f875,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f505])).

fof(f1184,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f875])).

fof(f876,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f505])).

fof(f1183,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f876])).

fof(f740,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK20(X0,X1) != X0
      | ~ r2_hidden(sK20(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f480])).

fof(f132,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f367,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f683,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f367])).

fof(f1001,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(definition_unfolding,[],[f683,f513])).

fof(f1146,plain,(
    r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f1001])).

fof(f141,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f380,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f141])).

fof(f381,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f380])).

fof(f695,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f381])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f721,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f661,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f881,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f721,f661])).

fof(f1010,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ) ),
    inference(definition_unfolding,[],[f695,f881])).

fof(f149,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f703,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f149])).

fof(f1016,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f703,f881])).

fof(f153,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f471,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f153])).

fof(f708,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f471])).

fof(f707,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f471])).

fof(f409,plain,(
    ! [X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP2(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X9 = X11
        | X8 = X11
        | X7 = X11
        | X6 = X11
        | X5 = X11
        | X4 = X11
        | X3 = X11
        | X2 = X11
        | X1 = X11
        | X0 = X11 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f498,plain,(
    ! [X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP2(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X9 != X11
          & X8 != X11
          & X7 != X11
          & X6 != X11
          & X5 != X11
          & X4 != X11
          & X3 != X11
          & X2 != X11
          & X1 != X11
          & X0 != X11 ) )
      & ( X9 = X11
        | X8 = X11
        | X7 = X11
        | X6 = X11
        | X5 = X11
        | X4 = X11
        | X3 = X11
        | X2 = X11
        | X1 = X11
        | X0 = X11
        | ~ sP2(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f409])).

fof(f499,plain,(
    ! [X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP2(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X9 != X11
          & X8 != X11
          & X7 != X11
          & X6 != X11
          & X5 != X11
          & X4 != X11
          & X3 != X11
          & X2 != X11
          & X1 != X11
          & X0 != X11 ) )
      & ( X9 = X11
        | X8 = X11
        | X7 = X11
        | X6 = X11
        | X5 = X11
        | X4 = X11
        | X3 = X11
        | X2 = X11
        | X1 = X11
        | X0 = X11
        | ~ sP2(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f498])).

fof(f500,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( ( sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8
          & X0 != X9
          & X0 != X10 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | X0 = X9
        | X0 = X10
        | ~ sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ) ) ),
    inference(rectify,[],[f499])).

fof(f768,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
      | X0 != X10 ) ),
    inference(cnf_transformation,[],[f500])).

fof(f1181,plain,(
    ! [X6,X4,X2,X10,X8,X7,X5,X3,X1,X9] : sP2(X10,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ),
    inference(equality_resolution,[],[f768])).

fof(f767,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( X0 = X1
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X6
      | X0 = X7
      | X0 = X8
      | X0 = X9
      | X0 = X10
      | ~ sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ) ),
    inference(cnf_transformation,[],[f500])).

fof(f287,conjecture,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f288,negated_conjecture,(
    k1_tarski(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f287])).

fof(f295,plain,(
    k1_tarski(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(flattening,[],[f288])).

fof(f880,plain,(
    k1_tarski(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f295])).

fof(f1132,plain,(
    k1_tarski(o_0_0_xboole_0) != k1_zfmisc_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f880,f513,f513])).

cnf(c_133,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f969])).

cnf(c_17800,plain,
    ( r1_tarski(o_0_0_xboole_0,sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_230,plain,
    ( r2_hidden(sK20(X0,X1),X1)
    | sK20(X0,X1) = X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f739])).

cnf(c_14903,plain,
    ( r2_hidden(sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0))
    | sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) = o_0_0_xboole_0
    | k1_tarski(o_0_0_xboole_0) = k1_zfmisc_1(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f574])).

cnf(c_14869,plain,
    ( ~ r1_tarski(sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ r1_tarski(o_0_0_xboole_0,sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)))
    | sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_6895,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_13687,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) != X0
    | o_0_0_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_6895])).

cnf(c_13688,plain,
    ( sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) != X0
    | o_0_0_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13687])).

cnf(c_13690,plain,
    ( sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) != o_0_0_xboole_0
    | o_0_0_xboole_0 != o_0_0_xboole_0
    | r1_tarski(sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) = iProver_top
    | r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13688])).

cnf(c_360,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f1184])).

cnf(c_13653,plain,
    ( r1_tarski(sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ r2_hidden(sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_359,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f1183])).

cnf(c_12206,plain,
    ( ~ r1_tarski(sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | r2_hidden(sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_12207,plain,
    ( r1_tarski(sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) != iProver_top
    | r2_hidden(sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12206])).

cnf(c_229,plain,
    ( ~ r2_hidden(sK20(X0,X1),X1)
    | sK20(X0,X1) != X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f740])).

cnf(c_11788,plain,
    ( ~ r2_hidden(sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0))
    | sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) != o_0_0_xboole_0
    | k1_tarski(o_0_0_xboole_0) = k1_zfmisc_1(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_11789,plain,
    ( sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) != o_0_0_xboole_0
    | k1_tarski(o_0_0_xboole_0) = k1_zfmisc_1(o_0_0_xboole_0)
    | r2_hidden(sK20(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11788])).

cnf(c_177,plain,
    ( r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1146])).

cnf(c_188,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(X2,X1),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ),
    inference(cnf_transformation,[],[f1010])).

cnf(c_598,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(X0,k5_xboole_0(k5_xboole_0(X2,X1),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_188])).

cnf(c_600,plain,
    ( r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | r1_tarski(o_0_0_xboole_0,k5_xboole_0(k5_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0),k4_xboole_0(o_0_0_xboole_0,k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)))) != iProver_top
    | r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_598])).

cnf(c_196,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(cnf_transformation,[],[f1016])).

cnf(c_574,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_196])).

cnf(c_576,plain,
    ( r1_tarski(o_0_0_xboole_0,k5_xboole_0(k5_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0),k4_xboole_0(o_0_0_xboole_0,k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_200,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f708])).

cnf(c_564,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_200])).

cnf(c_566,plain,
    ( k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_201,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f707])).

cnf(c_562,plain,
    ( ~ r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
    | k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_268,plain,
    ( sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X0) ),
    inference(cnf_transformation,[],[f1181])).

cnf(c_427,plain,
    ( sP2(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_268])).

cnf(c_269,plain,
    ( ~ sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
    | X1 = X0
    | X2 = X0
    | X5 = X0
    | X3 = X0
    | X4 = X0
    | X9 = X0
    | X8 = X0
    | X7 = X0
    | X6 = X0
    | X10 = X0 ),
    inference(cnf_transformation,[],[f767])).

cnf(c_424,plain,
    ( ~ sP2(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_362,negated_conjecture,
    ( k1_tarski(o_0_0_xboole_0) != k1_zfmisc_1(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1132])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17800,c_14903,c_14869,c_13690,c_13653,c_12207,c_11789,c_177,c_600,c_576,c_566,c_562,c_427,c_424,c_362])).

%------------------------------------------------------------------------------
