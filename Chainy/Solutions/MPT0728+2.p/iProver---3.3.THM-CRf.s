%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0728+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:51 EST 2020

% Result     : Theorem 31.34s
% Output     : CNFRefutation 31.34s
% Verified   : 
% Statistics : Number of formulae       :   48 (  59 expanded)
%              Number of clauses        :   14 (  16 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 (  92 expanded)
%              Number of equality atoms :   20 (  31 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1104,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f2828,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1104])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2158,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f2159,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2158])).

fof(f2797,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2159])).

fof(f5111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2797])).

fof(f106,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1138,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f106])).

fof(f2882,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f1138])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2946,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2886,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f4455,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f2946,f2886])).

fof(f4559,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f2882,f4455])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2943,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2735,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f395,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2278,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f395])).

fof(f3296,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f2278])).

fof(f1058,conjecture,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1059,negated_conjecture,(
    ~ ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(negated_conjecture,[],[f1058])).

fof(f2079,plain,(
    ? [X0] : ~ r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(ennf_transformation,[],[f1059])).

fof(f2729,plain,
    ( ? [X0] : ~ r2_hidden(X0,k1_ordinal1(X0))
   => ~ r2_hidden(sK235,k1_ordinal1(sK235)) ),
    introduced(choice_axiom,[])).

fof(f2730,plain,(
    ~ r2_hidden(sK235,k1_ordinal1(sK235)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK235])],[f2079,f2729])).

fof(f4449,plain,(
    ~ r2_hidden(sK235,k1_ordinal1(sK235)) ),
    inference(cnf_transformation,[],[f2730])).

fof(f1054,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4446,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f1054])).

fof(f4467,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,k1_tarski(X0)),k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(X0)))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f4446,f4455])).

fof(f5099,plain,(
    ~ r2_hidden(sK235,k5_xboole_0(k5_xboole_0(sK235,k1_tarski(sK235)),k4_xboole_0(sK235,k4_xboole_0(sK235,k1_tarski(sK235))))) ),
    inference(definition_unfolding,[],[f4449,f4467])).

cnf(c_97,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f2828])).

cnf(c_99914,plain,
    ( r1_tarski(k4_xboole_0(k1_tarski(sK235),sK235),k1_tarski(sK235))
    | ~ r1_tarski(k1_tarski(sK235),k1_tarski(sK235)) ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_69,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5111])).

cnf(c_92773,plain,
    ( r1_tarski(k1_tarski(sK235),k1_tarski(sK235)) ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_151,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4559])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2943])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2735])).

cnf(c_46765,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(theory_normalisation,[status(thm)],[c_151,c_211,c_7])).

cnf(c_74977,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_tarski(sK235),sK235),k1_tarski(sK235))
    | r1_tarski(k1_tarski(sK235),k5_xboole_0(sK235,k5_xboole_0(k1_tarski(sK235),k4_xboole_0(sK235,k4_xboole_0(sK235,k1_tarski(sK235)))))) ),
    inference(instantiation,[status(thm)],[c_46765])).

cnf(c_554,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f3296])).

cnf(c_73567,plain,
    ( ~ r1_tarski(k1_tarski(sK235),k5_xboole_0(sK235,k5_xboole_0(k1_tarski(sK235),k4_xboole_0(sK235,k4_xboole_0(sK235,k1_tarski(sK235))))))
    | r2_hidden(sK235,k5_xboole_0(sK235,k5_xboole_0(k1_tarski(sK235),k4_xboole_0(sK235,k4_xboole_0(sK235,k1_tarski(sK235)))))) ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_1703,negated_conjecture,
    ( ~ r2_hidden(sK235,k5_xboole_0(k5_xboole_0(sK235,k1_tarski(sK235)),k4_xboole_0(sK235,k4_xboole_0(sK235,k1_tarski(sK235))))) ),
    inference(cnf_transformation,[],[f5099])).

cnf(c_46509,negated_conjecture,
    ( ~ r2_hidden(sK235,k5_xboole_0(sK235,k5_xboole_0(k1_tarski(sK235),k4_xboole_0(sK235,k4_xboole_0(sK235,k1_tarski(sK235)))))) ),
    inference(theory_normalisation,[status(thm)],[c_1703,c_211,c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_99914,c_92773,c_74977,c_73567,c_46509])).

%------------------------------------------------------------------------------
