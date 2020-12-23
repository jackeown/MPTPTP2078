%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0044+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:14 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   47 (  68 expanded)
%              Number of clauses        :   22 (  23 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  101 ( 144 expanded)
%              Number of equality atoms :   61 (  90 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f187,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f265,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f187])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f202,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f329,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f265,f202])).

fof(f264,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f187])).

fof(f330,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f264,f202])).

fof(f64,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f293,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f64])).

fof(f334,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f293,f202])).

fof(f75,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f135,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f75])).

fof(f304,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f338,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f304,f202,f202])).

fof(f72,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
      <=> r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f72])).

fof(f134,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <~> r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f73])).

fof(f192,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f134])).

fof(f193,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(X0,X1)
          | k1_xboole_0 != k4_xboole_0(X0,X1) )
        & ( r1_tarski(X0,X1)
          | k1_xboole_0 = k4_xboole_0(X0,X1) ) )
   => ( ( ~ r1_tarski(sK15,sK16)
        | k1_xboole_0 != k4_xboole_0(sK15,sK16) )
      & ( r1_tarski(sK15,sK16)
        | k1_xboole_0 = k4_xboole_0(sK15,sK16) ) ) ),
    introduced(choice_axiom,[])).

fof(f194,plain,
    ( ( ~ r1_tarski(sK15,sK16)
      | k1_xboole_0 != k4_xboole_0(sK15,sK16) )
    & ( r1_tarski(sK15,sK16)
      | k1_xboole_0 = k4_xboole_0(sK15,sK16) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f192,f193])).

fof(f302,plain,
    ( ~ r1_tarski(sK15,sK16)
    | k1_xboole_0 != k4_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f194])).

fof(f335,plain,
    ( ~ r1_tarski(sK15,sK16)
    | o_0_0_xboole_0 != k4_xboole_0(sK15,sK16) ),
    inference(definition_unfolding,[],[f302,f202])).

fof(f301,plain,
    ( r1_tarski(sK15,sK16)
    | k1_xboole_0 = k4_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f194])).

fof(f336,plain,
    ( r1_tarski(sK15,sK16)
    | o_0_0_xboole_0 = k4_xboole_0(sK15,sK16) ),
    inference(definition_unfolding,[],[f301,f202])).

cnf(c_1968,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_8409,plain,
    ( k4_xboole_0(sK15,sK16) = k4_xboole_0(sK15,sK16) ),
    inference(instantiation,[status(thm)],[c_1968])).

cnf(c_1969,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4653,plain,
    ( k4_xboole_0(sK15,sK16) != X0
    | k4_xboole_0(sK15,sK16) = o_0_0_xboole_0
    | o_0_0_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1969])).

cnf(c_8408,plain,
    ( k4_xboole_0(sK15,sK16) != k4_xboole_0(sK15,sK16)
    | k4_xboole_0(sK15,sK16) = o_0_0_xboole_0
    | o_0_0_xboole_0 != k4_xboole_0(sK15,sK16) ),
    inference(instantiation,[status(thm)],[c_4653])).

cnf(c_5351,plain,
    ( k4_xboole_0(sK15,sK16) != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = k4_xboole_0(sK15,sK16) ),
    inference(instantiation,[status(thm)],[c_1969])).

cnf(c_5352,plain,
    ( k4_xboole_0(sK15,sK16) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k4_xboole_0(sK15,sK16)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5351])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f329])).

cnf(c_4650,plain,
    ( ~ r1_tarski(sK15,sK16)
    | k4_xboole_0(sK15,sK16) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_4651,plain,
    ( k4_xboole_0(sK15,sK16) = o_0_0_xboole_0
    | r1_tarski(sK15,sK16) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4650])).

cnf(c_68,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f330])).

cnf(c_4451,plain,
    ( r1_tarski(sK15,sK16)
    | k4_xboole_0(sK15,sK16) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(c_4452,plain,
    ( k4_xboole_0(sK15,sK16) != o_0_0_xboole_0
    | r1_tarski(sK15,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4451])).

cnf(c_96,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f334])).

cnf(c_159,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_107,plain,
    ( ~ r1_tarski(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f338])).

cnf(c_141,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_104,negated_conjecture,
    ( ~ r1_tarski(sK15,sK16)
    | o_0_0_xboole_0 != k4_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f335])).

cnf(c_119,plain,
    ( o_0_0_xboole_0 != k4_xboole_0(sK15,sK16)
    | r1_tarski(sK15,sK16) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_104])).

cnf(c_105,negated_conjecture,
    ( r1_tarski(sK15,sK16)
    | o_0_0_xboole_0 = k4_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f336])).

cnf(c_118,plain,
    ( o_0_0_xboole_0 = k4_xboole_0(sK15,sK16)
    | r1_tarski(sK15,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_105])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8409,c_8408,c_5352,c_4651,c_4452,c_159,c_141,c_119,c_118])).

%------------------------------------------------------------------------------
