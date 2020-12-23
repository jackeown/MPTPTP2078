%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0244+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:48 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 117 expanded)
%              Number of clauses        :   27 (  41 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :   15
%              Number of atoms          :  141 ( 467 expanded)
%              Number of equality atoms :  105 ( 327 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f5])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f4,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k1_tarski(X1)) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k1_tarski(X1)) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f7])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ( ( k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | ~ r1_tarski(X0,k1_tarski(X1)) )
        & ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | r1_tarski(X0,k1_tarski(X1)) ) )
   => ( ( ( k1_tarski(sK1) != sK0
          & k1_xboole_0 != sK0 )
        | ~ r1_tarski(sK0,k1_tarski(sK1)) )
      & ( k1_tarski(sK1) = sK0
        | k1_xboole_0 = sK0
        | r1_tarski(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ( ( k1_tarski(sK1) != sK0
        & k1_xboole_0 != sK0 )
      | ~ r1_tarski(sK0,k1_tarski(sK1)) )
    & ( k1_tarski(sK1) = sK0
      | k1_xboole_0 = sK0
      | r1_tarski(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).

fof(f14,plain,
    ( k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f12])).

fof(f15,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f13])).

fof(f16,plain,
    ( k1_tarski(sK1) != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_142,plain,
    ( X0_33 != X1_33
    | X2_33 != X1_33
    | X2_33 = X0_33 ),
    theory(equality)).

cnf(c_197,plain,
    ( sK0 != X0_33
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0_33 ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_198,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_141,plain,
    ( X0_33 = X0_33 ),
    theory(equality)).

cnf(c_194,plain,
    ( k1_tarski(sK1) = k1_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_141])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_5,negated_conjecture,
    ( r1_tarski(sK0,k1_tarski(sK1))
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_106,plain,
    ( k1_tarski(X0) = X1
    | k1_tarski(X0) != k1_tarski(sK1)
    | k1_tarski(sK1) = sK0
    | sK0 != X1
    | sK0 = k1_xboole_0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_5])).

cnf(c_107,plain,
    ( k1_tarski(X0) != k1_tarski(sK1)
    | k1_tarski(X0) = sK0
    | k1_tarski(sK1) = sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_106])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_4,negated_conjecture,
    ( ~ r1_tarski(sK0,k1_tarski(sK1))
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_95,plain,
    ( k1_tarski(X0) != k1_tarski(sK1)
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_4])).

cnf(c_109,plain,
    ( k1_tarski(sK1) = sK0
    | k1_tarski(X0) = sK0
    | k1_tarski(X0) != k1_tarski(sK1)
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_107,c_95])).

cnf(c_110,plain,
    ( k1_tarski(X0) != k1_tarski(sK1)
    | k1_tarski(X0) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(renaming,[status(thm)],[c_109])).

cnf(c_136,plain,
    ( k1_tarski(X0_34) != k1_tarski(sK1)
    | k1_tarski(X0_34) = sK0
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_110])).

cnf(c_139,plain,
    ( k1_tarski(X0_34) != k1_tarski(sK1)
    | k1_tarski(X0_34) = sK0
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_136])).

cnf(c_148,plain,
    ( ~ sP0_iProver_split
    | k1_tarski(sK1) != k1_tarski(sK1)
    | k1_tarski(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_139])).

cnf(c_140,plain,
    ( sP0_iProver_split
    | k1_tarski(sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_136])).

cnf(c_137,plain,
    ( k1_tarski(X0_34) != k1_tarski(sK1)
    | sK0 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_95])).

cnf(c_145,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_137])).

cnf(c_0,plain,
    ( r1_tarski(k1_tarski(X0),k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_3,negated_conjecture,
    ( ~ r1_tarski(sK0,k1_tarski(sK1))
    | k1_tarski(sK1) != sK0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_82,plain,
    ( k1_tarski(X0) != k1_tarski(sK1)
    | k1_tarski(X0) != sK0
    | k1_tarski(sK1) != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_138,plain,
    ( k1_tarski(X0_34) != k1_tarski(sK1)
    | k1_tarski(X0_34) != sK0
    | k1_tarski(sK1) != sK0 ),
    inference(subtyping,[status(esa)],[c_82])).

cnf(c_144,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | k1_tarski(sK1) != sK0 ),
    inference(instantiation,[status(thm)],[c_138])).

cnf(c_143,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_141])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_198,c_194,c_148,c_140,c_145,c_144,c_143])).


%------------------------------------------------------------------------------
