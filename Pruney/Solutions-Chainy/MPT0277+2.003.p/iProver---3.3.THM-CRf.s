%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:29 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 624 expanded)
%              Number of clauses        :   52 ( 180 expanded)
%              Number of leaves         :   10 ( 153 expanded)
%              Depth                    :   18
%              Number of atoms          :  310 (3011 expanded)
%              Number of equality atoms :  251 (2726 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f38,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f38])).

fof(f52,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f69,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0 )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f70,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0 )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 ) ) ),
    inference(flattening,[],[f69])).

fof(f71,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0 )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 ) )
   => ( ( ( k2_tarski(sK3,sK4) != sK2
          & k1_tarski(sK4) != sK2
          & k1_tarski(sK3) != sK2
          & k1_xboole_0 != sK2 )
        | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 )
      & ( k2_tarski(sK3,sK4) = sK2
        | k1_tarski(sK4) = sK2
        | k1_tarski(sK3) = sK2
        | k1_xboole_0 = sK2
        | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,
    ( ( ( k2_tarski(sK3,sK4) != sK2
        & k1_tarski(sK4) != sK2
        & k1_tarski(sK3) != sK2
        & k1_xboole_0 != sK2 )
      | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 )
    & ( k2_tarski(sK3,sK4) = sK2
      | k1_tarski(sK4) = sK2
      | k1_tarski(sK3) = sK2
      | k1_xboole_0 = sK2
      | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f70,f71])).

fof(f126,plain,
    ( k2_tarski(sK3,sK4) = sK2
    | k1_tarski(sK4) = sK2
    | k1_tarski(sK3) = sK2
    | k1_xboole_0 = sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

fof(f27,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f106,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f167,plain,
    ( k2_tarski(sK3,sK4) = sK2
    | k2_tarski(sK4,sK4) = sK2
    | k2_tarski(sK3,sK3) = sK2
    | k1_xboole_0 = sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f126,f106,f106])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f63])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f110,f106,f106])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f161,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f123,f106])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f80,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f129,plain,
    ( k1_tarski(sK4) != sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

fof(f165,plain,
    ( k2_tarski(sK4,sK4) != sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f129,f106])).

fof(f127,plain,
    ( k1_xboole_0 != sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

fof(f128,plain,
    ( k1_tarski(sK3) != sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

fof(f166,plain,
    ( k2_tarski(sK3,sK3) != sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f128,f106])).

fof(f130,plain,
    ( k2_tarski(sK3,sK4) != sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f113,f106])).

fof(f173,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f151])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f112,f106])).

fof(f174,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f152])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f175,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f111])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f172,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f114])).

cnf(c_629,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_54,negated_conjecture,
    ( k2_tarski(sK4,sK4) = sK2
    | k2_tarski(sK3,sK4) = sK2
    | k2_tarski(sK3,sK3) = sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f167])).

cnf(c_2101,plain,
    ( r1_tarski(sK2,k2_tarski(sK3,sK4))
    | k2_tarski(sK4,sK4) = sK2
    | k2_tarski(sK3,sK4) = sK2
    | k2_tarski(sK3,sK3) = sK2
    | k1_xboole_0 = sK2 ),
    inference(resolution,[status(thm)],[c_10,c_54])).

cnf(c_38,plain,
    ( ~ r1_tarski(X0,k2_tarski(X1,X2))
    | k2_tarski(X1,X2) = X0
    | k2_tarski(X2,X2) = X0
    | k2_tarski(X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f153])).

cnf(c_2243,plain,
    ( k2_tarski(sK4,sK4) = sK2
    | k2_tarski(sK3,sK4) = sK2
    | k2_tarski(sK3,sK3) = sK2
    | k1_xboole_0 = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2101,c_38])).

cnf(c_4459,plain,
    ( X0 != sK2
    | k2_tarski(sK4,sK4) = X0
    | k2_tarski(sK3,sK4) = sK2
    | k2_tarski(sK3,sK3) = sK2
    | k1_xboole_0 = sK2 ),
    inference(resolution,[status(thm)],[c_629,c_2243])).

cnf(c_4974,plain,
    ( X0 != X1
    | X1 != sK2
    | k2_tarski(sK4,sK4) = X0
    | k2_tarski(sK3,sK4) = sK2
    | k2_tarski(sK3,sK3) = sK2
    | k1_xboole_0 = sK2 ),
    inference(resolution,[status(thm)],[c_4459,c_629])).

cnf(c_46,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_tarski(X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f161])).

cnf(c_5123,plain,
    ( r2_hidden(X0,sK2)
    | X1 != k4_xboole_0(sK2,k2_tarski(X0,X0))
    | k2_tarski(sK4,sK4) = X1
    | k2_tarski(sK3,sK4) = sK2
    | k2_tarski(sK3,sK3) = sK2
    | k1_xboole_0 = sK2 ),
    inference(resolution,[status(thm)],[c_4974,c_46])).

cnf(c_6127,plain,
    ( r2_hidden(X0,sK2)
    | k2_tarski(sK4,sK4) = k2_tarski(sK4,sK4)
    | k2_tarski(sK3,sK4) = sK2
    | k2_tarski(sK3,sK3) = sK2
    | k4_xboole_0(sK2,k2_tarski(X0,X0)) != sK2
    | k1_xboole_0 = sK2 ),
    inference(resolution,[status(thm)],[c_5123,c_4459])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1597,plain,
    ( ~ r1_tarski(sK2,k2_tarski(sK3,sK4))
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1915,plain,
    ( k4_xboole_0(sK2,X0) != k4_xboole_0(X0,sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2225,plain,
    ( k4_xboole_0(sK2,sK2) != k4_xboole_0(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1915])).

cnf(c_628,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2226,plain,
    ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_628])).

cnf(c_51,negated_conjecture,
    ( k2_tarski(sK4,sK4) != sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f165])).

cnf(c_53,negated_conjecture,
    ( k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_52,negated_conjecture,
    ( k2_tarski(sK3,sK3) != sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f166])).

cnf(c_50,negated_conjecture,
    ( k2_tarski(sK3,sK4) != sK2
    | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_2313,negated_conjecture,
    ( k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_51,c_53,c_52,c_50,c_2243])).

cnf(c_635,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1852,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k2_tarski(sK3,sK4))
    | k2_tarski(sK3,sK4) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_635])).

cnf(c_2993,plain,
    ( ~ r1_tarski(X0,k2_tarski(sK3,sK4))
    | r1_tarski(sK2,k2_tarski(sK3,sK4))
    | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1852])).

cnf(c_2996,plain,
    ( r1_tarski(sK2,k2_tarski(sK3,sK4))
    | ~ r1_tarski(k1_xboole_0,k2_tarski(sK3,sK4))
    | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2993])).

cnf(c_2994,plain,
    ( k2_tarski(sK3,sK4) = k2_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_628])).

cnf(c_2664,plain,
    ( X0 != X1
    | X0 = k2_tarski(X2,X2)
    | k2_tarski(X2,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_4255,plain,
    ( X0 = k2_tarski(sK4,sK4)
    | X0 != sK2
    | k2_tarski(sK4,sK4) != sK2 ),
    inference(instantiation,[status(thm)],[c_2664])).

cnf(c_4876,plain,
    ( k2_tarski(sK4,sK4) != sK2
    | sK2 = k2_tarski(sK4,sK4)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4255])).

cnf(c_4257,plain,
    ( X0 = k2_tarski(sK3,sK3)
    | X0 != sK2
    | k2_tarski(sK3,sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_2664])).

cnf(c_5382,plain,
    ( k2_tarski(sK3,sK3) != sK2
    | sK2 = k2_tarski(sK3,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4257])).

cnf(c_1922,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_5649,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1922])).

cnf(c_5650,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_5649])).

cnf(c_6401,plain,
    ( ~ r1_tarski(k2_tarski(sK4,sK4),k2_tarski(sK3,sK4))
    | r1_tarski(sK2,k2_tarski(sK3,sK4))
    | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4)
    | sK2 != k2_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2993])).

cnf(c_35,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f173])).

cnf(c_6402,plain,
    ( r1_tarski(k2_tarski(sK4,sK4),k2_tarski(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_6407,plain,
    ( ~ r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK4))
    | r1_tarski(sK2,k2_tarski(sK3,sK4))
    | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4)
    | sK2 != k2_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2993])).

cnf(c_36,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f174])).

cnf(c_6408,plain,
    ( r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_37,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f175])).

cnf(c_6414,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_6621,plain,
    ( k2_tarski(sK3,sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6127,c_53,c_52,c_51,c_50,c_1597,c_2225,c_2226,c_2243,c_2996,c_2994,c_4876,c_5382,c_5650,c_6401,c_6402,c_6407,c_6408,c_6414])).

cnf(c_6630,plain,
    ( X0 != sK2
    | k2_tarski(sK3,sK4) = X0 ),
    inference(resolution,[status(thm)],[c_6621,c_629])).

cnf(c_3008,plain,
    ( k2_tarski(sK3,sK4) != X0
    | sK2 != X0
    | sK2 = k2_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1922])).

cnf(c_6395,plain,
    ( ~ r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK3,sK4))
    | r1_tarski(sK2,k2_tarski(sK3,sK4))
    | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4)
    | sK2 != k2_tarski(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2993])).

cnf(c_34,plain,
    ( r1_tarski(k2_tarski(X0,X1),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f172])).

cnf(c_6396,plain,
    ( r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_6822,plain,
    ( X0 != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6630,c_53,c_52,c_51,c_50,c_1597,c_2225,c_2226,c_2243,c_2994,c_3008,c_5649,c_6395,c_6396])).

cnf(c_7064,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_6822,c_6621])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:49:15 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  % Running in FOF mode
% 3.88/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/0.98  
% 3.88/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.88/0.98  
% 3.88/0.98  ------  iProver source info
% 3.88/0.98  
% 3.88/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.88/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.88/0.98  git: non_committed_changes: false
% 3.88/0.98  git: last_make_outside_of_git: false
% 3.88/0.98  
% 3.88/0.98  ------ 
% 3.88/0.98  ------ Parsing...
% 3.88/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.88/0.98  
% 3.88/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.88/0.98  
% 3.88/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.88/0.98  
% 3.88/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.98  ------ Proving...
% 3.88/0.98  ------ Problem Properties 
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  clauses                                 55
% 3.88/0.98  conjectures                             5
% 3.88/0.98  EPR                                     3
% 3.88/0.98  Horn                                    47
% 3.88/0.98  unary                                   23
% 3.88/0.98  binary                                  25
% 3.88/0.98  lits                                    100
% 3.88/0.98  lits eq                                 64
% 3.88/0.98  fd_pure                                 0
% 3.88/0.98  fd_pseudo                               0
% 3.88/0.98  fd_cond                                 4
% 3.88/0.98  fd_pseudo_cond                          6
% 3.88/0.98  AC symbols                              0
% 3.88/0.98  
% 3.88/0.98  ------ Input Options Time Limit: Unbounded
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  ------ 
% 3.88/0.98  Current options:
% 3.88/0.98  ------ 
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  ------ Proving...
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  % SZS status Theorem for theBenchmark.p
% 3.88/0.98  
% 3.88/0.98   Resolution empty clause
% 3.88/0.98  
% 3.88/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.88/0.98  
% 3.88/0.98  fof(f8,axiom,(
% 3.88/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f56,plain,(
% 3.88/0.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.88/0.98    inference(nnf_transformation,[],[f8])).
% 3.88/0.98  
% 3.88/0.98  fof(f81,plain,(
% 3.88/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.88/0.98    inference(cnf_transformation,[],[f56])).
% 3.88/0.98  
% 3.88/0.98  fof(f38,conjecture,(
% 3.88/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f39,negated_conjecture,(
% 3.88/0.98    ~! [X0,X1,X2] : (k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.88/0.98    inference(negated_conjecture,[],[f38])).
% 3.88/0.98  
% 3.88/0.98  fof(f52,plain,(
% 3.88/0.98    ? [X0,X1,X2] : (k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.88/0.98    inference(ennf_transformation,[],[f39])).
% 3.88/0.98  
% 3.88/0.98  fof(f69,plain,(
% 3.88/0.98    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0))),
% 3.88/0.98    inference(nnf_transformation,[],[f52])).
% 3.88/0.98  
% 3.88/0.98  fof(f70,plain,(
% 3.88/0.98    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0))),
% 3.88/0.98    inference(flattening,[],[f69])).
% 3.88/0.98  
% 3.88/0.98  fof(f71,plain,(
% 3.88/0.98    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0)) => (((k2_tarski(sK3,sK4) != sK2 & k1_tarski(sK4) != sK2 & k1_tarski(sK3) != sK2 & k1_xboole_0 != sK2) | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0) & (k2_tarski(sK3,sK4) = sK2 | k1_tarski(sK4) = sK2 | k1_tarski(sK3) = sK2 | k1_xboole_0 = sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0))),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f72,plain,(
% 3.88/0.98    ((k2_tarski(sK3,sK4) != sK2 & k1_tarski(sK4) != sK2 & k1_tarski(sK3) != sK2 & k1_xboole_0 != sK2) | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0) & (k2_tarski(sK3,sK4) = sK2 | k1_tarski(sK4) = sK2 | k1_tarski(sK3) = sK2 | k1_xboole_0 = sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0)),
% 3.88/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f70,f71])).
% 3.88/0.98  
% 3.88/0.98  fof(f126,plain,(
% 3.88/0.98    k2_tarski(sK3,sK4) = sK2 | k1_tarski(sK4) = sK2 | k1_tarski(sK3) = sK2 | k1_xboole_0 = sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0),
% 3.88/0.98    inference(cnf_transformation,[],[f72])).
% 3.88/0.98  
% 3.88/0.98  fof(f27,axiom,(
% 3.88/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f106,plain,(
% 3.88/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f27])).
% 3.88/0.98  
% 3.88/0.98  fof(f167,plain,(
% 3.88/0.98    k2_tarski(sK3,sK4) = sK2 | k2_tarski(sK4,sK4) = sK2 | k2_tarski(sK3,sK3) = sK2 | k1_xboole_0 = sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0),
% 3.88/0.98    inference(definition_unfolding,[],[f126,f106,f106])).
% 3.88/0.98  
% 3.88/0.98  fof(f30,axiom,(
% 3.88/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f49,plain,(
% 3.88/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.88/0.98    inference(ennf_transformation,[],[f30])).
% 3.88/0.98  
% 3.88/0.98  fof(f63,plain,(
% 3.88/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.88/0.98    inference(nnf_transformation,[],[f49])).
% 3.88/0.98  
% 3.88/0.98  fof(f64,plain,(
% 3.88/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.88/0.98    inference(flattening,[],[f63])).
% 3.88/0.98  
% 3.88/0.98  fof(f110,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.88/0.98    inference(cnf_transformation,[],[f64])).
% 3.88/0.98  
% 3.88/0.98  fof(f153,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k2_tarski(X2,X2) = X0 | k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.88/0.98    inference(definition_unfolding,[],[f110,f106,f106])).
% 3.88/0.98  
% 3.88/0.98  fof(f36,axiom,(
% 3.88/0.98    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f67,plain,(
% 3.88/0.98    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.88/0.98    inference(nnf_transformation,[],[f36])).
% 3.88/0.98  
% 3.88/0.98  fof(f123,plain,(
% 3.88/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f67])).
% 3.88/0.98  
% 3.88/0.98  fof(f161,plain,(
% 3.88/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k2_tarski(X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.88/0.98    inference(definition_unfolding,[],[f123,f106])).
% 3.88/0.98  
% 3.88/0.98  fof(f82,plain,(
% 3.88/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f56])).
% 3.88/0.98  
% 3.88/0.98  fof(f7,axiom,(
% 3.88/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 3.88/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f42,plain,(
% 3.88/0.98    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 3.88/0.98    inference(ennf_transformation,[],[f7])).
% 3.88/0.98  
% 3.88/0.98  fof(f80,plain,(
% 3.88/0.98    ( ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f42])).
% 3.88/0.98  
% 3.88/0.98  fof(f129,plain,(
% 3.88/0.98    k1_tarski(sK4) != sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0),
% 3.88/0.98    inference(cnf_transformation,[],[f72])).
% 3.88/0.98  
% 3.88/0.98  fof(f165,plain,(
% 3.88/0.98    k2_tarski(sK4,sK4) != sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0),
% 3.88/0.98    inference(definition_unfolding,[],[f129,f106])).
% 3.88/0.98  
% 3.88/0.98  fof(f127,plain,(
% 3.88/0.98    k1_xboole_0 != sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0),
% 3.88/0.98    inference(cnf_transformation,[],[f72])).
% 3.88/0.98  
% 3.88/0.98  fof(f128,plain,(
% 3.88/0.98    k1_tarski(sK3) != sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0),
% 3.88/0.98    inference(cnf_transformation,[],[f72])).
% 3.88/0.98  
% 3.88/0.98  fof(f166,plain,(
% 3.88/0.98    k2_tarski(sK3,sK3) != sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0),
% 3.88/0.98    inference(definition_unfolding,[],[f128,f106])).
% 3.88/0.98  
% 3.88/0.98  fof(f130,plain,(
% 3.88/0.98    k2_tarski(sK3,sK4) != sK2 | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0),
% 3.88/0.98    inference(cnf_transformation,[],[f72])).
% 3.88/0.98  
% 3.88/0.98  fof(f113,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 3.88/0.98    inference(cnf_transformation,[],[f64])).
% 3.88/0.98  
% 3.88/0.98  fof(f151,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X2,X2) != X0) )),
% 3.88/0.98    inference(definition_unfolding,[],[f113,f106])).
% 3.88/0.98  
% 3.88/0.98  fof(f173,plain,(
% 3.88/0.98    ( ! [X2,X1] : (r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2))) )),
% 3.88/0.98    inference(equality_resolution,[],[f151])).
% 3.88/0.98  
% 3.88/0.98  fof(f112,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 3.88/0.98    inference(cnf_transformation,[],[f64])).
% 3.88/0.98  
% 3.88/0.98  fof(f152,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X1) != X0) )),
% 3.88/0.98    inference(definition_unfolding,[],[f112,f106])).
% 3.88/0.98  
% 3.88/0.98  fof(f174,plain,(
% 3.88/0.98    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2))) )),
% 3.88/0.98    inference(equality_resolution,[],[f152])).
% 3.88/0.98  
% 3.88/0.98  fof(f111,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 3.88/0.98    inference(cnf_transformation,[],[f64])).
% 3.88/0.98  
% 3.88/0.98  fof(f175,plain,(
% 3.88/0.98    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X2))) )),
% 3.88/0.98    inference(equality_resolution,[],[f111])).
% 3.88/0.98  
% 3.88/0.98  fof(f114,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X2) != X0) )),
% 3.88/0.98    inference(cnf_transformation,[],[f64])).
% 3.88/0.98  
% 3.88/0.98  fof(f172,plain,(
% 3.88/0.98    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2))) )),
% 3.88/0.98    inference(equality_resolution,[],[f114])).
% 3.88/0.98  
% 3.88/0.98  cnf(c_629,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_10,plain,
% 3.88/0.98      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.88/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_54,negated_conjecture,
% 3.88/0.98      ( k2_tarski(sK4,sK4) = sK2
% 3.88/0.98      | k2_tarski(sK3,sK4) = sK2
% 3.88/0.98      | k2_tarski(sK3,sK3) = sK2
% 3.88/0.98      | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0
% 3.88/0.98      | k1_xboole_0 = sK2 ),
% 3.88/0.98      inference(cnf_transformation,[],[f167]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2101,plain,
% 3.88/0.98      ( r1_tarski(sK2,k2_tarski(sK3,sK4))
% 3.88/0.98      | k2_tarski(sK4,sK4) = sK2
% 3.88/0.98      | k2_tarski(sK3,sK4) = sK2
% 3.88/0.98      | k2_tarski(sK3,sK3) = sK2
% 3.88/0.98      | k1_xboole_0 = sK2 ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_10,c_54]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_38,plain,
% 3.88/0.98      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
% 3.88/0.98      | k2_tarski(X1,X2) = X0
% 3.88/0.98      | k2_tarski(X2,X2) = X0
% 3.88/0.98      | k2_tarski(X1,X1) = X0
% 3.88/0.98      | k1_xboole_0 = X0 ),
% 3.88/0.98      inference(cnf_transformation,[],[f153]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2243,plain,
% 3.88/0.98      ( k2_tarski(sK4,sK4) = sK2
% 3.88/0.98      | k2_tarski(sK3,sK4) = sK2
% 3.88/0.98      | k2_tarski(sK3,sK3) = sK2
% 3.88/0.98      | k1_xboole_0 = sK2 ),
% 3.88/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_2101,c_38]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4459,plain,
% 3.88/0.98      ( X0 != sK2
% 3.88/0.98      | k2_tarski(sK4,sK4) = X0
% 3.88/0.98      | k2_tarski(sK3,sK4) = sK2
% 3.88/0.98      | k2_tarski(sK3,sK3) = sK2
% 3.88/0.98      | k1_xboole_0 = sK2 ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_629,c_2243]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4974,plain,
% 3.88/0.98      ( X0 != X1
% 3.88/0.98      | X1 != sK2
% 3.88/0.98      | k2_tarski(sK4,sK4) = X0
% 3.88/0.98      | k2_tarski(sK3,sK4) = sK2
% 3.88/0.98      | k2_tarski(sK3,sK3) = sK2
% 3.88/0.98      | k1_xboole_0 = sK2 ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_4459,c_629]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_46,plain,
% 3.88/0.98      ( r2_hidden(X0,X1) | k4_xboole_0(X1,k2_tarski(X0,X0)) = X1 ),
% 3.88/0.98      inference(cnf_transformation,[],[f161]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_5123,plain,
% 3.88/0.98      ( r2_hidden(X0,sK2)
% 3.88/0.98      | X1 != k4_xboole_0(sK2,k2_tarski(X0,X0))
% 3.88/0.98      | k2_tarski(sK4,sK4) = X1
% 3.88/0.98      | k2_tarski(sK3,sK4) = sK2
% 3.88/0.98      | k2_tarski(sK3,sK3) = sK2
% 3.88/0.98      | k1_xboole_0 = sK2 ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_4974,c_46]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6127,plain,
% 3.88/0.98      ( r2_hidden(X0,sK2)
% 3.88/0.98      | k2_tarski(sK4,sK4) = k2_tarski(sK4,sK4)
% 3.88/0.98      | k2_tarski(sK3,sK4) = sK2
% 3.88/0.98      | k2_tarski(sK3,sK3) = sK2
% 3.88/0.98      | k4_xboole_0(sK2,k2_tarski(X0,X0)) != sK2
% 3.88/0.98      | k1_xboole_0 = sK2 ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_5123,c_4459]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_9,plain,
% 3.88/0.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.88/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1597,plain,
% 3.88/0.98      ( ~ r1_tarski(sK2,k2_tarski(sK3,sK4))
% 3.88/0.98      | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) = k1_xboole_0 ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_8,plain,
% 3.88/0.98      ( X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
% 3.88/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1915,plain,
% 3.88/0.98      ( k4_xboole_0(sK2,X0) != k4_xboole_0(X0,sK2) | sK2 = X0 ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2225,plain,
% 3.88/0.98      ( k4_xboole_0(sK2,sK2) != k4_xboole_0(sK2,sK2) | sK2 = sK2 ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_1915]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_628,plain,( X0 = X0 ),theory(equality) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2226,plain,
% 3.88/0.98      ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK2) ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_628]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_51,negated_conjecture,
% 3.88/0.98      ( k2_tarski(sK4,sK4) != sK2
% 3.88/0.98      | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
% 3.88/0.98      inference(cnf_transformation,[],[f165]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_53,negated_conjecture,
% 3.88/0.98      ( k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0
% 3.88/0.98      | k1_xboole_0 != sK2 ),
% 3.88/0.98      inference(cnf_transformation,[],[f127]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_52,negated_conjecture,
% 3.88/0.98      ( k2_tarski(sK3,sK3) != sK2
% 3.88/0.98      | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
% 3.88/0.98      inference(cnf_transformation,[],[f166]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_50,negated_conjecture,
% 3.88/0.98      ( k2_tarski(sK3,sK4) != sK2
% 3.88/0.98      | k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
% 3.88/0.98      inference(cnf_transformation,[],[f130]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2313,negated_conjecture,
% 3.88/0.98      ( k4_xboole_0(sK2,k2_tarski(sK3,sK4)) != k1_xboole_0 ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_51,c_53,c_52,c_50,c_2243]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_635,plain,
% 3.88/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.88/0.98      theory(equality) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1852,plain,
% 3.88/0.98      ( ~ r1_tarski(X0,X1)
% 3.88/0.98      | r1_tarski(sK2,k2_tarski(sK3,sK4))
% 3.88/0.98      | k2_tarski(sK3,sK4) != X1
% 3.88/0.98      | sK2 != X0 ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_635]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2993,plain,
% 3.88/0.98      ( ~ r1_tarski(X0,k2_tarski(sK3,sK4))
% 3.88/0.98      | r1_tarski(sK2,k2_tarski(sK3,sK4))
% 3.88/0.98      | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4)
% 3.88/0.98      | sK2 != X0 ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_1852]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2996,plain,
% 3.88/0.98      ( r1_tarski(sK2,k2_tarski(sK3,sK4))
% 3.88/0.98      | ~ r1_tarski(k1_xboole_0,k2_tarski(sK3,sK4))
% 3.88/0.98      | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4)
% 3.88/0.98      | sK2 != k1_xboole_0 ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_2993]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2994,plain,
% 3.88/0.98      ( k2_tarski(sK3,sK4) = k2_tarski(sK3,sK4) ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_628]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2664,plain,
% 3.88/0.98      ( X0 != X1 | X0 = k2_tarski(X2,X2) | k2_tarski(X2,X2) != X1 ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_629]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4255,plain,
% 3.88/0.98      ( X0 = k2_tarski(sK4,sK4) | X0 != sK2 | k2_tarski(sK4,sK4) != sK2 ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_2664]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4876,plain,
% 3.88/0.98      ( k2_tarski(sK4,sK4) != sK2 | sK2 = k2_tarski(sK4,sK4) | sK2 != sK2 ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_4255]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4257,plain,
% 3.88/0.98      ( X0 = k2_tarski(sK3,sK3) | X0 != sK2 | k2_tarski(sK3,sK3) != sK2 ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_2664]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_5382,plain,
% 3.88/0.98      ( k2_tarski(sK3,sK3) != sK2 | sK2 = k2_tarski(sK3,sK3) | sK2 != sK2 ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_4257]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_1922,plain,
% 3.88/0.98      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_629]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_5649,plain,
% 3.88/0.98      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_1922]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_5650,plain,
% 3.88/0.98      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_5649]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6401,plain,
% 3.88/0.98      ( ~ r1_tarski(k2_tarski(sK4,sK4),k2_tarski(sK3,sK4))
% 3.88/0.98      | r1_tarski(sK2,k2_tarski(sK3,sK4))
% 3.88/0.98      | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4)
% 3.88/0.98      | sK2 != k2_tarski(sK4,sK4) ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_2993]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_35,plain,
% 3.88/0.98      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X1,X0)) ),
% 3.88/0.98      inference(cnf_transformation,[],[f173]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6402,plain,
% 3.88/0.98      ( r1_tarski(k2_tarski(sK4,sK4),k2_tarski(sK3,sK4)) ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_35]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6407,plain,
% 3.88/0.98      ( ~ r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK4))
% 3.88/0.98      | r1_tarski(sK2,k2_tarski(sK3,sK4))
% 3.88/0.98      | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4)
% 3.88/0.98      | sK2 != k2_tarski(sK3,sK3) ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_2993]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_36,plain,
% 3.88/0.98      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
% 3.88/0.98      inference(cnf_transformation,[],[f174]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6408,plain,
% 3.88/0.98      ( r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK4)) ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_36]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_37,plain,
% 3.88/0.98      ( r1_tarski(k1_xboole_0,k2_tarski(X0,X1)) ),
% 3.88/0.98      inference(cnf_transformation,[],[f175]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6414,plain,
% 3.88/0.98      ( r1_tarski(k1_xboole_0,k2_tarski(sK3,sK4)) ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_37]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6621,plain,
% 3.88/0.98      ( k2_tarski(sK3,sK4) = sK2 ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_6127,c_53,c_52,c_51,c_50,c_1597,c_2225,c_2226,c_2243,
% 3.88/0.98                 c_2996,c_2994,c_4876,c_5382,c_5650,c_6401,c_6402,c_6407,
% 3.88/0.98                 c_6408,c_6414]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6630,plain,
% 3.88/0.98      ( X0 != sK2 | k2_tarski(sK3,sK4) = X0 ),
% 3.88/0.98      inference(resolution,[status(thm)],[c_6621,c_629]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3008,plain,
% 3.88/0.98      ( k2_tarski(sK3,sK4) != X0 | sK2 != X0 | sK2 = k2_tarski(sK3,sK4) ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_1922]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6395,plain,
% 3.88/0.98      ( ~ r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK3,sK4))
% 3.88/0.98      | r1_tarski(sK2,k2_tarski(sK3,sK4))
% 3.88/0.98      | k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4)
% 3.88/0.98      | sK2 != k2_tarski(sK3,sK4) ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_2993]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_34,plain,
% 3.88/0.98      ( r1_tarski(k2_tarski(X0,X1),k2_tarski(X0,X1)) ),
% 3.88/0.98      inference(cnf_transformation,[],[f172]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6396,plain,
% 3.88/0.98      ( r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK3,sK4)) ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_34]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6822,plain,
% 3.88/0.98      ( X0 != sK2 ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_6630,c_53,c_52,c_51,c_50,c_1597,c_2225,c_2226,c_2243,
% 3.88/0.98                 c_2994,c_3008,c_5649,c_6395,c_6396]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7064,plain,
% 3.88/0.98      ( $false ),
% 3.88/0.98      inference(backward_subsumption_resolution,[status(thm)],[c_6822,c_6621]) ).
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.88/0.98  
% 3.88/0.98  ------                               Statistics
% 3.88/0.98  
% 3.88/0.98  ------ Selected
% 3.88/0.98  
% 3.88/0.98  total_time:                             0.336
% 3.88/0.98  
%------------------------------------------------------------------------------
