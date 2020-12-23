%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0473+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:23 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   40 (  69 expanded)
%              Number of clauses        :   22 (  25 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :  106 ( 228 expanded)
%              Number of equality atoms :   88 ( 181 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f6,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k1_relat_1(X0)
        <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <~> k1_xboole_0 = k2_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0) )
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f9,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0) )
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f10,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k2_relat_1(sK0)
        | k1_xboole_0 != k1_relat_1(sK0) )
      & ( k1_xboole_0 = k2_relat_1(sK0)
        | k1_xboole_0 = k1_relat_1(sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ( k1_xboole_0 != k2_relat_1(sK0)
      | k1_xboole_0 != k1_relat_1(sK0) )
    & ( k1_xboole_0 = k2_relat_1(sK0)
      | k1_xboole_0 = k1_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f17,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 != k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_6,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_58,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | sK0 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_59,plain,
    ( k1_relat_1(sK0) != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_58])).

cnf(c_5,negated_conjecture,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_66,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | sK0 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_6])).

cnf(c_67,plain,
    ( k2_relat_1(sK0) != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_66])).

cnf(c_98,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_147,plain,
    ( k1_relat_1(sK0) != X0
    | k1_relat_1(sK0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_159,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | k1_relat_1(sK0) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_97,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_160,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_148,plain,
    ( k2_relat_1(sK0) != X0
    | k2_relat_1(sK0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_166,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | k2_relat_1(sK0) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_167,plain,
    ( k2_relat_1(sK0) = k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_180,plain,
    ( k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_59,c_5,c_67,c_159,c_160,c_166,c_167])).

cnf(c_4,negated_conjecture,
    ( k1_xboole_0 != k1_relat_1(sK0)
    | k1_xboole_0 != k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_184,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_180,c_4])).

cnf(c_0,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_1,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_184,c_0,c_1])).


%------------------------------------------------------------------------------
