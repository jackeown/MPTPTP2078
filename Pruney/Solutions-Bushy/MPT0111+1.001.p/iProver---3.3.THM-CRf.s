%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0111+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:30 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 294 expanded)
%              Number of clauses        :   33 (  91 expanded)
%              Number of leaves         :    5 (  51 expanded)
%              Depth                    :   18
%              Number of atoms          :  189 (1346 expanded)
%              Number of equality atoms :   54 ( 308 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f8])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ~ ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) )
    <=> r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( ~ r2_xboole_0(X1,X0)
            & X0 != X1
            & ~ r2_xboole_0(X0,X1) )
      <=> r3_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    <~> r3_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( ~ r3_xboole_0(X0,X1)
        | ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) ) )
      & ( r3_xboole_0(X0,X1)
        | r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( ~ r3_xboole_0(X0,X1)
        | ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) ) )
      & ( r3_xboole_0(X0,X1)
        | r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ( ~ r3_xboole_0(X0,X1)
          | ( ~ r2_xboole_0(X1,X0)
            & X0 != X1
            & ~ r2_xboole_0(X0,X1) ) )
        & ( r3_xboole_0(X0,X1)
          | r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1) ) )
   => ( ( ~ r3_xboole_0(sK0,sK1)
        | ( ~ r2_xboole_0(sK1,sK0)
          & sK0 != sK1
          & ~ r2_xboole_0(sK0,sK1) ) )
      & ( r3_xboole_0(sK0,sK1)
        | r2_xboole_0(sK1,sK0)
        | sK0 = sK1
        | r2_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ( ~ r3_xboole_0(sK0,sK1)
      | ( ~ r2_xboole_0(sK1,sK0)
        & sK0 != sK1
        & ~ r2_xboole_0(sK0,sK1) ) )
    & ( r3_xboole_0(sK0,sK1)
      | r2_xboole_0(sK1,sK0)
      | sK0 = sK1
      | r2_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f24,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f25,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,
    ( r3_xboole_0(sK0,sK1)
    | r2_xboole_0(sK1,sK0)
    | sK0 = sK1
    | r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] : r3_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(rectify,[],[f3])).

fof(f22,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_4,plain,
    ( r3_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,negated_conjecture,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_95,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_xboole_0(sK0,sK1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_9])).

cnf(c_96,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r2_xboole_0(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_95])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_102,plain,
    ( ~ r2_xboole_0(sK0,sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_96,c_2])).

cnf(c_207,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_102])).

cnf(c_208,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK1 = sK0 ),
    inference(unflattening,[status(thm)],[c_207])).

cnf(c_8,negated_conjecture,
    ( ~ r3_xboole_0(sK0,sK1)
    | sK0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_105,plain,
    ( ~ r1_tarski(X0,X1)
    | sK1 != X1
    | sK1 != sK0
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_106,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK1 != sK0 ),
    inference(unflattening,[status(thm)],[c_105])).

cnf(c_210,plain,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_208,c_106])).

cnf(c_5,plain,
    ( ~ r3_xboole_0(X0,X1)
    | r1_tarski(X0,X1)
    | r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_10,negated_conjecture,
    ( r3_xboole_0(sK0,sK1)
    | r2_xboole_0(sK1,sK0)
    | r2_xboole_0(sK0,sK1)
    | sK0 = sK1 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_147,plain,
    ( r1_tarski(X0,X1)
    | r1_tarski(X1,X0)
    | r2_xboole_0(sK1,sK0)
    | r2_xboole_0(sK0,sK1)
    | sK1 != X1
    | sK1 = sK0
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

cnf(c_148,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1)
    | r2_xboole_0(sK1,sK0)
    | r2_xboole_0(sK0,sK1)
    | sK1 = sK0 ),
    inference(unflattening,[status(thm)],[c_147])).

cnf(c_3,plain,
    ( r3_xboole_0(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_7,negated_conjecture,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_137,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_xboole_0(sK1,sK0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_7])).

cnf(c_138,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ r2_xboole_0(sK1,sK0) ),
    inference(unflattening,[status(thm)],[c_137])).

cnf(c_144,plain,
    ( ~ r2_xboole_0(sK1,sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_138,c_2])).

cnf(c_150,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1)
    | sK1 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_148,c_102,c_144])).

cnf(c_223,plain,
    ( r1_tarski(sK1,sK0)
    | sK1 = sK0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_210,c_150])).

cnf(c_197,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_144])).

cnf(c_198,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_225,plain,
    ( sK1 = sK0 ),
    inference(resolution,[status(thm)],[c_223,c_198])).

cnf(c_6,plain,
    ( r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_166,plain,
    ( sK1 != X0
    | sK1 != sK0
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_8])).

cnf(c_167,plain,
    ( sK1 != sK0
    | sK0 != sK1 ),
    inference(unflattening,[status(thm)],[c_166])).

cnf(c_241,plain,
    ( sK0 != sK1 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_225,c_167])).

cnf(c_248,plain,
    ( sK0 != sK0 ),
    inference(light_normalisation,[status(thm)],[c_241,c_225])).

cnf(c_249,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_248])).


%------------------------------------------------------------------------------
