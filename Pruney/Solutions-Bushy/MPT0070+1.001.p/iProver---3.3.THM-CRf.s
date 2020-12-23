%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0070+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:24 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   52 (  68 expanded)
%              Number of clauses        :   33 (  35 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :  116 ( 168 expanded)
%              Number of equality atoms :   51 (  58 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).

fof(f18,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_155,plain,
    ( ~ r1_tarski(X0_35,X1_35)
    | r1_tarski(X2_35,X3_35)
    | X2_35 != X0_35
    | X3_35 != X1_35 ),
    theory(equality)).

cnf(c_263,plain,
    ( r1_tarski(X0_35,X1_35)
    | ~ r1_tarski(k3_xboole_0(sK0,X0_36),k3_xboole_0(sK1,X0_36))
    | X1_35 != k3_xboole_0(sK1,X0_36)
    | X0_35 != k3_xboole_0(sK0,X0_36) ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_409,plain,
    ( r1_tarski(k3_xboole_0(sK0,X0_36),X0_35)
    | ~ r1_tarski(k3_xboole_0(sK0,X0_36),k3_xboole_0(sK1,X0_36))
    | X0_35 != k3_xboole_0(sK1,X0_36)
    | k3_xboole_0(sK0,X0_36) != k3_xboole_0(sK0,X0_36) ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_412,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))
    | r1_tarski(k3_xboole_0(sK0,sK2),k1_xboole_0)
    | k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,sK2)
    | k1_xboole_0 != k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_149,plain,
    ( ~ r1_tarski(X0_35,k1_xboole_0)
    | k1_xboole_0 = X0_35 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_350,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k1_xboole_0)
    | k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_153,plain,
    ( X0_35 != X1_35
    | X2_35 != X1_35
    | X2_35 = X0_35 ),
    theory(equality)).

cnf(c_341,plain,
    ( X0_35 != X1_35
    | X0_35 = k3_xboole_0(sK1,X0_36)
    | k3_xboole_0(sK1,X0_36) != X1_35 ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_342,plain,
    ( k3_xboole_0(sK1,sK2) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_152,plain,
    ( X0_35 = X0_35 ),
    theory(equality)).

cnf(c_288,plain,
    ( k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_259,plain,
    ( k3_xboole_0(sK0,sK2) != X0_35
    | k3_xboole_0(sK0,sK2) = k1_xboole_0
    | k1_xboole_0 != X0_35 ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_287,plain,
    ( k3_xboole_0(sK0,sK2) != k3_xboole_0(sK0,sK2)
    | k3_xboole_0(sK0,sK2) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_150,plain,
    ( ~ r1_tarski(X0_35,X1_35)
    | r1_tarski(k3_xboole_0(X0_35,X0_36),k3_xboole_0(X1_35,X0_36)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_247,plain,
    ( r1_tarski(k3_xboole_0(sK0,X0_36),k3_xboole_0(sK1,X0_36))
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_249,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_56,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_5,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_103,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_56,c_5])).

cnf(c_104,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_103])).

cnf(c_146,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_104])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_54,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_4,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_98,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_54,c_4])).

cnf(c_99,plain,
    ( k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_98])).

cnf(c_147,plain,
    ( k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_99])).

cnf(c_159,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_6,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_412,c_350,c_342,c_288,c_287,c_249,c_146,c_147,c_159,c_6])).


%------------------------------------------------------------------------------
