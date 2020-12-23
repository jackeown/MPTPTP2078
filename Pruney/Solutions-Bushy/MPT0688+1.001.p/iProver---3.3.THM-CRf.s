%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0688+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:54 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   37 (  62 expanded)
%              Number of clauses        :   17 (  18 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :   11
%              Number of atoms          :   99 ( 201 expanded)
%              Number of equality atoms :   30 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f10])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ~ ( k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( ! [X2] :
              ~ ( k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0
                & r2_hidden(X2,X0) )
         => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k10_relat_1(X1,k1_tarski(X2)) != k1_xboole_0
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( k10_relat_1(X1,k1_tarski(X2)) != k1_xboole_0
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k2_relat_1(X1))
        & ! [X2] :
            ( k10_relat_1(X1,k1_tarski(X2)) != k1_xboole_0
            | ~ r2_hidden(X2,X0) )
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK1,k2_relat_1(sK2))
      & ! [X2] :
          ( k10_relat_1(sK2,k1_tarski(X2)) != k1_xboole_0
          | ~ r2_hidden(X2,sK1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    & ! [X2] :
        ( k10_relat_1(sK2,k1_tarski(X2)) != k1_xboole_0
        | ~ r2_hidden(X2,sK1) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f9,f13])).

fof(f21,plain,(
    ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 )
        & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_relat_1(X1))
      | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X2] :
      ( k10_relat_1(sK2,k1_tarski(X2)) != k1_xboole_0
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_4,negated_conjecture,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_91,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k2_relat_1(sK2) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_92,plain,
    ( ~ r2_hidden(sK0(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_91])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_6,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_114,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_6])).

cnf(c_115,plain,
    ( r2_hidden(X0,k2_relat_1(sK2))
    | k10_relat_1(sK2,k1_tarski(X0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_114])).

cnf(c_149,plain,
    ( k10_relat_1(sK2,k1_tarski(X0)) = k1_xboole_0
    | sK0(sK1,k2_relat_1(sK2)) != X0
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(resolution_lifted,[status(thm)],[c_92,c_115])).

cnf(c_150,plain,
    ( k10_relat_1(sK2,k1_tarski(sK0(sK1,k2_relat_1(sK2)))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_149])).

cnf(c_5,negated_conjecture,
    ( ~ r2_hidden(X0,sK1)
    | k10_relat_1(sK2,k1_tarski(X0)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_84,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k2_relat_1(sK2) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_4])).

cnf(c_85,plain,
    ( r2_hidden(sK0(sK1,k2_relat_1(sK2)),sK1) ),
    inference(unflattening,[status(thm)],[c_84])).

cnf(c_133,plain,
    ( k10_relat_1(sK2,k1_tarski(X0)) != k1_xboole_0
    | sK0(sK1,k2_relat_1(sK2)) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_85])).

cnf(c_134,plain,
    ( k10_relat_1(sK2,k1_tarski(sK0(sK1,k2_relat_1(sK2)))) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_133])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_150,c_134])).


%------------------------------------------------------------------------------
