%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0468+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:22 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   45 (  82 expanded)
%              Number of clauses        :   19 (  26 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 205 expanded)
%              Number of equality atoms :   40 (  70 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X1] :
      ( ? [X2,X3] : k4_tarski(X2,X3) = X1
     => k4_tarski(sK0(X1),sK1(X1)) = X1 ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tarski(sK0(X1),sK1(X1)) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_tarski(sK0(X1),sK1(X1)) = X1
      | ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f18,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != sK3
      & ! [X2,X1] : ~ r2_hidden(k4_tarski(X1,X2),sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( k1_xboole_0 != sK3
    & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f18])).

fof(f24,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f2,f16])).

fof(f21,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
    ! [X2,X1] : ~ r2_hidden(k4_tarski(X1,X2),sK3) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(sK0(X0),sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_6,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_73,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(sK0(X0),sK1(X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_74,plain,
    ( ~ r2_hidden(X0,sK3)
    | k4_tarski(sK0(X0),sK1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_73])).

cnf(c_1,plain,
    ( m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_88,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | sK2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_89,plain,
    ( r2_hidden(sK2(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_88])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_103,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_89,c_3])).

cnf(c_126,plain,
    ( k4_tarski(sK0(X0),sK1(X0)) = X0
    | sK2(X1) != X0
    | sK3 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_74,c_103])).

cnf(c_127,plain,
    ( k4_tarski(sK0(sK2(sK3)),sK1(sK2(sK3))) = sK2(sK3)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_126])).

cnf(c_4,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_128,plain,
    ( k4_tarski(sK0(sK2(sK3)),sK1(sK2(sK3))) = sK2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_127,c_4])).

cnf(c_5,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK3) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_117,plain,
    ( k4_tarski(X0,X1) != sK2(X2)
    | sK3 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_103])).

cnf(c_118,plain,
    ( k4_tarski(X0,X1) != sK2(sK3)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_117])).

cnf(c_120,plain,
    ( k4_tarski(X0,X1) != sK2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_118,c_4])).

cnf(c_131,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_128,c_120])).


%------------------------------------------------------------------------------
