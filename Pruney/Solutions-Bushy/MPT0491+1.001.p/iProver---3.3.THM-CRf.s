%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0491+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:25 EST 2020

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   30 (  47 expanded)
%              Number of clauses        :   11 (  12 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 119 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f8,f13])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

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

fof(f9,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f9])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_6,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_116,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
    | r2_hidden(X0,k1_relat_1(sK2)) ),
    inference(resolution,[status(thm)],[c_3,c_6])).

cnf(c_169,plain,
    ( ~ r2_hidden(X0_36,k1_relat_1(k7_relat_1(sK2,X0_37)))
    | r2_hidden(X0_36,k1_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_116])).

cnf(c_200,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)),k1_relat_1(k7_relat_1(sK2,sK1)))
    | r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_81,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    inference(resolution,[status(thm)],[c_0,c_5])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_75,plain,
    ( r2_hidden(sK0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(sK2)),k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(resolution,[status(thm)],[c_1,c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_200,c_81,c_75])).


%------------------------------------------------------------------------------
