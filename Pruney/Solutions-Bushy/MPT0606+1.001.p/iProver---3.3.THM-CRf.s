%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0606+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:42 EST 2020

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   46 (  84 expanded)
%              Number of clauses        :   26 (  28 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  138 ( 356 expanded)
%              Number of equality atoms :   32 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( r1_tarski(X2,X1)
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( ( v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( r1_tarski(X2,X1)
             => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(sK2,k7_relat_1(X1,X0))
        & r1_tarski(sK2,X1)
        & v4_relat_1(sK2,X0)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
            & r1_tarski(X2,X1)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
          & r1_tarski(X2,sK1)
          & v4_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
    & r1_tarski(sK2,sK1)
    & v4_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12,f11])).

fof(f18,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    ~ r1_tarski(sK2,k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f19,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_127,plain,
    ( X0_35 != X1_35
    | X2_35 != X1_35
    | X2_35 = X0_35 ),
    theory(equality)).

cnf(c_366,plain,
    ( X0_35 != X1_35
    | X0_35 = k7_relat_1(sK2,X0_36)
    | k7_relat_1(sK2,X0_36) != X1_35 ),
    inference(instantiation,[status(thm)],[c_127])).

cnf(c_367,plain,
    ( k7_relat_1(sK2,sK0) != sK2
    | sK2 = k7_relat_1(sK2,sK0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_126,plain,
    ( X0_35 = X0_35 ),
    theory(equality)).

cnf(c_310,plain,
    ( k7_relat_1(sK1,X0_36) = k7_relat_1(sK1,X0_36) ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_315,plain,
    ( k7_relat_1(sK1,sK0) = k7_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_129,plain,
    ( ~ r1_tarski(X0_35,X1_35)
    | r1_tarski(X2_35,X3_35)
    | X2_35 != X0_35
    | X3_35 != X1_35 ),
    theory(equality)).

cnf(c_283,plain,
    ( r1_tarski(X0_35,X1_35)
    | ~ r1_tarski(k7_relat_1(sK2,X0_36),k7_relat_1(sK1,X0_36))
    | X1_35 != k7_relat_1(sK1,X0_36)
    | X0_35 != k7_relat_1(sK2,X0_36) ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_309,plain,
    ( r1_tarski(X0_35,k7_relat_1(sK1,X0_36))
    | ~ r1_tarski(k7_relat_1(sK2,X0_36),k7_relat_1(sK1,X0_36))
    | X0_35 != k7_relat_1(sK2,X0_36)
    | k7_relat_1(sK1,X0_36) != k7_relat_1(sK1,X0_36) ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_312,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK1,sK0))
    | r1_tarski(sK2,k7_relat_1(sK1,sK0))
    | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0)
    | sK2 != k7_relat_1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(X0,X2),k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_124,plain,
    ( ~ r1_tarski(X0_35,X1_35)
    | r1_tarski(k7_relat_1(X0_35,X0_36),k7_relat_1(X1_35,X0_36))
    | ~ v1_relat_1(X1_35)
    | ~ v1_relat_1(X0_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_269,plain,
    ( r1_tarski(k7_relat_1(sK2,X0_36),k7_relat_1(sK1,X0_36))
    | ~ r1_tarski(sK2,sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_124])).

cnf(c_271,plain,
    ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK1,sK0))
    | ~ r1_tarski(sK2,sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_1,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_4,negated_conjecture,
    ( v4_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_74,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_4])).

cnf(c_75,plain,
    ( ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,sK0) = sK2 ),
    inference(unflattening,[status(thm)],[c_74])).

cnf(c_5,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_77,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_75,c_5])).

cnf(c_119,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(subtyping,[status(esa)],[c_77])).

cnf(c_135,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_2,negated_conjecture,
    ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_3,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_6,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_367,c_315,c_312,c_271,c_119,c_135,c_2,c_3,c_5,c_6])).


%------------------------------------------------------------------------------
