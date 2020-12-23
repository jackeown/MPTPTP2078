%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0518+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:29 EST 2020

% Result     : Theorem 0.64s
% Output     : CNFRefutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   30 (  35 expanded)
%              Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 (  88 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f18,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0_35,X1_35)
    | r1_tarski(k2_relat_1(X0_35),k2_relat_1(X1_35))
    | ~ v1_relat_1(X1_35)
    | ~ v1_relat_1(X0_35) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_103,plain,
    ( ~ r1_tarski(k8_relat_1(X0_36,X0_35),X0_35)
    | r1_tarski(k2_relat_1(k8_relat_1(X0_36,X0_35)),k2_relat_1(X0_35))
    | ~ v1_relat_1(X0_35)
    | ~ v1_relat_1(k8_relat_1(X0_36,X0_35)) ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_105,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK1),sK1)
    | r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(sK1))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_1,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_68,plain,
    ( r1_tarski(k8_relat_1(X0_36,X0_35),X0_35)
    | ~ v1_relat_1(X0_35) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_74,plain,
    ( r1_tarski(k8_relat_1(sK0,sK1),sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_69,plain,
    ( ~ v1_relat_1(X0_35)
    | v1_relat_1(k8_relat_1(X0_36,X0_35)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_71,plain,
    ( v1_relat_1(k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_4,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_5,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_105,c_74,c_71,c_4,c_5])).


%------------------------------------------------------------------------------
