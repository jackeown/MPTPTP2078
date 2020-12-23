%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0559+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:35 EST 2020

% Result     : Theorem 0.58s
% Output     : CNFRefutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   30 (  35 expanded)
%              Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 (  85 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f17,plain,(
    ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X0,X2),k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_56,plain,
    ( ~ r1_tarski(X0_35,X1_35)
    | r1_tarski(k9_relat_1(X0_35,X0_36),k9_relat_1(X1_35,X0_36))
    | ~ v1_relat_1(X0_35)
    | ~ v1_relat_1(X1_35) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_84,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(X0_35,X0_37),X0_36),k9_relat_1(X0_35,X0_36))
    | ~ r1_tarski(k7_relat_1(X0_35,X0_37),X0_35)
    | ~ v1_relat_1(X0_35)
    | ~ v1_relat_1(k7_relat_1(X0_35,X0_37)) ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_86,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_2,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_55,plain,
    ( r1_tarski(k7_relat_1(X0_35,X0_37),X0_35)
    | ~ v1_relat_1(X0_35) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_65,plain,
    ( r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_57,plain,
    ( ~ v1_relat_1(X0_35)
    | v1_relat_1(k7_relat_1(X0_35,X0_37)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_59,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_3,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_4,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_86,c_65,c_59,c_3,c_4])).


%------------------------------------------------------------------------------
