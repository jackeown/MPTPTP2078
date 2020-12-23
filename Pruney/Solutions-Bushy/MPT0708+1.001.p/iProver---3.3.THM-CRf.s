%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0708+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:57 EST 2020

% Result     : Theorem 0.49s
% Output     : CNFRefutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   40 (  70 expanded)
%              Number of clauses        :   17 (  18 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :   11
%              Number of atoms          :  109 ( 247 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
            & r1_tarski(X0,k1_relat_1(X2)) )
         => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
            & r1_tarski(X0,k1_relat_1(X2)) )
         => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
      & r1_tarski(k9_relat_1(X2,X0),X1)
      & r1_tarski(X0,k1_relat_1(X2))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
      & r1_tarski(k9_relat_1(X2,X0),X1)
      & r1_tarski(X0,k1_relat_1(X2))
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
        & r1_tarski(k9_relat_1(X2,X0),X1)
        & r1_tarski(X0,k1_relat_1(X2))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK2,sK1))
      & r1_tarski(k9_relat_1(sK2,sK0),sK1)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,sK1))
    & r1_tarski(k9_relat_1(sK2,sK0),sK1)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f23,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f22,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f21,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_138,plain,
    ( ~ r1_tarski(X0_36,X1_36)
    | ~ r1_tarski(X1_36,X2_36)
    | r1_tarski(X0_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_188,plain,
    ( r1_tarski(X0_36,X1_36)
    | ~ r1_tarski(X0_36,k10_relat_1(sK2,k9_relat_1(sK2,X0_36)))
    | ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0_36)),X1_36) ),
    inference(instantiation,[status(thm)],[c_138])).

cnf(c_263,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,sK1))
    | ~ r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | r1_tarski(sK0,k10_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_6,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_78,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(resolution,[status(thm)],[c_1,c_6])).

cnf(c_133,plain,
    ( ~ r1_tarski(X0_36,X1_36)
    | r1_tarski(k10_relat_1(sK2,X0_36),k10_relat_1(sK2,X1_36)) ),
    inference(subtyping,[status(esa)],[c_78])).

cnf(c_167,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_0,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_67,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
    | ~ r1_tarski(X0,k1_relat_1(sK2)) ),
    inference(resolution,[status(thm)],[c_0,c_6])).

cnf(c_134,plain,
    ( r1_tarski(X0_36,k10_relat_1(sK2,k9_relat_1(sK2,X0_36)))
    | ~ r1_tarski(X0_36,k1_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_67])).

cnf(c_144,plain,
    ( r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | ~ r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_3,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_4,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_263,c_167,c_144,c_3,c_4,c_5])).


%------------------------------------------------------------------------------
