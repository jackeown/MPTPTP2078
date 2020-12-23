%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0522+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:29 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   33 (  45 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 137 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f15,plain,(
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

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(k5_relat_1(X1,k8_relat_1(X0,sK2)),k5_relat_1(X1,sK2))
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,X2)),k5_relat_1(sK1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12,f11])).

fof(f19,plain,(
    ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_1,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_66,plain,
    ( r1_tarski(k8_relat_1(X0_36,X0_35),X0_35)
    | ~ v1_relat_1(X0_35) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_112,plain,
    ( r1_tarski(k8_relat_1(sK0,sK2),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_67,plain,
    ( ~ v1_relat_1(X0_35)
    | v1_relat_1(k8_relat_1(X0_36,X0_35)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_109,plain,
    ( v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_65,plain,
    ( ~ r1_tarski(X0_35,X1_35)
    | r1_tarski(k5_relat_1(X2_35,X0_35),k5_relat_1(X2_35,X1_35))
    | ~ v1_relat_1(X1_35)
    | ~ v1_relat_1(X0_35)
    | ~ v1_relat_1(X2_35) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_96,plain,
    ( r1_tarski(k5_relat_1(X0_35,k8_relat_1(X0_36,X1_35)),k5_relat_1(X0_35,X1_35))
    | ~ r1_tarski(k8_relat_1(X0_36,X1_35),X1_35)
    | ~ v1_relat_1(X0_35)
    | ~ v1_relat_1(X1_35)
    | ~ v1_relat_1(k8_relat_1(X0_36,X1_35)) ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_101,plain,
    ( r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2))
    | ~ r1_tarski(k8_relat_1(sK0,sK2),sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_3,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_4,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_5,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_112,c_109,c_101,c_3,c_4,c_5])).


%------------------------------------------------------------------------------
