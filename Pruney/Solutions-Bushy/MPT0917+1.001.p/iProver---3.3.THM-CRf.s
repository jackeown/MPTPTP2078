%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0917+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:25 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   27 (  52 expanded)
%              Number of clauses        :   10 (  11 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 168 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f5])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X4,X5)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
        & r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5))
      & r1_tarski(sK4,sK5)
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5))
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f9])).

fof(f16,plain,(
    ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,plain,(
    ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5)) ),
    inference(definition_unfolding,[],[f16,f11,f11])).

fof(f15,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_72,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X1,sK3))
    | ~ r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_110,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | ~ r1_tarski(sK2,sK3)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X0,sK4),k2_zfmisc_1(X1,sK5))
    | ~ r1_tarski(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_87,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5))
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | ~ r1_tarski(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_1,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_2,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_3,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_4,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_110,c_87,c_1,c_2,c_3,c_4])).


%------------------------------------------------------------------------------
