%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0928+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:26 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   35 (  61 expanded)
%              Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 244 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      | ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      | ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f16,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      | ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( r1_tarski(X6,X7)
        & r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( r1_tarski(X6,X7)
          & r1_tarski(X4,X5)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7))
      & r1_tarski(X6,X7)
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7))
      & r1_tarski(X6,X7)
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ~ r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7))
        & r1_tarski(X6,X7)
        & r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7))
      & r1_tarski(sK6,sK7)
      & r1_tarski(sK4,sK5)
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ~ r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7))
    & r1_tarski(sK6,sK7)
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f11,f12])).

fof(f21,plain,(
    ~ r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7)) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f22,plain,(
    ~ r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK2,sK4),sK6),k2_zfmisc_1(k3_zfmisc_1(sK1,sK3,sK5),sK7)) ),
    inference(definition_unfolding,[],[f21,f14,f14])).

fof(f20,plain,(
    r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f13])).

fof(f19,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X4,X5)
    | r1_tarski(k3_zfmisc_1(X2,X0,X4),k3_zfmisc_1(X3,X1,X5)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_125,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k3_zfmisc_1(X0,sK2,X2),k3_zfmisc_1(X1,sK3,X3))
    | ~ r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_637,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_zfmisc_1(sK0,sK2,X0),k3_zfmisc_1(sK1,sK3,X1))
    | ~ r1_tarski(sK2,sK3)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_2236,plain,
    ( r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5))
    | ~ r1_tarski(sK4,sK5)
    | ~ r1_tarski(sK2,sK3)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_95,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X0,sK6),k2_zfmisc_1(X1,sK7))
    | ~ r1_tarski(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_145,plain,
    ( ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5))
    | r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK2,sK4),sK6),k2_zfmisc_1(k3_zfmisc_1(sK1,sK3,sK5),sK7))
    | ~ r1_tarski(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_2,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK2,sK4),sK6),k2_zfmisc_1(k3_zfmisc_1(sK1,sK3,sK5),sK7)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_3,negated_conjecture,
    ( r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_4,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_5,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_6,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2236,c_145,c_2,c_3,c_4,c_5,c_6])).


%------------------------------------------------------------------------------
