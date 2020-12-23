%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0892+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:21 EST 2020

% Result     : Theorem 0.57s
% Output     : CNFRefutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   28 (  45 expanded)
%              Number of clauses        :   14 (  16 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 120 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
     => ( ~ r1_xboole_0(X2,X5)
        & ~ r1_xboole_0(X1,X4)
        & ~ r1_xboole_0(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
       => ( ~ r1_xboole_0(X2,X5)
          & ~ r1_xboole_0(X1,X4)
          & ~ r1_xboole_0(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( r1_xboole_0(X2,X5)
        | r1_xboole_0(X1,X4)
        | r1_xboole_0(X0,X3) )
      & ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( r1_xboole_0(X2,X5)
          | r1_xboole_0(X1,X4)
          | r1_xboole_0(X0,X3) )
        & ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
   => ( ( r1_xboole_0(sK2,sK5)
        | r1_xboole_0(sK1,sK4)
        | r1_xboole_0(sK0,sK3) )
      & ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ( r1_xboole_0(sK2,sK5)
      | r1_xboole_0(sK1,sK4)
      | r1_xboole_0(sK0,sK3) )
    & ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f9])).

fof(f16,plain,
    ( r1_xboole_0(sK2,sK5)
    | r1_xboole_0(sK1,sK4)
    | r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f15,f11,f11])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_168,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK4))
    | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X2),k2_zfmisc_1(k2_zfmisc_1(X1,sK4),X3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_323,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),X1))
    | ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_872,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_118,plain,
    ( r1_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK4))
    | ~ r1_xboole_0(sK1,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_473,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ r1_xboole_0(sK1,sK4) ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_78,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK3,X1))
    | ~ r1_xboole_0(sK0,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_322,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ r1_xboole_0(sK0,sK3) ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_201,plain,
    ( r1_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X1,sK5))
    | ~ r1_xboole_0(sK2,sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_276,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ r1_xboole_0(sK2,sK5) ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_3,negated_conjecture,
    ( r1_xboole_0(sK0,sK3)
    | r1_xboole_0(sK1,sK4)
    | r1_xboole_0(sK2,sK5) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_4,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_872,c_473,c_322,c_276,c_3,c_4])).


%------------------------------------------------------------------------------
