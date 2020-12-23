%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0121+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:31 EST 2020

% Result     : Theorem 0.87s
% Output     : CNFRefutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   31 (  65 expanded)
%              Number of clauses        :   15 (  19 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   83 ( 209 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          & r1_xboole_0(X1,X3)
          & r1_xboole_0(X0,X3) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(flattening,[],[f7])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
        & r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
   => ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
      & r1_xboole_0(sK2,sK3)
      & r1_xboole_0(sK1,sK3)
      & r1_xboole_0(sK0,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
    & r1_xboole_0(sK2,sK3)
    & r1_xboole_0(sK1,sK3)
    & r1_xboole_0(sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f18,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_518,plain,
    ( ~ r1_xboole_0(sK3,X0)
    | r1_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK0,sK1),X0))
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3005,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK0,sK1),sK2))
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_2904,plain,
    ( r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
    | ~ r1_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK0,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_147,plain,
    ( ~ r1_xboole_0(sK3,X0)
    | r1_xboole_0(sK3,k2_xboole_0(sK0,X0))
    | ~ r1_xboole_0(sK3,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_222,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ r1_xboole_0(sK3,sK1)
    | ~ r1_xboole_0(sK3,sK0) ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_117,plain,
    ( r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK0,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_114,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ r1_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_111,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_5,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_6,negated_conjecture,
    ( r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_7,negated_conjecture,
    ( r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3005,c_2904,c_222,c_117,c_114,c_111,c_4,c_5,c_6,c_7])).


%------------------------------------------------------------------------------
