%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:09 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 384 expanded)
%              Number of clauses        :   32 (  83 expanded)
%              Number of leaves         :    6 (  82 expanded)
%              Depth                    :   12
%              Number of atoms          :  269 (2703 expanded)
%              Number of equality atoms :   40 ( 405 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f11])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f6])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f7])).

fof(f9,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))
   => k3_xboole_0(k4_xboole_0(sK2,sK4),sK3) != k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k3_xboole_0(k4_xboole_0(sK2,sK4),sK3) != k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f5,f16])).

fof(f30,plain,(
    k3_xboole_0(k4_xboole_0(sK2,sK4),sK3) != k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f18,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_622,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),X0)
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(sK2,X0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6115,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(sK2,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK4)
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_675,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),X0)
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),X1)
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1825,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),X0)
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(k3_xboole_0(sK2,sK3),X0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_4535,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,sK3))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1825])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_12,negated_conjecture,
    ( k3_xboole_0(k4_xboole_0(sK2,sK4),sK3) != k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2614,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(sK2,sK4)) ),
    inference(resolution,[status(thm)],[c_2,c_12])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3015,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(sK2,sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,sK3)) ),
    inference(resolution,[status(thm)],[c_2614,c_10])).

cnf(c_3202,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,sK3))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK4) ),
    inference(resolution,[status(thm)],[c_3015,c_10])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3214,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,sK3)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3202,c_5])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3512,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK3)
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK4) ),
    inference(resolution,[status(thm)],[c_3214,c_3])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_784,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK3) ),
    inference(resolution,[status(thm)],[c_1,c_12])).

cnf(c_1105,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK2,sK3))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK3) ),
    inference(resolution,[status(thm)],[c_11,c_784])).

cnf(c_486,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(sK2,sK4))
    | k3_xboole_0(k4_xboole_0(sK2,sK4),sK3) = k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_555,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(sK2,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_592,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_636,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),X0)
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK2,X0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_638,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK3)
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_1383,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1105,c_12,c_486,c_555,c_592,c_638])).

cnf(c_1538,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK2) ),
    inference(resolution,[status(thm)],[c_1383,c_5])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1536,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK3) ),
    inference(resolution,[status(thm)],[c_1383,c_4])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_569,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(sK2,sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK3)
    | k3_xboole_0(k4_xboole_0(sK2,sK4),sK3) = k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6115,c_4535,c_3512,c_3214,c_1538,c_1536,c_1383,c_569,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:41:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.78/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/0.98  
% 2.78/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/0.98  
% 2.78/0.98  ------  iProver source info
% 2.78/0.98  
% 2.78/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.78/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/0.98  git: non_committed_changes: false
% 2.78/0.98  git: last_make_outside_of_git: false
% 2.78/0.98  
% 2.78/0.98  ------ 
% 2.78/0.98  ------ Parsing...
% 2.78/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/0.98  ------ Proving...
% 2.78/0.98  ------ Problem Properties 
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  clauses                                 13
% 2.78/0.98  conjectures                             1
% 2.78/0.98  EPR                                     0
% 2.78/0.98  Horn                                    7
% 2.78/0.98  unary                                   1
% 2.78/0.98  binary                                  4
% 2.78/0.98  lits                                    35
% 2.78/0.98  lits eq                                 7
% 2.78/0.98  fd_pure                                 0
% 2.78/0.98  fd_pseudo                               0
% 2.78/0.98  fd_cond                                 0
% 2.78/0.98  fd_pseudo_cond                          6
% 2.78/0.98  AC symbols                              0
% 2.78/0.98  
% 2.78/0.98  ------ Input Options Time Limit: Unbounded
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  ------ 
% 2.78/0.98  Current options:
% 2.78/0.98  ------ 
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  ------ Proving...
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  % SZS status Theorem for theBenchmark.p
% 2.78/0.98  
% 2.78/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/0.98  
% 2.78/0.98  fof(f2,axiom,(
% 2.78/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f11,plain,(
% 2.78/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.78/0.98    inference(nnf_transformation,[],[f2])).
% 2.78/0.98  
% 2.78/0.98  fof(f12,plain,(
% 2.78/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.78/0.98    inference(flattening,[],[f11])).
% 2.78/0.98  
% 2.78/0.98  fof(f13,plain,(
% 2.78/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.78/0.98    inference(rectify,[],[f12])).
% 2.78/0.98  
% 2.78/0.98  fof(f14,plain,(
% 2.78/0.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.78/0.98    introduced(choice_axiom,[])).
% 2.78/0.98  
% 2.78/0.98  fof(f15,plain,(
% 2.78/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).
% 2.78/0.98  
% 2.78/0.98  fof(f26,plain,(
% 2.78/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.78/0.98    inference(cnf_transformation,[],[f15])).
% 2.78/0.98  
% 2.78/0.98  fof(f34,plain,(
% 2.78/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.78/0.98    inference(equality_resolution,[],[f26])).
% 2.78/0.98  
% 2.78/0.98  fof(f1,axiom,(
% 2.78/0.98    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f6,plain,(
% 2.78/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.78/0.98    inference(nnf_transformation,[],[f1])).
% 2.78/0.98  
% 2.78/0.98  fof(f7,plain,(
% 2.78/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.78/0.98    inference(flattening,[],[f6])).
% 2.78/0.98  
% 2.78/0.98  fof(f8,plain,(
% 2.78/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.78/0.98    inference(rectify,[],[f7])).
% 2.78/0.98  
% 2.78/0.98  fof(f9,plain,(
% 2.78/0.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.78/0.98    introduced(choice_axiom,[])).
% 2.78/0.98  
% 2.78/0.98  fof(f10,plain,(
% 2.78/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).
% 2.78/0.98  
% 2.78/0.98  fof(f21,plain,(
% 2.78/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f10])).
% 2.78/0.98  
% 2.78/0.98  fof(f3,conjecture,(
% 2.78/0.98    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 2.78/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/0.98  
% 2.78/0.98  fof(f4,negated_conjecture,(
% 2.78/0.98    ~! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 2.78/0.98    inference(negated_conjecture,[],[f3])).
% 2.78/0.98  
% 2.78/0.98  fof(f5,plain,(
% 2.78/0.98    ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 2.78/0.98    inference(ennf_transformation,[],[f4])).
% 2.78/0.98  
% 2.78/0.98  fof(f16,plain,(
% 2.78/0.98    ? [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) => k3_xboole_0(k4_xboole_0(sK2,sK4),sK3) != k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),
% 2.78/0.98    introduced(choice_axiom,[])).
% 2.78/0.98  
% 2.78/0.98  fof(f17,plain,(
% 2.78/0.98    k3_xboole_0(k4_xboole_0(sK2,sK4),sK3) != k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),
% 2.78/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f5,f16])).
% 2.78/0.98  
% 2.78/0.98  fof(f30,plain,(
% 2.78/0.98    k3_xboole_0(k4_xboole_0(sK2,sK4),sK3) != k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),
% 2.78/0.98    inference(cnf_transformation,[],[f17])).
% 2.78/0.98  
% 2.78/0.98  fof(f25,plain,(
% 2.78/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.78/0.98    inference(cnf_transformation,[],[f15])).
% 2.78/0.98  
% 2.78/0.98  fof(f35,plain,(
% 2.78/0.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.78/0.98    inference(equality_resolution,[],[f25])).
% 2.78/0.98  
% 2.78/0.98  fof(f18,plain,(
% 2.78/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.78/0.98    inference(cnf_transformation,[],[f10])).
% 2.78/0.98  
% 2.78/0.98  fof(f33,plain,(
% 2.78/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 2.78/0.98    inference(equality_resolution,[],[f18])).
% 2.78/0.98  
% 2.78/0.98  fof(f20,plain,(
% 2.78/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 2.78/0.98    inference(cnf_transformation,[],[f10])).
% 2.78/0.98  
% 2.78/0.98  fof(f31,plain,(
% 2.78/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.78/0.98    inference(equality_resolution,[],[f20])).
% 2.78/0.98  
% 2.78/0.98  fof(f24,plain,(
% 2.78/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.78/0.98    inference(cnf_transformation,[],[f15])).
% 2.78/0.98  
% 2.78/0.98  fof(f36,plain,(
% 2.78/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.78/0.98    inference(equality_resolution,[],[f24])).
% 2.78/0.98  
% 2.78/0.98  fof(f22,plain,(
% 2.78/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f10])).
% 2.78/0.98  
% 2.78/0.98  fof(f19,plain,(
% 2.78/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.78/0.98    inference(cnf_transformation,[],[f10])).
% 2.78/0.98  
% 2.78/0.98  fof(f32,plain,(
% 2.78/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 2.78/0.98    inference(equality_resolution,[],[f19])).
% 2.78/0.98  
% 2.78/0.98  fof(f23,plain,(
% 2.78/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.78/0.98    inference(cnf_transformation,[],[f10])).
% 2.78/0.98  
% 2.78/0.98  cnf(c_9,plain,
% 2.78/0.98      ( ~ r2_hidden(X0,X1)
% 2.78/0.98      | r2_hidden(X0,X2)
% 2.78/0.98      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 2.78/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_622,plain,
% 2.78/0.98      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),X0)
% 2.78/0.98      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(sK2,X0))
% 2.78/0.98      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK2) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_6115,plain,
% 2.78/0.98      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(sK2,sK4))
% 2.78/0.98      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK4)
% 2.78/0.98      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK2) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_622]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_675,plain,
% 2.78/0.98      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),X0)
% 2.78/0.98      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),X1)
% 2.78/0.98      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(X0,X1)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1825,plain,
% 2.78/0.98      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),X0)
% 2.78/0.98      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(k3_xboole_0(sK2,sK3),X0))
% 2.78/0.98      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK2,sK3)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_675]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_4535,plain,
% 2.78/0.98      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)))
% 2.78/0.98      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,sK3))
% 2.78/0.98      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK2,sK3)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1825]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2,plain,
% 2.78/0.98      ( r2_hidden(sK0(X0,X1,X2),X0)
% 2.78/0.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.78/0.98      | k3_xboole_0(X0,X1) = X2 ),
% 2.78/0.98      inference(cnf_transformation,[],[f21]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_12,negated_conjecture,
% 2.78/0.98      ( k3_xboole_0(k4_xboole_0(sK2,sK4),sK3) != k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)) ),
% 2.78/0.98      inference(cnf_transformation,[],[f30]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2614,plain,
% 2.78/0.98      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)))
% 2.78/0.98      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(sK2,sK4)) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_2,c_12]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_10,plain,
% 2.78/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.78/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3015,plain,
% 2.78/0.98      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(sK2,sK4))
% 2.78/0.98      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,sK3)) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_2614,c_10]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3202,plain,
% 2.78/0.98      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,sK3))
% 2.78/0.98      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK4) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_3015,c_10]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_5,plain,
% 2.78/0.98      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 2.78/0.98      inference(cnf_transformation,[],[f33]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3214,plain,
% 2.78/0.98      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,sK3)) ),
% 2.78/0.98      inference(forward_subsumption_resolution,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_3202,c_5]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3,plain,
% 2.78/0.98      ( ~ r2_hidden(X0,X1)
% 2.78/0.98      | ~ r2_hidden(X0,X2)
% 2.78/0.98      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 2.78/0.98      inference(cnf_transformation,[],[f31]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_3512,plain,
% 2.78/0.98      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK3)
% 2.78/0.98      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK4) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_3214,c_3]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_11,plain,
% 2.78/0.98      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 2.78/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1,plain,
% 2.78/0.98      ( r2_hidden(sK0(X0,X1,X2),X1)
% 2.78/0.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.78/0.98      | k3_xboole_0(X0,X1) = X2 ),
% 2.78/0.98      inference(cnf_transformation,[],[f22]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_784,plain,
% 2.78/0.98      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)))
% 2.78/0.98      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK3) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_1,c_12]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1105,plain,
% 2.78/0.98      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK2,sK3))
% 2.78/0.98      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK3) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_11,c_784]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_486,plain,
% 2.78/0.98      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)))
% 2.78/0.98      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(sK2,sK4))
% 2.78/0.98      | k3_xboole_0(k4_xboole_0(sK2,sK4),sK3) = k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_555,plain,
% 2.78/0.98      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(sK2,sK4))
% 2.78/0.98      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK2) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_592,plain,
% 2.78/0.98      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)))
% 2.78/0.98      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK2,sK3)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_636,plain,
% 2.78/0.98      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),X0)
% 2.78/0.98      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK2,X0))
% 2.78/0.98      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK2) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_638,plain,
% 2.78/0.98      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK2,sK3))
% 2.78/0.98      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK3)
% 2.78/0.98      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK2) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_636]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1383,plain,
% 2.78/0.98      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k3_xboole_0(sK2,sK3)) ),
% 2.78/0.98      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_1105,c_12,c_486,c_555,c_592,c_638]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1538,plain,
% 2.78/0.98      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK2) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_1383,c_5]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_4,plain,
% 2.78/0.98      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 2.78/0.98      inference(cnf_transformation,[],[f32]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1536,plain,
% 2.78/0.98      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK3) ),
% 2.78/0.98      inference(resolution,[status(thm)],[c_1383,c_4]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_0,plain,
% 2.78/0.98      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 2.78/0.98      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 2.78/0.98      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.78/0.98      | k3_xboole_0(X0,X1) = X2 ),
% 2.78/0.98      inference(cnf_transformation,[],[f23]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_569,plain,
% 2.78/0.98      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)))
% 2.78/0.98      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),k4_xboole_0(sK2,sK4))
% 2.78/0.98      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),sK3,k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3))),sK3)
% 2.78/0.98      | k3_xboole_0(k4_xboole_0(sK2,sK4),sK3) = k4_xboole_0(k3_xboole_0(sK2,sK3),k3_xboole_0(sK4,sK3)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(contradiction,plain,
% 2.78/0.98      ( $false ),
% 2.78/0.98      inference(minisat,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_6115,c_4535,c_3512,c_3214,c_1538,c_1536,c_1383,c_569,
% 2.78/0.98                 c_12]) ).
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/0.98  
% 2.78/0.98  ------                               Statistics
% 2.78/0.98  
% 2.78/0.98  ------ Selected
% 2.78/0.98  
% 2.78/0.98  total_time:                             0.179
% 2.78/0.98  
%------------------------------------------------------------------------------
