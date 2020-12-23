%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0023+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:16 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 128 expanded)
%              Number of clauses        :   23 (  29 expanded)
%              Number of leaves         :    4 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  165 (1005 expanded)
%              Number of equality atoms :   29 ( 134 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
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
    inference(flattening,[],[f5])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f6])).

fof(f8,plain,(
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

fof(f9,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f8])).

fof(f14,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f14])).

fof(f12,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f12])).

fof(f13,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f2])).

fof(f4,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),X2)
   => k3_xboole_0(k3_xboole_0(sK1,sK2),sK3) != k3_xboole_0(sK1,k3_xboole_0(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    k3_xboole_0(k3_xboole_0(sK1,sK2),sK3) != k3_xboole_0(sK1,k3_xboole_0(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f4,f10])).

fof(f18,plain,(
    k3_xboole_0(k3_xboole_0(sK1,sK2),sK3) != k3_xboole_0(sK1,k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_301,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),X0)
    | r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(X0,sK3))
    | ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1040,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),sK3)
    | ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_416,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK2,sK3))
    | r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_413,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK2,sK3))
    | r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_404,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),X0)
    | r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(X0,k3_xboole_0(sK2,sK3)))
    | ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_406,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK2,sK3))
    | r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK1,k3_xboole_0(sK2,sK3)))
    | ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),sK1) ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_345,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),X0)
    | r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(X0,sK2))
    | ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_347,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),sK2)
    | ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),sK1) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_297,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_294,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_274,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK1,k3_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_271,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_248,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK1,k3_xboole_0(sK2,sK3)))
    | ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),sK3)
    | k3_xboole_0(k3_xboole_0(sK1,sK2),sK3) = k3_xboole_0(sK1,k3_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_241,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK1,k3_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK1,sK2))
    | k3_xboole_0(k3_xboole_0(sK1,sK2),sK3) = k3_xboole_0(sK1,k3_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_238,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),k3_xboole_0(sK1,k3_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(k3_xboole_0(sK1,sK2),sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK3))),sK3)
    | k3_xboole_0(k3_xboole_0(sK1,sK2),sK3) = k3_xboole_0(sK1,k3_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),sK3) != k3_xboole_0(sK1,k3_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1040,c_416,c_413,c_406,c_347,c_297,c_294,c_274,c_271,c_248,c_241,c_238,c_6])).


%------------------------------------------------------------------------------
