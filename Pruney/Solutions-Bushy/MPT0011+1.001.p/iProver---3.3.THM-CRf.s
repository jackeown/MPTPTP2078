%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0011+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:14 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 132 expanded)
%              Number of clauses        :   27 (  33 expanded)
%              Number of leaves         :    4 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  173 (1013 expanded)
%              Number of equality atoms :   29 ( 134 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f6])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f7])).

fof(f9,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f14,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f14])).

fof(f15,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f15])).

fof(f16,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f16])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) != k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) != k2_xboole_0(k2_xboole_0(X0,X1),X2)
   => k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) != k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) != k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f5,f11])).

fof(f20,plain,(
    k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) != k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_201,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),X0)
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(X0,sK3))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2857,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK2,sK3))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK3)
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_296,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),X0)
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1357,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_296])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_291,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(X0,sK3))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1068,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_291])).

cnf(c_501,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),X0)
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(X0,k2_xboole_0(X1,sK3))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_928,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK1) ),
    inference(instantiation,[status(thm)],[c_501])).

cnf(c_496,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(X0,k2_xboole_0(X1,sK3)))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(X1,sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_894,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK2,sK3))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_286,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),X0)
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(X0,k2_xboole_0(X1,sK3)))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(X1,sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_492,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK1) ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_263,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),X0)
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(X0,sK2))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_265,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK2)
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK1) ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_219,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_216,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_186,plain,
    ( r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK3)
    | k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) = k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_187,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK3)
    | k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) = k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_188,plain,
    ( ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | ~ r2_hidden(sK0(k2_xboole_0(sK1,sK2),sK3,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
    | k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) = k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) != k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2857,c_1357,c_1068,c_928,c_894,c_492,c_265,c_219,c_216,c_186,c_187,c_188,c_7])).


%------------------------------------------------------------------------------
