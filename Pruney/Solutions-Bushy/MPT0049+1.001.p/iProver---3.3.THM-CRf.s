%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0049+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:20 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   70 (1653 expanded)
%              Number of clauses        :   37 ( 385 expanded)
%              Number of leaves         :    6 ( 344 expanded)
%              Depth                    :   19
%              Number of atoms          :  280 (11848 expanded)
%              Number of equality atoms :   41 (1696 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

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

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) != k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) != k4_xboole_0(k2_xboole_0(X0,X1),X2)
   => k2_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4)) != k4_xboole_0(k2_xboole_0(sK2,sK3),sK4) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4)) != k4_xboole_0(k2_xboole_0(sK2,sK3),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f5,f16])).

fof(f30,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4)) != k4_xboole_0(k2_xboole_0(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f18,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f18])).

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

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f20])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f19])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_12,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4)) != k4_xboole_0(k2_xboole_0(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2871,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4)) ),
    inference(resolution,[status(thm)],[c_2,c_12])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2940,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK4) ),
    inference(resolution,[status(thm)],[c_2871,c_10])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_767,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),X0)
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,X0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_784,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK3)
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_887,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),X0)
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,X0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_904,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK4)
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK2) ),
    inference(instantiation,[status(thm)],[c_887])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1198,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k2_xboole_0(sK2,sK3))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK3)
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2942,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k2_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_2871,c_11])).

cnf(c_2949,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2940,c_784,c_904,c_1198,c_2942])).

cnf(c_2950,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4)) ),
    inference(renaming,[status(thm)],[c_2949])).

cnf(c_3111,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK4) ),
    inference(resolution,[status(thm)],[c_2950,c_10])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_556,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
    | k2_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4)) = k4_xboole_0(k2_xboole_0(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1174,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),X0)
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k2_xboole_0(sK2,sK3),X0))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1191,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k2_xboole_0(sK2,sK3))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_1174])).

cnf(c_3113,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK3) ),
    inference(resolution,[status(thm)],[c_2950,c_11])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_770,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k2_xboole_0(X0,sK3))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3175,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k2_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_3392,plain,
    ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3111,c_12,c_556,c_1191,c_2950,c_3113,c_3175])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_3404,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4))
    | k2_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4)) = k4_xboole_0(k2_xboole_0(sK2,sK3),sK4) ),
    inference(resolution,[status(thm)],[c_3392,c_1])).

cnf(c_486,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4))
    | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4))
    | k2_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4)) = k4_xboole_0(k2_xboole_0(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4798,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3404,c_12,c_486,c_556,c_1191,c_2950,c_3111,c_3113,c_3175])).

cnf(c_5091,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k2_xboole_0(sK2,sK3))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK4) ),
    inference(resolution,[status(thm)],[c_4798,c_9])).

cnf(c_3406,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK4) ),
    inference(resolution,[status(thm)],[c_3392,c_10])).

cnf(c_9642,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k2_xboole_0(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5091,c_12,c_486,c_556,c_1191,c_2950,c_3111,c_3113,c_3175,c_3406])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9656,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK2) ),
    inference(resolution,[status(thm)],[c_9642,c_4])).

cnf(c_514,plain,
    ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4))
    | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9656,c_3392,c_514])).


%------------------------------------------------------------------------------
