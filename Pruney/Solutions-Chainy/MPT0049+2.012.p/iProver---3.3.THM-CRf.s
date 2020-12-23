%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:40 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
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
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:04:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.98/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.00  
% 2.98/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.98/1.00  
% 2.98/1.00  ------  iProver source info
% 2.98/1.00  
% 2.98/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.98/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.98/1.00  git: non_committed_changes: false
% 2.98/1.00  git: last_make_outside_of_git: false
% 2.98/1.00  
% 2.98/1.00  ------ 
% 2.98/1.00  ------ Parsing...
% 2.98/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.98/1.00  
% 2.98/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.98/1.00  
% 2.98/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.98/1.00  
% 2.98/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.98/1.00  ------ Proving...
% 2.98/1.00  ------ Problem Properties 
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  clauses                                 13
% 2.98/1.00  conjectures                             1
% 2.98/1.00  EPR                                     0
% 2.98/1.00  Horn                                    7
% 2.98/1.00  unary                                   1
% 2.98/1.00  binary                                  4
% 2.98/1.00  lits                                    35
% 2.98/1.00  lits eq                                 7
% 2.98/1.00  fd_pure                                 0
% 2.98/1.00  fd_pseudo                               0
% 2.98/1.00  fd_cond                                 0
% 2.98/1.00  fd_pseudo_cond                          6
% 2.98/1.00  AC symbols                              0
% 2.98/1.00  
% 2.98/1.00  ------ Input Options Time Limit: Unbounded
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  ------ 
% 2.98/1.00  Current options:
% 2.98/1.00  ------ 
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  ------ Proving...
% 2.98/1.00  
% 2.98/1.00  
% 2.98/1.00  % SZS status Theorem for theBenchmark.p
% 2.98/1.00  
% 2.98/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.98/1.00  
% 2.98/1.00  fof(f1,axiom,(
% 2.98/1.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f6,plain,(
% 2.98/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.98/1.00    inference(nnf_transformation,[],[f1])).
% 2.98/1.00  
% 2.98/1.00  fof(f7,plain,(
% 2.98/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.98/1.00    inference(flattening,[],[f6])).
% 2.98/1.00  
% 2.98/1.00  fof(f8,plain,(
% 2.98/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.98/1.00    inference(rectify,[],[f7])).
% 2.98/1.00  
% 2.98/1.00  fof(f9,plain,(
% 2.98/1.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.98/1.00    introduced(choice_axiom,[])).
% 2.98/1.00  
% 2.98/1.00  fof(f10,plain,(
% 2.98/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.98/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).
% 2.98/1.00  
% 2.98/1.00  fof(f21,plain,(
% 2.98/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.98/1.00    inference(cnf_transformation,[],[f10])).
% 2.98/1.00  
% 2.98/1.00  fof(f3,conjecture,(
% 2.98/1.00    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 2.98/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.00  
% 2.98/1.00  fof(f4,negated_conjecture,(
% 2.98/1.00    ~! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 2.98/1.00    inference(negated_conjecture,[],[f3])).
% 2.98/1.00  
% 2.98/1.00  fof(f5,plain,(
% 2.98/1.00    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) != k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 2.98/1.00    inference(ennf_transformation,[],[f4])).
% 2.98/1.00  
% 2.98/1.00  fof(f16,plain,(
% 2.98/1.00    ? [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) != k4_xboole_0(k2_xboole_0(X0,X1),X2) => k2_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4)) != k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),
% 2.98/1.00    introduced(choice_axiom,[])).
% 2.98/1.00  
% 2.98/1.00  fof(f17,plain,(
% 2.98/1.00    k2_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4)) != k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),
% 2.98/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f5,f16])).
% 2.98/1.00  
% 2.98/1.00  fof(f30,plain,(
% 2.98/1.00    k2_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4)) != k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),
% 2.98/1.00    inference(cnf_transformation,[],[f17])).
% 2.98/1.00  
% 2.98/1.00  fof(f2,axiom,(
% 2.98/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f11,plain,(
% 2.98/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.98/1.01    inference(nnf_transformation,[],[f2])).
% 2.98/1.01  
% 2.98/1.01  fof(f12,plain,(
% 2.98/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.98/1.01    inference(flattening,[],[f11])).
% 2.98/1.01  
% 2.98/1.01  fof(f13,plain,(
% 2.98/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.98/1.01    inference(rectify,[],[f12])).
% 2.98/1.01  
% 2.98/1.01  fof(f14,plain,(
% 2.98/1.01    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.98/1.01    introduced(choice_axiom,[])).
% 2.98/1.01  
% 2.98/1.01  fof(f15,plain,(
% 2.98/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).
% 2.98/1.01  
% 2.98/1.01  fof(f25,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.98/1.01    inference(cnf_transformation,[],[f15])).
% 2.98/1.01  
% 2.98/1.01  fof(f35,plain,(
% 2.98/1.01    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.98/1.01    inference(equality_resolution,[],[f25])).
% 2.98/1.01  
% 2.98/1.01  fof(f26,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.98/1.01    inference(cnf_transformation,[],[f15])).
% 2.98/1.01  
% 2.98/1.01  fof(f34,plain,(
% 2.98/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.98/1.01    inference(equality_resolution,[],[f26])).
% 2.98/1.01  
% 2.98/1.01  fof(f18,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.98/1.01    inference(cnf_transformation,[],[f10])).
% 2.98/1.01  
% 2.98/1.01  fof(f33,plain,(
% 2.98/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 2.98/1.01    inference(equality_resolution,[],[f18])).
% 2.98/1.01  
% 2.98/1.01  fof(f24,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.98/1.01    inference(cnf_transformation,[],[f15])).
% 2.98/1.01  
% 2.98/1.01  fof(f36,plain,(
% 2.98/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.98/1.01    inference(equality_resolution,[],[f24])).
% 2.98/1.01  
% 2.98/1.01  fof(f23,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f10])).
% 2.98/1.01  
% 2.98/1.01  fof(f20,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.98/1.01    inference(cnf_transformation,[],[f10])).
% 2.98/1.01  
% 2.98/1.01  fof(f31,plain,(
% 2.98/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.98/1.01    inference(equality_resolution,[],[f20])).
% 2.98/1.01  
% 2.98/1.01  fof(f22,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f10])).
% 2.98/1.01  
% 2.98/1.01  fof(f19,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.98/1.01    inference(cnf_transformation,[],[f10])).
% 2.98/1.01  
% 2.98/1.01  fof(f32,plain,(
% 2.98/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 2.98/1.01    inference(equality_resolution,[],[f19])).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2,plain,
% 2.98/1.01      ( r2_hidden(sK0(X0,X1,X2),X1)
% 2.98/1.01      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.98/1.01      | r2_hidden(sK0(X0,X1,X2),X0)
% 2.98/1.01      | k2_xboole_0(X0,X1) = X2 ),
% 2.98/1.01      inference(cnf_transformation,[],[f21]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_12,negated_conjecture,
% 2.98/1.01      ( k2_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4)) != k4_xboole_0(k2_xboole_0(sK2,sK3),sK4) ),
% 2.98/1.01      inference(cnf_transformation,[],[f30]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2871,plain,
% 2.98/1.01      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4))
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4)) ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_2,c_12]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_10,plain,
% 2.98/1.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.98/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2940,plain,
% 2.98/1.01      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4))
% 2.98/1.01      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK4) ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_2871,c_10]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_9,plain,
% 2.98/1.01      ( ~ r2_hidden(X0,X1)
% 2.98/1.01      | r2_hidden(X0,X2)
% 2.98/1.01      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 2.98/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_767,plain,
% 2.98/1.01      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),X0)
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,X0))
% 2.98/1.01      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK3) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_784,plain,
% 2.98/1.01      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
% 2.98/1.01      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK3)
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK4) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_767]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_887,plain,
% 2.98/1.01      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),X0)
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,X0))
% 2.98/1.01      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK2) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_904,plain,
% 2.98/1.01      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4))
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK4)
% 2.98/1.01      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK2) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_887]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5,plain,
% 2.98/1.01      ( r2_hidden(X0,X1)
% 2.98/1.01      | r2_hidden(X0,X2)
% 2.98/1.01      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 2.98/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1198,plain,
% 2.98/1.01      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k2_xboole_0(sK2,sK3))
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK3)
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK2) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_11,plain,
% 2.98/1.01      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 2.98/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2942,plain,
% 2.98/1.01      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4))
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k2_xboole_0(sK2,sK3)) ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_2871,c_11]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2949,plain,
% 2.98/1.01      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4))
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4)) ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_2940,c_784,c_904,c_1198,c_2942]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2950,plain,
% 2.98/1.01      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4)) ),
% 2.98/1.01      inference(renaming,[status(thm)],[c_2949]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3111,plain,
% 2.98/1.01      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4))
% 2.98/1.01      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK4) ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_2950,c_10]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_0,plain,
% 2.98/1.01      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 2.98/1.01      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.98/1.01      | k2_xboole_0(X0,X1) = X2 ),
% 2.98/1.01      inference(cnf_transformation,[],[f23]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_556,plain,
% 2.98/1.01      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4))
% 2.98/1.01      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
% 2.98/1.01      | k2_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4)) = k4_xboole_0(k2_xboole_0(sK2,sK3),sK4) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1174,plain,
% 2.98/1.01      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),X0)
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k2_xboole_0(sK2,sK3),X0))
% 2.98/1.01      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k2_xboole_0(sK2,sK3)) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1191,plain,
% 2.98/1.01      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4))
% 2.98/1.01      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k2_xboole_0(sK2,sK3))
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK4) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_1174]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3113,plain,
% 2.98/1.01      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4))
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK3) ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_2950,c_11]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3,plain,
% 2.98/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 2.98/1.01      inference(cnf_transformation,[],[f31]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_770,plain,
% 2.98/1.01      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k2_xboole_0(X0,sK3))
% 2.98/1.01      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK3) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3175,plain,
% 2.98/1.01      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k2_xboole_0(sK2,sK3))
% 2.98/1.01      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK3) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_770]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3392,plain,
% 2.98/1.01      ( r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4)) ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_3111,c_12,c_556,c_1191,c_2950,c_3113,c_3175]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1,plain,
% 2.98/1.01      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.98/1.01      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 2.98/1.01      | k2_xboole_0(X0,X1) = X2 ),
% 2.98/1.01      inference(cnf_transformation,[],[f22]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3404,plain,
% 2.98/1.01      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4))
% 2.98/1.01      | k2_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4)) = k4_xboole_0(k2_xboole_0(sK2,sK3),sK4) ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_3392,c_1]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_486,plain,
% 2.98/1.01      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4))
% 2.98/1.01      | ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4))
% 2.98/1.01      | k2_xboole_0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4)) = k4_xboole_0(k2_xboole_0(sK2,sK3),sK4) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_4798,plain,
% 2.98/1.01      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)) ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_3404,c_12,c_486,c_556,c_1191,c_2950,c_3111,c_3113,
% 2.98/1.01                 c_3175]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5091,plain,
% 2.98/1.01      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k2_xboole_0(sK2,sK3))
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK4) ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_4798,c_9]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3406,plain,
% 2.98/1.01      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK4) ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_3392,c_10]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_9642,plain,
% 2.98/1.01      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k2_xboole_0(sK2,sK3)) ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_5091,c_12,c_486,c_556,c_1191,c_2950,c_3111,c_3113,
% 2.98/1.01                 c_3175,c_3406]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_4,plain,
% 2.98/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 2.98/1.01      inference(cnf_transformation,[],[f32]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_9656,plain,
% 2.98/1.01      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK2) ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_9642,c_4]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_514,plain,
% 2.98/1.01      ( ~ r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK2,sK4))
% 2.98/1.01      | r2_hidden(sK0(k4_xboole_0(sK2,sK4),k4_xboole_0(sK3,sK4),k4_xboole_0(k2_xboole_0(sK2,sK3),sK4)),sK2) ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(contradiction,plain,
% 2.98/1.01      ( $false ),
% 2.98/1.01      inference(minisat,[status(thm)],[c_9656,c_3392,c_514]) ).
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.98/1.01  
% 2.98/1.01  ------                               Statistics
% 2.98/1.01  
% 2.98/1.01  ------ Selected
% 2.98/1.01  
% 2.98/1.01  total_time:                             0.293
% 2.98/1.01  
%------------------------------------------------------------------------------
