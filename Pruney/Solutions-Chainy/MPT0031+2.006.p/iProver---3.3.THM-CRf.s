%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:25 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 311 expanded)
%              Number of clauses        :   34 (  76 expanded)
%              Number of leaves         :    6 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  278 (2310 expanded)
%              Number of equality atoms :   40 ( 309 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f26])).

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

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))
   => k2_xboole_0(sK2,k3_xboole_0(sK3,sK4)) != k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k2_xboole_0(sK2,k3_xboole_0(sK3,sK4)) != k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f5,f16])).

fof(f30,plain,(
    k2_xboole_0(sK2,k3_xboole_0(sK3,sK4)) != k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

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

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_992,plain,
    ( ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),X0)
    | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(k2_xboole_0(sK2,X1),X0))
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8751,plain,
    ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)))
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK4))
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_442,plain,
    ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,X0))
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5871,plain,
    ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_5868,plain,
    ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK4))
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_12,negated_conjecture,
    ( k2_xboole_0(sK2,k3_xboole_0(sK3,sK4)) != k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_4515,plain,
    ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)))
    | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(sK3,sK4))
    | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
    inference(resolution,[status(thm)],[c_2,c_12])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_522,plain,
    ( ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)))
    | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_525,plain,
    ( ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)))
    | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3556,plain,
    ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),X0)
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(X0,sK4))
    | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3558,plain,
    ( ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK4))
    | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK4)
    | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
    inference(instantiation,[status(thm)],[c_3556])).

cnf(c_3614,plain,
    ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),X0)
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(X0,sK3))
    | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3616,plain,
    ( ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK3))
    | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK3)
    | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
    inference(instantiation,[status(thm)],[c_3614])).

cnf(c_781,plain,
    ( ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),X0)
    | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(sK3,X0))
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3968,plain,
    ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK4)
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_781])).

cnf(c_5423,plain,
    ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(sK3,sK4))
    | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4515,c_522,c_525,c_3558,c_3616,c_3968])).

cnf(c_5441,plain,
    ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK3)
    | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
    inference(resolution,[status(thm)],[c_5423,c_11])).

cnf(c_5439,plain,
    ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK4)
    | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
    inference(resolution,[status(thm)],[c_5423,c_10])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_768,plain,
    ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(X0,sK3))
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_770,plain,
    ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_768])).

cnf(c_748,plain,
    ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(X0,sK4))
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_750,plain,
    ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK4))
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK4) ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_499,plain,
    ( ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)))
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(sK3,sK4))
    | k2_xboole_0(sK2,k3_xboole_0(sK3,sK4)) = k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_438,plain,
    ( ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)))
    | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2)
    | k2_xboole_0(sK2,k3_xboole_0(sK3,sK4)) = k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8751,c_5871,c_5868,c_5441,c_5439,c_5423,c_770,c_750,c_499,c_438,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:17:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.64/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.64/0.99  
% 3.64/0.99  ------  iProver source info
% 3.64/0.99  
% 3.64/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.64/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.64/0.99  git: non_committed_changes: false
% 3.64/0.99  git: last_make_outside_of_git: false
% 3.64/0.99  
% 3.64/0.99  ------ 
% 3.64/0.99  ------ Parsing...
% 3.64/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/0.99  ------ Proving...
% 3.64/0.99  ------ Problem Properties 
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  clauses                                 13
% 3.64/0.99  conjectures                             1
% 3.64/0.99  EPR                                     0
% 3.64/0.99  Horn                                    9
% 3.64/0.99  unary                                   1
% 3.64/0.99  binary                                  4
% 3.64/0.99  lits                                    35
% 3.64/0.99  lits eq                                 7
% 3.64/0.99  fd_pure                                 0
% 3.64/0.99  fd_pseudo                               0
% 3.64/0.99  fd_cond                                 0
% 3.64/0.99  fd_pseudo_cond                          6
% 3.64/0.99  AC symbols                              0
% 3.64/0.99  
% 3.64/0.99  ------ Input Options Time Limit: Unbounded
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ 
% 3.64/0.99  Current options:
% 3.64/0.99  ------ 
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ Proving...
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  % SZS status Theorem for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  fof(f2,axiom,(
% 3.64/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f11,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.64/0.99    inference(nnf_transformation,[],[f2])).
% 3.64/0.99  
% 3.64/0.99  fof(f12,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.64/0.99    inference(flattening,[],[f11])).
% 3.64/0.99  
% 3.64/0.99  fof(f13,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.64/0.99    inference(rectify,[],[f12])).
% 3.64/0.99  
% 3.64/0.99  fof(f14,plain,(
% 3.64/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f15,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).
% 3.64/0.99  
% 3.64/0.99  fof(f26,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 3.64/0.99    inference(cnf_transformation,[],[f15])).
% 3.64/0.99  
% 3.64/0.99  fof(f34,plain,(
% 3.64/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.64/0.99    inference(equality_resolution,[],[f26])).
% 3.64/0.99  
% 3.64/0.99  fof(f1,axiom,(
% 3.64/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f6,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.64/0.99    inference(nnf_transformation,[],[f1])).
% 3.64/0.99  
% 3.64/0.99  fof(f7,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.64/0.99    inference(flattening,[],[f6])).
% 3.64/0.99  
% 3.64/0.99  fof(f8,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.64/0.99    inference(rectify,[],[f7])).
% 3.64/0.99  
% 3.64/0.99  fof(f9,plain,(
% 3.64/0.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f10,plain,(
% 3.64/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).
% 3.64/0.99  
% 3.64/0.99  fof(f19,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.64/0.99    inference(cnf_transformation,[],[f10])).
% 3.64/0.99  
% 3.64/0.99  fof(f32,plain,(
% 3.64/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 3.64/0.99    inference(equality_resolution,[],[f19])).
% 3.64/0.99  
% 3.64/0.99  fof(f21,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f10])).
% 3.64/0.99  
% 3.64/0.99  fof(f3,conjecture,(
% 3.64/0.99    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 3.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f4,negated_conjecture,(
% 3.64/0.99    ~! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 3.64/0.99    inference(negated_conjecture,[],[f3])).
% 3.64/0.99  
% 3.64/0.99  fof(f5,plain,(
% 3.64/0.99    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 3.64/0.99    inference(ennf_transformation,[],[f4])).
% 3.64/0.99  
% 3.64/0.99  fof(f16,plain,(
% 3.64/0.99    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) => k2_xboole_0(sK2,k3_xboole_0(sK3,sK4)) != k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f17,plain,(
% 3.64/0.99    k2_xboole_0(sK2,k3_xboole_0(sK3,sK4)) != k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),
% 3.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f5,f16])).
% 3.64/0.99  
% 3.64/0.99  fof(f30,plain,(
% 3.64/0.99    k2_xboole_0(sK2,k3_xboole_0(sK3,sK4)) != k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),
% 3.64/0.99    inference(cnf_transformation,[],[f17])).
% 3.64/0.99  
% 3.64/0.99  fof(f25,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.64/0.99    inference(cnf_transformation,[],[f15])).
% 3.64/0.99  
% 3.64/0.99  fof(f35,plain,(
% 3.64/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.64/0.99    inference(equality_resolution,[],[f25])).
% 3.64/0.99  
% 3.64/0.99  fof(f24,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.64/0.99    inference(cnf_transformation,[],[f15])).
% 3.64/0.99  
% 3.64/0.99  fof(f36,plain,(
% 3.64/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.64/0.99    inference(equality_resolution,[],[f24])).
% 3.64/0.99  
% 3.64/0.99  fof(f18,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.64/0.99    inference(cnf_transformation,[],[f10])).
% 3.64/0.99  
% 3.64/0.99  fof(f33,plain,(
% 3.64/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 3.64/0.99    inference(equality_resolution,[],[f18])).
% 3.64/0.99  
% 3.64/0.99  fof(f20,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.64/0.99    inference(cnf_transformation,[],[f10])).
% 3.64/0.99  
% 3.64/0.99  fof(f31,plain,(
% 3.64/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.64/0.99    inference(equality_resolution,[],[f20])).
% 3.64/0.99  
% 3.64/0.99  fof(f23,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f10])).
% 3.64/0.99  
% 3.64/0.99  fof(f22,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f10])).
% 3.64/0.99  
% 3.64/0.99  cnf(c_9,plain,
% 3.64/0.99      ( ~ r2_hidden(X0,X1)
% 3.64/0.99      | ~ r2_hidden(X0,X2)
% 3.64/0.99      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.64/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_992,plain,
% 3.64/0.99      ( ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),X0)
% 3.64/0.99      | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(k2_xboole_0(sK2,X1),X0))
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,X1)) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_8751,plain,
% 3.64/0.99      ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)))
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK4))
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK3)) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_992]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_4,plain,
% 3.64/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 3.64/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_442,plain,
% 3.64/0.99      ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,X0))
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5871,plain,
% 3.64/0.99      ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK3))
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_442]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5868,plain,
% 3.64/0.99      ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK4))
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_442]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2,plain,
% 3.64/0.99      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.64/0.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.64/0.99      | r2_hidden(sK0(X0,X1,X2),X0)
% 3.64/0.99      | k2_xboole_0(X0,X1) = X2 ),
% 3.64/0.99      inference(cnf_transformation,[],[f21]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_12,negated_conjecture,
% 3.64/0.99      ( k2_xboole_0(sK2,k3_xboole_0(sK3,sK4)) != k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)) ),
% 3.64/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_4515,plain,
% 3.64/0.99      ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)))
% 3.64/0.99      | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(sK3,sK4))
% 3.64/0.99      | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_2,c_12]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_10,plain,
% 3.64/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.64/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_522,plain,
% 3.64/0.99      ( ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)))
% 3.64/0.99      | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK4)) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_11,plain,
% 3.64/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 3.64/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_525,plain,
% 3.64/0.99      ( ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)))
% 3.64/0.99      | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK3)) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5,plain,
% 3.64/0.99      ( r2_hidden(X0,X1)
% 3.64/0.99      | r2_hidden(X0,X2)
% 3.64/0.99      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.64/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3556,plain,
% 3.64/0.99      ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),X0)
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(X0,sK4))
% 3.64/0.99      | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK4) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3558,plain,
% 3.64/0.99      ( ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK4))
% 3.64/0.99      | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK4)
% 3.64/0.99      | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_3556]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3614,plain,
% 3.64/0.99      ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),X0)
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(X0,sK3))
% 3.64/0.99      | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK3) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3616,plain,
% 3.64/0.99      ( ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK3))
% 3.64/0.99      | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK3)
% 3.64/0.99      | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_3614]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_781,plain,
% 3.64/0.99      ( ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),X0)
% 3.64/0.99      | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(sK3,X0))
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK3) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3968,plain,
% 3.64/0.99      ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(sK3,sK4))
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK4)
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK3) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_781]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5423,plain,
% 3.64/0.99      ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(sK3,sK4))
% 3.64/0.99      | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
% 3.64/0.99      inference(global_propositional_subsumption,
% 3.64/0.99                [status(thm)],
% 3.64/0.99                [c_4515,c_522,c_525,c_3558,c_3616,c_3968]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5441,plain,
% 3.64/0.99      ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK3)
% 3.64/0.99      | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_5423,c_11]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5439,plain,
% 3.64/0.99      ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK4)
% 3.64/0.99      | r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2) ),
% 3.64/0.99      inference(resolution,[status(thm)],[c_5423,c_10]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3,plain,
% 3.64/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.64/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_768,plain,
% 3.64/0.99      ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(X0,sK3))
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK3) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_770,plain,
% 3.64/0.99      ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK3))
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK3) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_768]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_748,plain,
% 3.64/0.99      ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(X0,sK4))
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK4) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_750,plain,
% 3.64/0.99      ( r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k2_xboole_0(sK2,sK4))
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK4) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_748]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_0,plain,
% 3.64/0.99      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 3.64/0.99      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.64/0.99      | k2_xboole_0(X0,X1) = X2 ),
% 3.64/0.99      inference(cnf_transformation,[],[f23]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_499,plain,
% 3.64/0.99      ( ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)))
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(sK3,sK4))
% 3.64/0.99      | k2_xboole_0(sK2,k3_xboole_0(sK3,sK4)) = k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1,plain,
% 3.64/0.99      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.64/0.99      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 3.64/0.99      | k2_xboole_0(X0,X1) = X2 ),
% 3.64/0.99      inference(cnf_transformation,[],[f22]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_438,plain,
% 3.64/0.99      ( ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)))
% 3.64/0.99      | ~ r2_hidden(sK0(sK2,k3_xboole_0(sK3,sK4),k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4))),sK2)
% 3.64/0.99      | k2_xboole_0(sK2,k3_xboole_0(sK3,sK4)) = k3_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK4)) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(contradiction,plain,
% 3.64/0.99      ( $false ),
% 3.64/0.99      inference(minisat,
% 3.64/0.99                [status(thm)],
% 3.64/0.99                [c_8751,c_5871,c_5868,c_5441,c_5439,c_5423,c_770,c_750,
% 3.64/0.99                 c_499,c_438,c_12]) ).
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  ------                               Statistics
% 3.64/0.99  
% 3.64/0.99  ------ Selected
% 3.64/0.99  
% 3.64/0.99  total_time:                             0.277
% 3.64/0.99  
%------------------------------------------------------------------------------
