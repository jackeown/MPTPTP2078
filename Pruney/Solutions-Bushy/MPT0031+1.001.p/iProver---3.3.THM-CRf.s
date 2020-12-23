%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0031+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:17 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
