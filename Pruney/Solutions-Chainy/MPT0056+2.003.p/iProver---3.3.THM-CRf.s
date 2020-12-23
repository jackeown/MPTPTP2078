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
% DateTime   : Thu Dec  3 11:22:54 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 171 expanded)
%              Number of clauses        :   30 (  39 expanded)
%              Number of leaves         :    6 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  265 (1192 expanded)
%              Number of equality atoms :   39 ( 177 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2)
   => k3_xboole_0(sK2,k4_xboole_0(sK3,sK4)) != k4_xboole_0(k3_xboole_0(sK2,sK3),sK4) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k3_xboole_0(sK2,k4_xboole_0(sK3,sK4)) != k4_xboole_0(k3_xboole_0(sK2,sK3),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f5,f16])).

fof(f30,plain,(
    k3_xboole_0(sK2,k4_xboole_0(sK3,sK4)) != k4_xboole_0(k3_xboole_0(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f17])).

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

cnf(c_677,plain,
    ( ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),X0)
    | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),X1)
    | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2042,plain,
    ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),X0)
    | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k3_xboole_0(sK2,sK3),X0))
    | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_11602,plain,
    ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4))
    | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(sK2,sK3))
    | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_2042])).

cnf(c_624,plain,
    ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),X0)
    | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,X0))
    | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4275,plain,
    ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK4)
    | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_553,plain,
    ( ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),X0)
    | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(sK2,X0))
    | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3069,plain,
    ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK3)
    | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK2) ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_12,negated_conjecture,
    ( k3_xboole_0(sK2,k4_xboole_0(sK3,sK4)) != k4_xboole_0(k3_xboole_0(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2554,plain,
    ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4))
    | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK2) ),
    inference(resolution,[status(thm)],[c_2,c_12])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_592,plain,
    ( ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4))
    | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_731,plain,
    ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),X0)
    | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1798,plain,
    ( ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(sK2,sK3))
    | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK2) ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_3005,plain,
    ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2554,c_592,c_1798])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_788,plain,
    ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4))
    | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_1,c_12])).

cnf(c_1020,plain,
    ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
    | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_11,c_788])).

cnf(c_1499,plain,
    ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(sK2,sK3))
    | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK3) ),
    inference(resolution,[status(thm)],[c_1020,c_11])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1508,plain,
    ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1499,c_4])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1031,plain,
    ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK4) ),
    inference(resolution,[status(thm)],[c_10,c_788])).

cnf(c_1357,plain,
    ( ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1031,c_10])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_569,plain,
    ( ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4))
    | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
    | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK2)
    | k3_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = k4_xboole_0(k3_xboole_0(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11602,c_4275,c_3069,c_3005,c_1508,c_1357,c_569,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:15:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.28/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.03  
% 3.28/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.28/1.03  
% 3.28/1.03  ------  iProver source info
% 3.28/1.03  
% 3.28/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.28/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.28/1.03  git: non_committed_changes: false
% 3.28/1.03  git: last_make_outside_of_git: false
% 3.28/1.03  
% 3.28/1.03  ------ 
% 3.28/1.03  ------ Parsing...
% 3.28/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.28/1.03  
% 3.28/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.28/1.03  
% 3.28/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.28/1.03  
% 3.28/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.28/1.03  ------ Proving...
% 3.28/1.03  ------ Problem Properties 
% 3.28/1.03  
% 3.28/1.03  
% 3.28/1.03  clauses                                 13
% 3.28/1.03  conjectures                             1
% 3.28/1.03  EPR                                     0
% 3.28/1.03  Horn                                    7
% 3.28/1.03  unary                                   1
% 3.28/1.03  binary                                  4
% 3.28/1.03  lits                                    35
% 3.28/1.03  lits eq                                 7
% 3.28/1.03  fd_pure                                 0
% 3.28/1.03  fd_pseudo                               0
% 3.28/1.03  fd_cond                                 0
% 3.28/1.03  fd_pseudo_cond                          6
% 3.28/1.03  AC symbols                              0
% 3.28/1.03  
% 3.28/1.03  ------ Input Options Time Limit: Unbounded
% 3.28/1.03  
% 3.28/1.03  
% 3.28/1.03  ------ 
% 3.28/1.03  Current options:
% 3.28/1.03  ------ 
% 3.28/1.03  
% 3.28/1.03  
% 3.28/1.03  
% 3.28/1.03  
% 3.28/1.03  ------ Proving...
% 3.28/1.03  
% 3.28/1.03  
% 3.28/1.03  % SZS status Theorem for theBenchmark.p
% 3.28/1.03  
% 3.28/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.28/1.03  
% 3.28/1.03  fof(f2,axiom,(
% 3.28/1.03    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.28/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.03  
% 3.28/1.03  fof(f11,plain,(
% 3.28/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.28/1.03    inference(nnf_transformation,[],[f2])).
% 3.28/1.03  
% 3.28/1.03  fof(f12,plain,(
% 3.28/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.28/1.03    inference(flattening,[],[f11])).
% 3.28/1.03  
% 3.28/1.03  fof(f13,plain,(
% 3.28/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.28/1.03    inference(rectify,[],[f12])).
% 3.28/1.03  
% 3.28/1.03  fof(f14,plain,(
% 3.28/1.03    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.28/1.03    introduced(choice_axiom,[])).
% 3.28/1.03  
% 3.28/1.03  fof(f15,plain,(
% 3.28/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.28/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).
% 3.28/1.03  
% 3.28/1.03  fof(f26,plain,(
% 3.28/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.28/1.03    inference(cnf_transformation,[],[f15])).
% 3.28/1.03  
% 3.28/1.03  fof(f34,plain,(
% 3.28/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.28/1.03    inference(equality_resolution,[],[f26])).
% 3.28/1.03  
% 3.28/1.03  fof(f1,axiom,(
% 3.28/1.03    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.28/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.03  
% 3.28/1.03  fof(f6,plain,(
% 3.28/1.03    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.28/1.03    inference(nnf_transformation,[],[f1])).
% 3.28/1.03  
% 3.28/1.03  fof(f7,plain,(
% 3.28/1.03    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.28/1.03    inference(flattening,[],[f6])).
% 3.28/1.03  
% 3.28/1.03  fof(f8,plain,(
% 3.28/1.03    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.28/1.03    inference(rectify,[],[f7])).
% 3.28/1.03  
% 3.28/1.03  fof(f9,plain,(
% 3.28/1.03    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.28/1.03    introduced(choice_axiom,[])).
% 3.28/1.03  
% 3.28/1.03  fof(f10,plain,(
% 3.28/1.03    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.28/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).
% 3.28/1.03  
% 3.28/1.03  fof(f20,plain,(
% 3.28/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 3.28/1.03    inference(cnf_transformation,[],[f10])).
% 3.28/1.03  
% 3.28/1.03  fof(f31,plain,(
% 3.28/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.28/1.03    inference(equality_resolution,[],[f20])).
% 3.28/1.03  
% 3.28/1.03  fof(f21,plain,(
% 3.28/1.03    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.28/1.03    inference(cnf_transformation,[],[f10])).
% 3.28/1.03  
% 3.28/1.03  fof(f3,conjecture,(
% 3.28/1.03    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.28/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.28/1.03  
% 3.28/1.03  fof(f4,negated_conjecture,(
% 3.28/1.03    ~! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.28/1.03    inference(negated_conjecture,[],[f3])).
% 3.28/1.03  
% 3.28/1.03  fof(f5,plain,(
% 3.28/1.03    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.28/1.03    inference(ennf_transformation,[],[f4])).
% 3.28/1.03  
% 3.28/1.03  fof(f16,plain,(
% 3.28/1.03    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2) => k3_xboole_0(sK2,k4_xboole_0(sK3,sK4)) != k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),
% 3.28/1.03    introduced(choice_axiom,[])).
% 3.28/1.03  
% 3.28/1.03  fof(f17,plain,(
% 3.28/1.03    k3_xboole_0(sK2,k4_xboole_0(sK3,sK4)) != k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),
% 3.28/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f5,f16])).
% 3.28/1.03  
% 3.28/1.03  fof(f30,plain,(
% 3.28/1.03    k3_xboole_0(sK2,k4_xboole_0(sK3,sK4)) != k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),
% 3.28/1.03    inference(cnf_transformation,[],[f17])).
% 3.28/1.03  
% 3.28/1.03  fof(f24,plain,(
% 3.28/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.28/1.03    inference(cnf_transformation,[],[f15])).
% 3.28/1.03  
% 3.28/1.03  fof(f36,plain,(
% 3.28/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.28/1.03    inference(equality_resolution,[],[f24])).
% 3.28/1.03  
% 3.28/1.03  fof(f18,plain,(
% 3.28/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.28/1.03    inference(cnf_transformation,[],[f10])).
% 3.28/1.03  
% 3.28/1.03  fof(f33,plain,(
% 3.28/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.28/1.03    inference(equality_resolution,[],[f18])).
% 3.28/1.03  
% 3.28/1.03  fof(f22,plain,(
% 3.28/1.03    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.28/1.03    inference(cnf_transformation,[],[f10])).
% 3.28/1.03  
% 3.28/1.03  fof(f19,plain,(
% 3.28/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.28/1.03    inference(cnf_transformation,[],[f10])).
% 3.28/1.03  
% 3.28/1.03  fof(f32,plain,(
% 3.28/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.28/1.03    inference(equality_resolution,[],[f19])).
% 3.28/1.03  
% 3.28/1.03  fof(f25,plain,(
% 3.28/1.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.28/1.03    inference(cnf_transformation,[],[f15])).
% 3.28/1.03  
% 3.28/1.03  fof(f35,plain,(
% 3.28/1.03    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.28/1.03    inference(equality_resolution,[],[f25])).
% 3.28/1.03  
% 3.28/1.03  fof(f23,plain,(
% 3.28/1.03    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.28/1.03    inference(cnf_transformation,[],[f10])).
% 3.28/1.03  
% 3.28/1.03  cnf(c_9,plain,
% 3.28/1.03      ( ~ r2_hidden(X0,X1)
% 3.28/1.03      | r2_hidden(X0,X2)
% 3.28/1.03      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.28/1.03      inference(cnf_transformation,[],[f34]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_677,plain,
% 3.28/1.03      ( ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),X0)
% 3.28/1.03      | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),X1)
% 3.28/1.03      | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(X0,X1)) ),
% 3.28/1.03      inference(instantiation,[status(thm)],[c_9]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_2042,plain,
% 3.28/1.03      ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),X0)
% 3.28/1.03      | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k3_xboole_0(sK2,sK3),X0))
% 3.28/1.03      | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(sK2,sK3)) ),
% 3.28/1.03      inference(instantiation,[status(thm)],[c_677]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_11602,plain,
% 3.28/1.03      ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4))
% 3.28/1.03      | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(sK2,sK3))
% 3.28/1.03      | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK4) ),
% 3.28/1.03      inference(instantiation,[status(thm)],[c_2042]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_624,plain,
% 3.28/1.03      ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),X0)
% 3.28/1.03      | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,X0))
% 3.28/1.03      | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK3) ),
% 3.28/1.03      inference(instantiation,[status(thm)],[c_9]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_4275,plain,
% 3.28/1.03      ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
% 3.28/1.03      | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK4)
% 3.28/1.03      | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK3) ),
% 3.28/1.03      inference(instantiation,[status(thm)],[c_624]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_3,plain,
% 3.28/1.03      ( ~ r2_hidden(X0,X1)
% 3.28/1.03      | ~ r2_hidden(X0,X2)
% 3.28/1.03      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.28/1.03      inference(cnf_transformation,[],[f31]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_553,plain,
% 3.28/1.03      ( ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),X0)
% 3.28/1.03      | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(sK2,X0))
% 3.28/1.03      | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK2) ),
% 3.28/1.03      inference(instantiation,[status(thm)],[c_3]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_3069,plain,
% 3.28/1.03      ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(sK2,sK3))
% 3.28/1.03      | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK3)
% 3.28/1.03      | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK2) ),
% 3.28/1.03      inference(instantiation,[status(thm)],[c_553]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_2,plain,
% 3.28/1.03      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.28/1.03      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.28/1.03      | k3_xboole_0(X0,X1) = X2 ),
% 3.28/1.03      inference(cnf_transformation,[],[f21]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_12,negated_conjecture,
% 3.28/1.03      ( k3_xboole_0(sK2,k4_xboole_0(sK3,sK4)) != k4_xboole_0(k3_xboole_0(sK2,sK3),sK4) ),
% 3.28/1.03      inference(cnf_transformation,[],[f30]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_2554,plain,
% 3.28/1.03      ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4))
% 3.28/1.03      | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK2) ),
% 3.28/1.03      inference(resolution,[status(thm)],[c_2,c_12]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_11,plain,
% 3.28/1.03      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.28/1.03      inference(cnf_transformation,[],[f36]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_592,plain,
% 3.28/1.03      ( ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4))
% 3.28/1.03      | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(sK2,sK3)) ),
% 3.28/1.03      inference(instantiation,[status(thm)],[c_11]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_5,plain,
% 3.28/1.03      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 3.28/1.03      inference(cnf_transformation,[],[f33]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_731,plain,
% 3.28/1.03      ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),X0)
% 3.28/1.03      | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(X0,X1)) ),
% 3.28/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_1798,plain,
% 3.28/1.03      ( ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(sK2,sK3))
% 3.28/1.03      | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK2) ),
% 3.28/1.03      inference(instantiation,[status(thm)],[c_731]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_3005,plain,
% 3.28/1.03      ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK2) ),
% 3.28/1.03      inference(global_propositional_subsumption,
% 3.28/1.03                [status(thm)],
% 3.28/1.03                [c_2554,c_592,c_1798]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_1,plain,
% 3.28/1.03      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.28/1.03      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.28/1.03      | k3_xboole_0(X0,X1) = X2 ),
% 3.28/1.03      inference(cnf_transformation,[],[f22]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_788,plain,
% 3.28/1.03      ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4))
% 3.28/1.03      | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4)) ),
% 3.28/1.03      inference(resolution,[status(thm)],[c_1,c_12]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_1020,plain,
% 3.28/1.03      ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
% 3.28/1.03      | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(sK2,sK3)) ),
% 3.28/1.03      inference(resolution,[status(thm)],[c_11,c_788]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_1499,plain,
% 3.28/1.03      ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k3_xboole_0(sK2,sK3))
% 3.28/1.03      | r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK3) ),
% 3.28/1.03      inference(resolution,[status(thm)],[c_1020,c_11]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_4,plain,
% 3.28/1.03      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.28/1.03      inference(cnf_transformation,[],[f32]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_1508,plain,
% 3.28/1.03      ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK3) ),
% 3.28/1.03      inference(forward_subsumption_resolution,
% 3.28/1.03                [status(thm)],
% 3.28/1.03                [c_1499,c_4]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_10,plain,
% 3.28/1.03      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.28/1.03      inference(cnf_transformation,[],[f35]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_1031,plain,
% 3.28/1.03      ( r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
% 3.28/1.03      | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK4) ),
% 3.28/1.03      inference(resolution,[status(thm)],[c_10,c_788]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_1357,plain,
% 3.28/1.03      ( ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK4) ),
% 3.28/1.03      inference(forward_subsumption_resolution,
% 3.28/1.03                [status(thm)],
% 3.28/1.03                [c_1031,c_10]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_0,plain,
% 3.28/1.03      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 3.28/1.03      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 3.28/1.03      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.28/1.03      | k3_xboole_0(X0,X1) = X2 ),
% 3.28/1.03      inference(cnf_transformation,[],[f23]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(c_569,plain,
% 3.28/1.03      ( ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4))
% 3.28/1.03      | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),k4_xboole_0(sK3,sK4))
% 3.28/1.03      | ~ r2_hidden(sK0(sK2,k4_xboole_0(sK3,sK4),k4_xboole_0(k3_xboole_0(sK2,sK3),sK4)),sK2)
% 3.28/1.03      | k3_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = k4_xboole_0(k3_xboole_0(sK2,sK3),sK4) ),
% 3.28/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 3.28/1.03  
% 3.28/1.03  cnf(contradiction,plain,
% 3.28/1.03      ( $false ),
% 3.28/1.03      inference(minisat,
% 3.28/1.03                [status(thm)],
% 3.28/1.03                [c_11602,c_4275,c_3069,c_3005,c_1508,c_1357,c_569,c_12]) ).
% 3.28/1.03  
% 3.28/1.03  
% 3.28/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.28/1.03  
% 3.28/1.03  ------                               Statistics
% 3.28/1.03  
% 3.28/1.03  ------ Selected
% 3.28/1.03  
% 3.28/1.03  total_time:                             0.419
% 3.28/1.03  
%------------------------------------------------------------------------------
