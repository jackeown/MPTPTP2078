%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0055+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:21 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   47 (  90 expanded)
%              Number of clauses        :   20 (  23 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :  229 ( 681 expanded)
%              Number of equality atoms :   38 (  94 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK2,sK3) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k3_xboole_0(sK2,sK3) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f5,f16])).

fof(f30,plain,(
    k3_xboole_0(sK2,sK3) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_482,plain,
    ( r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),X0)
    | r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK2,X0))
    | ~ r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1394,plain,
    ( r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(X0,X1))
    | r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK2,k4_xboole_0(X0,X1)))
    | ~ r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_3498,plain,
    ( r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_1394])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_608,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),X0)
    | ~ r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1389,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_656,plain,
    ( r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK2,sK3))
    | r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),sK3)
    | ~ r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_519,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_458,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(X0,sK3))
    | ~ r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_460,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_452,plain,
    ( ~ r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),sK3)
    | ~ r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),sK2)
    | k3_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_449,plain,
    ( r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),sK2)
    | k3_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_446,plain,
    ( r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(sK2,sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),sK3)
    | k3_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_12,negated_conjecture,
    ( k3_xboole_0(sK2,sK3) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3498,c_1389,c_656,c_519,c_460,c_452,c_449,c_446,c_12])).


%------------------------------------------------------------------------------
