%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:22 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 162 expanded)
%              Number of clauses        :   38 (  45 expanded)
%              Number of leaves         :    7 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  244 (1048 expanded)
%              Number of equality atoms :   34 ( 135 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f34])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f18,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f25])).

fof(f47,plain,(
    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,(
    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
    inference(definition_unfolding,[],[f47,f34,f42])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_563,plain,
    ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),X0)
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,X0))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7304,plain,
    ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,sK2))
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK2)
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_735,plain,
    ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),X0)
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2041,plain,
    ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,sK2))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(k4_xboole_0(X0,sK2),X1)) ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_5911,plain,
    ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,sK2))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X1,sK1))) ),
    inference(instantiation,[status(thm)],[c_2041])).

cnf(c_5917,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK1)))
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5911])).

cnf(c_720,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),X0)
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),X1)
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2299,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),X0)
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,k4_xboole_0(X1,sK1)))
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X1,sK1)) ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_5910,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,sK2))
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X1,sK1))
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X1,sK1))) ),
    inference(instantiation,[status(thm)],[c_2299])).

cnf(c_5913,plain,
    ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK1)))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,sK2))
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_5910])).

cnf(c_4187,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_721,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),X0)
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2407,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1038,plain,
    ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,sK2))
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,k4_xboole_0(X0,sK2)))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_1041,plain,
    ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_560,plain,
    ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),X0)
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k2_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(X0,sK1)))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1019,plain,
    ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_559,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),X0)
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k2_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(X0,sK1)))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_832,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_626,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,sK2))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_628,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK2) ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_564,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,sK1))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_566,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,sK1))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_556,plain,
    ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)))
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_523,plain,
    ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)))
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK2)
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1)
    | k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_520,plain,
    ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)))
    | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1)
    | k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_517,plain,
    ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)))
    | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK2)
    | k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_18,negated_conjecture,
    ( k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7304,c_5917,c_5913,c_4187,c_2407,c_1041,c_1019,c_832,c_628,c_566,c_556,c_523,c_520,c_517,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:57:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.73/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.01  
% 2.73/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.73/1.01  
% 2.73/1.01  ------  iProver source info
% 2.73/1.01  
% 2.73/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.73/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.73/1.01  git: non_committed_changes: false
% 2.73/1.01  git: last_make_outside_of_git: false
% 2.73/1.01  
% 2.73/1.01  ------ 
% 2.73/1.01  
% 2.73/1.01  ------ Input Options
% 2.73/1.01  
% 2.73/1.01  --out_options                           all
% 2.73/1.01  --tptp_safe_out                         true
% 2.73/1.01  --problem_path                          ""
% 2.73/1.01  --include_path                          ""
% 2.73/1.01  --clausifier                            res/vclausify_rel
% 2.73/1.01  --clausifier_options                    --mode clausify
% 2.73/1.01  --stdin                                 false
% 2.73/1.01  --stats_out                             all
% 2.73/1.01  
% 2.73/1.01  ------ General Options
% 2.73/1.01  
% 2.73/1.01  --fof                                   false
% 2.73/1.01  --time_out_real                         305.
% 2.73/1.01  --time_out_virtual                      -1.
% 2.73/1.01  --symbol_type_check                     false
% 2.73/1.01  --clausify_out                          false
% 2.73/1.01  --sig_cnt_out                           false
% 2.73/1.01  --trig_cnt_out                          false
% 2.73/1.01  --trig_cnt_out_tolerance                1.
% 2.73/1.01  --trig_cnt_out_sk_spl                   false
% 2.73/1.01  --abstr_cl_out                          false
% 2.73/1.01  
% 2.73/1.01  ------ Global Options
% 2.73/1.01  
% 2.73/1.01  --schedule                              default
% 2.73/1.01  --add_important_lit                     false
% 2.73/1.01  --prop_solver_per_cl                    1000
% 2.73/1.01  --min_unsat_core                        false
% 2.73/1.01  --soft_assumptions                      false
% 2.73/1.01  --soft_lemma_size                       3
% 2.73/1.01  --prop_impl_unit_size                   0
% 2.73/1.01  --prop_impl_unit                        []
% 2.73/1.01  --share_sel_clauses                     true
% 2.73/1.01  --reset_solvers                         false
% 2.73/1.01  --bc_imp_inh                            [conj_cone]
% 2.73/1.01  --conj_cone_tolerance                   3.
% 2.73/1.01  --extra_neg_conj                        none
% 2.73/1.01  --large_theory_mode                     true
% 2.73/1.01  --prolific_symb_bound                   200
% 2.73/1.01  --lt_threshold                          2000
% 2.73/1.01  --clause_weak_htbl                      true
% 2.73/1.01  --gc_record_bc_elim                     false
% 2.73/1.01  
% 2.73/1.01  ------ Preprocessing Options
% 2.73/1.01  
% 2.73/1.01  --preprocessing_flag                    true
% 2.73/1.01  --time_out_prep_mult                    0.1
% 2.73/1.01  --splitting_mode                        input
% 2.73/1.01  --splitting_grd                         true
% 2.73/1.01  --splitting_cvd                         false
% 2.73/1.01  --splitting_cvd_svl                     false
% 2.73/1.01  --splitting_nvd                         32
% 2.73/1.01  --sub_typing                            true
% 2.73/1.01  --prep_gs_sim                           true
% 2.73/1.01  --prep_unflatten                        true
% 2.73/1.01  --prep_res_sim                          true
% 2.73/1.01  --prep_upred                            true
% 2.73/1.01  --prep_sem_filter                       exhaustive
% 2.73/1.01  --prep_sem_filter_out                   false
% 2.73/1.01  --pred_elim                             true
% 2.73/1.01  --res_sim_input                         true
% 2.73/1.01  --eq_ax_congr_red                       true
% 2.73/1.01  --pure_diseq_elim                       true
% 2.73/1.01  --brand_transform                       false
% 2.73/1.01  --non_eq_to_eq                          false
% 2.73/1.01  --prep_def_merge                        true
% 2.73/1.01  --prep_def_merge_prop_impl              false
% 2.73/1.01  --prep_def_merge_mbd                    true
% 2.73/1.01  --prep_def_merge_tr_red                 false
% 2.73/1.01  --prep_def_merge_tr_cl                  false
% 2.73/1.01  --smt_preprocessing                     true
% 2.73/1.01  --smt_ac_axioms                         fast
% 2.73/1.01  --preprocessed_out                      false
% 2.73/1.01  --preprocessed_stats                    false
% 2.73/1.01  
% 2.73/1.01  ------ Abstraction refinement Options
% 2.73/1.01  
% 2.73/1.01  --abstr_ref                             []
% 2.73/1.01  --abstr_ref_prep                        false
% 2.73/1.01  --abstr_ref_until_sat                   false
% 2.73/1.01  --abstr_ref_sig_restrict                funpre
% 2.73/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/1.01  --abstr_ref_under                       []
% 2.73/1.01  
% 2.73/1.01  ------ SAT Options
% 2.73/1.01  
% 2.73/1.01  --sat_mode                              false
% 2.73/1.01  --sat_fm_restart_options                ""
% 2.73/1.01  --sat_gr_def                            false
% 2.73/1.01  --sat_epr_types                         true
% 2.73/1.01  --sat_non_cyclic_types                  false
% 2.73/1.01  --sat_finite_models                     false
% 2.73/1.01  --sat_fm_lemmas                         false
% 2.73/1.01  --sat_fm_prep                           false
% 2.73/1.01  --sat_fm_uc_incr                        true
% 2.73/1.01  --sat_out_model                         small
% 2.73/1.01  --sat_out_clauses                       false
% 2.73/1.01  
% 2.73/1.01  ------ QBF Options
% 2.73/1.01  
% 2.73/1.01  --qbf_mode                              false
% 2.73/1.01  --qbf_elim_univ                         false
% 2.73/1.01  --qbf_dom_inst                          none
% 2.73/1.01  --qbf_dom_pre_inst                      false
% 2.73/1.01  --qbf_sk_in                             false
% 2.73/1.01  --qbf_pred_elim                         true
% 2.73/1.01  --qbf_split                             512
% 2.73/1.01  
% 2.73/1.01  ------ BMC1 Options
% 2.73/1.01  
% 2.73/1.01  --bmc1_incremental                      false
% 2.73/1.01  --bmc1_axioms                           reachable_all
% 2.73/1.01  --bmc1_min_bound                        0
% 2.73/1.01  --bmc1_max_bound                        -1
% 2.73/1.01  --bmc1_max_bound_default                -1
% 2.73/1.01  --bmc1_symbol_reachability              true
% 2.73/1.01  --bmc1_property_lemmas                  false
% 2.73/1.01  --bmc1_k_induction                      false
% 2.73/1.01  --bmc1_non_equiv_states                 false
% 2.73/1.01  --bmc1_deadlock                         false
% 2.73/1.01  --bmc1_ucm                              false
% 2.73/1.01  --bmc1_add_unsat_core                   none
% 2.73/1.01  --bmc1_unsat_core_children              false
% 2.73/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/1.01  --bmc1_out_stat                         full
% 2.73/1.01  --bmc1_ground_init                      false
% 2.73/1.01  --bmc1_pre_inst_next_state              false
% 2.73/1.01  --bmc1_pre_inst_state                   false
% 2.73/1.01  --bmc1_pre_inst_reach_state             false
% 2.73/1.01  --bmc1_out_unsat_core                   false
% 2.73/1.01  --bmc1_aig_witness_out                  false
% 2.73/1.01  --bmc1_verbose                          false
% 2.73/1.01  --bmc1_dump_clauses_tptp                false
% 2.73/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.73/1.01  --bmc1_dump_file                        -
% 2.73/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.73/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.73/1.01  --bmc1_ucm_extend_mode                  1
% 2.73/1.01  --bmc1_ucm_init_mode                    2
% 2.73/1.01  --bmc1_ucm_cone_mode                    none
% 2.73/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.73/1.01  --bmc1_ucm_relax_model                  4
% 2.73/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.73/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/1.01  --bmc1_ucm_layered_model                none
% 2.73/1.01  --bmc1_ucm_max_lemma_size               10
% 2.73/1.01  
% 2.73/1.01  ------ AIG Options
% 2.73/1.01  
% 2.73/1.01  --aig_mode                              false
% 2.73/1.01  
% 2.73/1.01  ------ Instantiation Options
% 2.73/1.01  
% 2.73/1.01  --instantiation_flag                    true
% 2.73/1.01  --inst_sos_flag                         false
% 2.73/1.01  --inst_sos_phase                        true
% 2.73/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/1.01  --inst_lit_sel_side                     num_symb
% 2.73/1.01  --inst_solver_per_active                1400
% 2.73/1.01  --inst_solver_calls_frac                1.
% 2.73/1.01  --inst_passive_queue_type               priority_queues
% 2.73/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/1.01  --inst_passive_queues_freq              [25;2]
% 2.73/1.01  --inst_dismatching                      true
% 2.73/1.01  --inst_eager_unprocessed_to_passive     true
% 2.73/1.01  --inst_prop_sim_given                   true
% 2.73/1.01  --inst_prop_sim_new                     false
% 2.73/1.01  --inst_subs_new                         false
% 2.73/1.01  --inst_eq_res_simp                      false
% 2.73/1.01  --inst_subs_given                       false
% 2.73/1.01  --inst_orphan_elimination               true
% 2.73/1.01  --inst_learning_loop_flag               true
% 2.73/1.01  --inst_learning_start                   3000
% 2.73/1.01  --inst_learning_factor                  2
% 2.73/1.01  --inst_start_prop_sim_after_learn       3
% 2.73/1.01  --inst_sel_renew                        solver
% 2.73/1.01  --inst_lit_activity_flag                true
% 2.73/1.01  --inst_restr_to_given                   false
% 2.73/1.01  --inst_activity_threshold               500
% 2.73/1.01  --inst_out_proof                        true
% 2.73/1.01  
% 2.73/1.01  ------ Resolution Options
% 2.73/1.01  
% 2.73/1.01  --resolution_flag                       true
% 2.73/1.01  --res_lit_sel                           adaptive
% 2.73/1.01  --res_lit_sel_side                      none
% 2.73/1.01  --res_ordering                          kbo
% 2.73/1.01  --res_to_prop_solver                    active
% 2.73/1.01  --res_prop_simpl_new                    false
% 2.73/1.01  --res_prop_simpl_given                  true
% 2.73/1.01  --res_passive_queue_type                priority_queues
% 2.73/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/1.01  --res_passive_queues_freq               [15;5]
% 2.73/1.01  --res_forward_subs                      full
% 2.73/1.01  --res_backward_subs                     full
% 2.73/1.01  --res_forward_subs_resolution           true
% 2.73/1.01  --res_backward_subs_resolution          true
% 2.73/1.01  --res_orphan_elimination                true
% 2.73/1.01  --res_time_limit                        2.
% 2.73/1.01  --res_out_proof                         true
% 2.73/1.01  
% 2.73/1.01  ------ Superposition Options
% 2.73/1.01  
% 2.73/1.01  --superposition_flag                    true
% 2.73/1.01  --sup_passive_queue_type                priority_queues
% 2.73/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.73/1.01  --demod_completeness_check              fast
% 2.73/1.01  --demod_use_ground                      true
% 2.73/1.01  --sup_to_prop_solver                    passive
% 2.73/1.01  --sup_prop_simpl_new                    true
% 2.73/1.01  --sup_prop_simpl_given                  true
% 2.73/1.01  --sup_fun_splitting                     false
% 2.73/1.01  --sup_smt_interval                      50000
% 2.73/1.01  
% 2.73/1.01  ------ Superposition Simplification Setup
% 2.73/1.01  
% 2.73/1.01  --sup_indices_passive                   []
% 2.73/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.01  --sup_full_bw                           [BwDemod]
% 2.73/1.01  --sup_immed_triv                        [TrivRules]
% 2.73/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.01  --sup_immed_bw_main                     []
% 2.73/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.01  
% 2.73/1.01  ------ Combination Options
% 2.73/1.01  
% 2.73/1.01  --comb_res_mult                         3
% 2.73/1.01  --comb_sup_mult                         2
% 2.73/1.01  --comb_inst_mult                        10
% 2.73/1.01  
% 2.73/1.01  ------ Debug Options
% 2.73/1.01  
% 2.73/1.01  --dbg_backtrace                         false
% 2.73/1.01  --dbg_dump_prop_clauses                 false
% 2.73/1.01  --dbg_dump_prop_clauses_file            -
% 2.73/1.01  --dbg_out_stat                          false
% 2.73/1.01  ------ Parsing...
% 2.73/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.73/1.01  
% 2.73/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.73/1.01  
% 2.73/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.73/1.01  
% 2.73/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.73/1.01  ------ Proving...
% 2.73/1.01  ------ Problem Properties 
% 2.73/1.01  
% 2.73/1.01  
% 2.73/1.01  clauses                                 18
% 2.73/1.01  conjectures                             1
% 2.73/1.01  EPR                                     0
% 2.73/1.01  Horn                                    11
% 2.73/1.01  unary                                   8
% 2.73/1.01  binary                                  2
% 2.73/1.01  lits                                    37
% 2.73/1.01  lits eq                                 11
% 2.73/1.01  fd_pure                                 0
% 2.73/1.01  fd_pseudo                               0
% 2.73/1.01  fd_cond                                 0
% 2.73/1.01  fd_pseudo_cond                          3
% 2.73/1.01  AC symbols                              0
% 2.73/1.01  
% 2.73/1.01  ------ Schedule dynamic 5 is on 
% 2.73/1.01  
% 2.73/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.73/1.01  
% 2.73/1.01  
% 2.73/1.01  ------ 
% 2.73/1.01  Current options:
% 2.73/1.01  ------ 
% 2.73/1.01  
% 2.73/1.01  ------ Input Options
% 2.73/1.01  
% 2.73/1.01  --out_options                           all
% 2.73/1.01  --tptp_safe_out                         true
% 2.73/1.01  --problem_path                          ""
% 2.73/1.01  --include_path                          ""
% 2.73/1.01  --clausifier                            res/vclausify_rel
% 2.73/1.01  --clausifier_options                    --mode clausify
% 2.73/1.01  --stdin                                 false
% 2.73/1.01  --stats_out                             all
% 2.73/1.01  
% 2.73/1.01  ------ General Options
% 2.73/1.01  
% 2.73/1.01  --fof                                   false
% 2.73/1.01  --time_out_real                         305.
% 2.73/1.01  --time_out_virtual                      -1.
% 2.73/1.01  --symbol_type_check                     false
% 2.73/1.01  --clausify_out                          false
% 2.73/1.01  --sig_cnt_out                           false
% 2.73/1.01  --trig_cnt_out                          false
% 2.73/1.01  --trig_cnt_out_tolerance                1.
% 2.73/1.01  --trig_cnt_out_sk_spl                   false
% 2.73/1.01  --abstr_cl_out                          false
% 2.73/1.01  
% 2.73/1.01  ------ Global Options
% 2.73/1.01  
% 2.73/1.01  --schedule                              default
% 2.73/1.01  --add_important_lit                     false
% 2.73/1.01  --prop_solver_per_cl                    1000
% 2.73/1.01  --min_unsat_core                        false
% 2.73/1.01  --soft_assumptions                      false
% 2.73/1.01  --soft_lemma_size                       3
% 2.73/1.01  --prop_impl_unit_size                   0
% 2.73/1.01  --prop_impl_unit                        []
% 2.73/1.01  --share_sel_clauses                     true
% 2.73/1.01  --reset_solvers                         false
% 2.73/1.01  --bc_imp_inh                            [conj_cone]
% 2.73/1.01  --conj_cone_tolerance                   3.
% 2.73/1.01  --extra_neg_conj                        none
% 2.73/1.01  --large_theory_mode                     true
% 2.73/1.01  --prolific_symb_bound                   200
% 2.73/1.01  --lt_threshold                          2000
% 2.73/1.01  --clause_weak_htbl                      true
% 2.73/1.01  --gc_record_bc_elim                     false
% 2.73/1.01  
% 2.73/1.01  ------ Preprocessing Options
% 2.73/1.01  
% 2.73/1.01  --preprocessing_flag                    true
% 2.73/1.01  --time_out_prep_mult                    0.1
% 2.73/1.01  --splitting_mode                        input
% 2.73/1.01  --splitting_grd                         true
% 2.73/1.01  --splitting_cvd                         false
% 2.73/1.01  --splitting_cvd_svl                     false
% 2.73/1.01  --splitting_nvd                         32
% 2.73/1.01  --sub_typing                            true
% 2.73/1.01  --prep_gs_sim                           true
% 2.73/1.01  --prep_unflatten                        true
% 2.73/1.01  --prep_res_sim                          true
% 2.73/1.01  --prep_upred                            true
% 2.73/1.01  --prep_sem_filter                       exhaustive
% 2.73/1.01  --prep_sem_filter_out                   false
% 2.73/1.01  --pred_elim                             true
% 2.73/1.01  --res_sim_input                         true
% 2.73/1.01  --eq_ax_congr_red                       true
% 2.73/1.01  --pure_diseq_elim                       true
% 2.73/1.01  --brand_transform                       false
% 2.73/1.01  --non_eq_to_eq                          false
% 2.73/1.01  --prep_def_merge                        true
% 2.73/1.01  --prep_def_merge_prop_impl              false
% 2.73/1.01  --prep_def_merge_mbd                    true
% 2.73/1.01  --prep_def_merge_tr_red                 false
% 2.73/1.01  --prep_def_merge_tr_cl                  false
% 2.73/1.01  --smt_preprocessing                     true
% 2.73/1.01  --smt_ac_axioms                         fast
% 2.73/1.01  --preprocessed_out                      false
% 2.73/1.01  --preprocessed_stats                    false
% 2.73/1.01  
% 2.73/1.01  ------ Abstraction refinement Options
% 2.73/1.01  
% 2.73/1.01  --abstr_ref                             []
% 2.73/1.01  --abstr_ref_prep                        false
% 2.73/1.01  --abstr_ref_until_sat                   false
% 2.73/1.01  --abstr_ref_sig_restrict                funpre
% 2.73/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/1.01  --abstr_ref_under                       []
% 2.73/1.01  
% 2.73/1.01  ------ SAT Options
% 2.73/1.01  
% 2.73/1.01  --sat_mode                              false
% 2.73/1.01  --sat_fm_restart_options                ""
% 2.73/1.01  --sat_gr_def                            false
% 2.73/1.01  --sat_epr_types                         true
% 2.73/1.01  --sat_non_cyclic_types                  false
% 2.73/1.01  --sat_finite_models                     false
% 2.73/1.01  --sat_fm_lemmas                         false
% 2.73/1.01  --sat_fm_prep                           false
% 2.73/1.01  --sat_fm_uc_incr                        true
% 2.73/1.01  --sat_out_model                         small
% 2.73/1.01  --sat_out_clauses                       false
% 2.73/1.01  
% 2.73/1.01  ------ QBF Options
% 2.73/1.01  
% 2.73/1.01  --qbf_mode                              false
% 2.73/1.01  --qbf_elim_univ                         false
% 2.73/1.01  --qbf_dom_inst                          none
% 2.73/1.01  --qbf_dom_pre_inst                      false
% 2.73/1.01  --qbf_sk_in                             false
% 2.73/1.01  --qbf_pred_elim                         true
% 2.73/1.01  --qbf_split                             512
% 2.73/1.01  
% 2.73/1.01  ------ BMC1 Options
% 2.73/1.01  
% 2.73/1.01  --bmc1_incremental                      false
% 2.73/1.01  --bmc1_axioms                           reachable_all
% 2.73/1.01  --bmc1_min_bound                        0
% 2.73/1.01  --bmc1_max_bound                        -1
% 2.73/1.01  --bmc1_max_bound_default                -1
% 2.73/1.01  --bmc1_symbol_reachability              true
% 2.73/1.01  --bmc1_property_lemmas                  false
% 2.73/1.01  --bmc1_k_induction                      false
% 2.73/1.01  --bmc1_non_equiv_states                 false
% 2.73/1.01  --bmc1_deadlock                         false
% 2.73/1.01  --bmc1_ucm                              false
% 2.73/1.01  --bmc1_add_unsat_core                   none
% 2.73/1.01  --bmc1_unsat_core_children              false
% 2.73/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/1.01  --bmc1_out_stat                         full
% 2.73/1.01  --bmc1_ground_init                      false
% 2.73/1.01  --bmc1_pre_inst_next_state              false
% 2.73/1.01  --bmc1_pre_inst_state                   false
% 2.73/1.01  --bmc1_pre_inst_reach_state             false
% 2.73/1.01  --bmc1_out_unsat_core                   false
% 2.73/1.01  --bmc1_aig_witness_out                  false
% 2.73/1.01  --bmc1_verbose                          false
% 2.73/1.01  --bmc1_dump_clauses_tptp                false
% 2.73/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.73/1.01  --bmc1_dump_file                        -
% 2.73/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.73/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.73/1.01  --bmc1_ucm_extend_mode                  1
% 2.73/1.01  --bmc1_ucm_init_mode                    2
% 2.73/1.01  --bmc1_ucm_cone_mode                    none
% 2.73/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.73/1.01  --bmc1_ucm_relax_model                  4
% 2.73/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.73/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/1.01  --bmc1_ucm_layered_model                none
% 2.73/1.01  --bmc1_ucm_max_lemma_size               10
% 2.73/1.01  
% 2.73/1.01  ------ AIG Options
% 2.73/1.01  
% 2.73/1.01  --aig_mode                              false
% 2.73/1.01  
% 2.73/1.01  ------ Instantiation Options
% 2.73/1.01  
% 2.73/1.01  --instantiation_flag                    true
% 2.73/1.01  --inst_sos_flag                         false
% 2.73/1.01  --inst_sos_phase                        true
% 2.73/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/1.01  --inst_lit_sel_side                     none
% 2.73/1.01  --inst_solver_per_active                1400
% 2.73/1.01  --inst_solver_calls_frac                1.
% 2.73/1.01  --inst_passive_queue_type               priority_queues
% 2.73/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/1.01  --inst_passive_queues_freq              [25;2]
% 2.73/1.01  --inst_dismatching                      true
% 2.73/1.01  --inst_eager_unprocessed_to_passive     true
% 2.73/1.01  --inst_prop_sim_given                   true
% 2.73/1.01  --inst_prop_sim_new                     false
% 2.73/1.01  --inst_subs_new                         false
% 2.73/1.01  --inst_eq_res_simp                      false
% 2.73/1.01  --inst_subs_given                       false
% 2.73/1.01  --inst_orphan_elimination               true
% 2.73/1.01  --inst_learning_loop_flag               true
% 2.73/1.01  --inst_learning_start                   3000
% 2.73/1.01  --inst_learning_factor                  2
% 2.73/1.01  --inst_start_prop_sim_after_learn       3
% 2.73/1.01  --inst_sel_renew                        solver
% 2.73/1.01  --inst_lit_activity_flag                true
% 2.73/1.01  --inst_restr_to_given                   false
% 2.73/1.01  --inst_activity_threshold               500
% 2.73/1.01  --inst_out_proof                        true
% 2.73/1.01  
% 2.73/1.01  ------ Resolution Options
% 2.73/1.01  
% 2.73/1.01  --resolution_flag                       false
% 2.73/1.01  --res_lit_sel                           adaptive
% 2.73/1.01  --res_lit_sel_side                      none
% 2.73/1.01  --res_ordering                          kbo
% 2.73/1.01  --res_to_prop_solver                    active
% 2.73/1.01  --res_prop_simpl_new                    false
% 2.73/1.01  --res_prop_simpl_given                  true
% 2.73/1.01  --res_passive_queue_type                priority_queues
% 2.73/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/1.01  --res_passive_queues_freq               [15;5]
% 2.73/1.01  --res_forward_subs                      full
% 2.73/1.01  --res_backward_subs                     full
% 2.73/1.01  --res_forward_subs_resolution           true
% 2.73/1.01  --res_backward_subs_resolution          true
% 2.73/1.01  --res_orphan_elimination                true
% 2.73/1.01  --res_time_limit                        2.
% 2.73/1.01  --res_out_proof                         true
% 2.73/1.01  
% 2.73/1.01  ------ Superposition Options
% 2.73/1.01  
% 2.73/1.01  --superposition_flag                    true
% 2.73/1.01  --sup_passive_queue_type                priority_queues
% 2.73/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.73/1.01  --demod_completeness_check              fast
% 2.73/1.01  --demod_use_ground                      true
% 2.73/1.01  --sup_to_prop_solver                    passive
% 2.73/1.01  --sup_prop_simpl_new                    true
% 2.73/1.01  --sup_prop_simpl_given                  true
% 2.73/1.01  --sup_fun_splitting                     false
% 2.73/1.01  --sup_smt_interval                      50000
% 2.73/1.01  
% 2.73/1.01  ------ Superposition Simplification Setup
% 2.73/1.01  
% 2.73/1.01  --sup_indices_passive                   []
% 2.73/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.01  --sup_full_bw                           [BwDemod]
% 2.73/1.01  --sup_immed_triv                        [TrivRules]
% 2.73/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.01  --sup_immed_bw_main                     []
% 2.73/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.01  
% 2.73/1.01  ------ Combination Options
% 2.73/1.01  
% 2.73/1.01  --comb_res_mult                         3
% 2.73/1.01  --comb_sup_mult                         2
% 2.73/1.01  --comb_inst_mult                        10
% 2.73/1.01  
% 2.73/1.01  ------ Debug Options
% 2.73/1.01  
% 2.73/1.01  --dbg_backtrace                         false
% 2.73/1.01  --dbg_dump_prop_clauses                 false
% 2.73/1.01  --dbg_dump_prop_clauses_file            -
% 2.73/1.01  --dbg_out_stat                          false
% 2.73/1.01  
% 2.73/1.01  
% 2.73/1.01  
% 2.73/1.01  
% 2.73/1.01  ------ Proving...
% 2.73/1.01  
% 2.73/1.01  
% 2.73/1.01  % SZS status Theorem for theBenchmark.p
% 2.73/1.01  
% 2.73/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.73/1.01  
% 2.73/1.01  fof(f2,axiom,(
% 2.73/1.01    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f19,plain,(
% 2.73/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.73/1.01    inference(nnf_transformation,[],[f2])).
% 2.73/1.01  
% 2.73/1.01  fof(f20,plain,(
% 2.73/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.73/1.01    inference(flattening,[],[f19])).
% 2.73/1.01  
% 2.73/1.01  fof(f21,plain,(
% 2.73/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.73/1.01    inference(rectify,[],[f20])).
% 2.73/1.01  
% 2.73/1.01  fof(f22,plain,(
% 2.73/1.01    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.73/1.01    introduced(choice_axiom,[])).
% 2.73/1.01  
% 2.73/1.01  fof(f23,plain,(
% 2.73/1.01    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.73/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 2.73/1.01  
% 2.73/1.01  fof(f30,plain,(
% 2.73/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.73/1.01    inference(cnf_transformation,[],[f23])).
% 2.73/1.01  
% 2.73/1.01  fof(f58,plain,(
% 2.73/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.73/1.01    inference(equality_resolution,[],[f30])).
% 2.73/1.01  
% 2.73/1.01  fof(f28,plain,(
% 2.73/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.73/1.01    inference(cnf_transformation,[],[f23])).
% 2.73/1.01  
% 2.73/1.01  fof(f60,plain,(
% 2.73/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.73/1.01    inference(equality_resolution,[],[f28])).
% 2.73/1.01  
% 2.73/1.01  fof(f29,plain,(
% 2.73/1.01    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.73/1.01    inference(cnf_transformation,[],[f23])).
% 2.73/1.01  
% 2.73/1.01  fof(f59,plain,(
% 2.73/1.01    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.73/1.01    inference(equality_resolution,[],[f29])).
% 2.73/1.01  
% 2.73/1.01  fof(f4,axiom,(
% 2.73/1.01    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f16,plain,(
% 2.73/1.01    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.73/1.01    inference(ennf_transformation,[],[f4])).
% 2.73/1.01  
% 2.73/1.01  fof(f24,plain,(
% 2.73/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.73/1.01    inference(nnf_transformation,[],[f16])).
% 2.73/1.01  
% 2.73/1.01  fof(f37,plain,(
% 2.73/1.01    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f24])).
% 2.73/1.01  
% 2.73/1.01  fof(f3,axiom,(
% 2.73/1.01    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f34,plain,(
% 2.73/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 2.73/1.01    inference(cnf_transformation,[],[f3])).
% 2.73/1.01  
% 2.73/1.01  fof(f51,plain,(
% 2.73/1.01    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 2.73/1.01    inference(definition_unfolding,[],[f37,f34])).
% 2.73/1.01  
% 2.73/1.01  fof(f36,plain,(
% 2.73/1.01    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 2.73/1.01    inference(cnf_transformation,[],[f24])).
% 2.73/1.01  
% 2.73/1.01  fof(f52,plain,(
% 2.73/1.01    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))) )),
% 2.73/1.01    inference(definition_unfolding,[],[f36,f34])).
% 2.73/1.01  
% 2.73/1.01  fof(f35,plain,(
% 2.73/1.01    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 2.73/1.01    inference(cnf_transformation,[],[f24])).
% 2.73/1.01  
% 2.73/1.01  fof(f53,plain,(
% 2.73/1.01    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))) )),
% 2.73/1.01    inference(definition_unfolding,[],[f35,f34])).
% 2.73/1.01  
% 2.73/1.01  fof(f33,plain,(
% 2.73/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f23])).
% 2.73/1.01  
% 2.73/1.01  fof(f31,plain,(
% 2.73/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f23])).
% 2.73/1.01  
% 2.73/1.01  fof(f32,plain,(
% 2.73/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f23])).
% 2.73/1.01  
% 2.73/1.01  fof(f13,conjecture,(
% 2.73/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f14,negated_conjecture,(
% 2.73/1.01    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.73/1.01    inference(negated_conjecture,[],[f13])).
% 2.73/1.01  
% 2.73/1.01  fof(f18,plain,(
% 2.73/1.01    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.73/1.01    inference(ennf_transformation,[],[f14])).
% 2.73/1.01  
% 2.73/1.01  fof(f25,plain,(
% 2.73/1.01    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 2.73/1.01    introduced(choice_axiom,[])).
% 2.73/1.01  
% 2.73/1.01  fof(f26,plain,(
% 2.73/1.01    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 2.73/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f25])).
% 2.73/1.01  
% 2.73/1.01  fof(f47,plain,(
% 2.73/1.01    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 2.73/1.01    inference(cnf_transformation,[],[f26])).
% 2.73/1.01  
% 2.73/1.01  fof(f8,axiom,(
% 2.73/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f42,plain,(
% 2.73/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.73/1.01    inference(cnf_transformation,[],[f8])).
% 2.73/1.01  
% 2.73/1.01  fof(f57,plain,(
% 2.73/1.01    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),
% 2.73/1.01    inference(definition_unfolding,[],[f47,f34,f42])).
% 2.73/1.01  
% 2.73/1.01  cnf(c_5,plain,
% 2.73/1.01      ( ~ r2_hidden(X0,X1)
% 2.73/1.01      | r2_hidden(X0,X2)
% 2.73/1.01      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 2.73/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_563,plain,
% 2.73/1.01      ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),X0)
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,X0))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_7304,plain,
% 2.73/1.01      ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,sK2))
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK2)
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_563]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_7,plain,
% 2.73/1.01      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 2.73/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_735,plain,
% 2.73/1.01      ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),X0)
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,X1)) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2041,plain,
% 2.73/1.01      ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,sK2))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(k4_xboole_0(X0,sK2),X1)) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_735]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_5911,plain,
% 2.73/1.01      ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,sK2))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X1,sK1))) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_2041]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_5917,plain,
% 2.73/1.01      ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK1)))
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,sK2)) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_5911]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_720,plain,
% 2.73/1.01      ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),X0)
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),X1)
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,X1)) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2299,plain,
% 2.73/1.01      ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),X0)
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,k4_xboole_0(X1,sK1)))
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X1,sK1)) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_720]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_5910,plain,
% 2.73/1.01      ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,sK2))
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X1,sK1))
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X1,sK1))) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_2299]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_5913,plain,
% 2.73/1.01      ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK1)))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,sK2))
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,sK1)) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_5910]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_4187,plain,
% 2.73/1.01      ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_735]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_6,plain,
% 2.73/1.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.73/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_721,plain,
% 2.73/1.01      ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),X0)
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X1,X0)) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2407,plain,
% 2.73/1.01      ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,sK2)) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_721]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1038,plain,
% 2.73/1.01      ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,sK2))
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,k4_xboole_0(X0,sK2)))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_563]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1041,plain,
% 2.73/1.01      ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,sK2))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_1038]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_9,plain,
% 2.73/1.01      ( ~ r2_hidden(X0,X1)
% 2.73/1.01      | r2_hidden(X0,X2)
% 2.73/1.01      | r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ),
% 2.73/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_560,plain,
% 2.73/1.01      ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),X0)
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k2_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(X0,sK1)))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1019,plain,
% 2.73/1.01      ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_560]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_10,plain,
% 2.73/1.01      ( ~ r2_hidden(X0,X1)
% 2.73/1.01      | ~ r2_hidden(X0,X2)
% 2.73/1.01      | ~ r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ),
% 2.73/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_559,plain,
% 2.73/1.01      ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),X0)
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k2_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(X0,sK1)))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_832,plain,
% 2.73/1.01      ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_559]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_626,plain,
% 2.73/1.01      ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,sK2))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK2) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_628,plain,
% 2.73/1.01      ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,sK2))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK2) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_626]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_564,plain,
% 2.73/1.01      ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(X0,sK1))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_566,plain,
% 2.73/1.01      ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,sK1))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_564]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_11,plain,
% 2.73/1.01      ( r2_hidden(X0,X1)
% 2.73/1.01      | r2_hidden(X0,X2)
% 2.73/1.01      | ~ r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ),
% 2.73/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_556,plain,
% 2.73/1.01      ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)))
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2,plain,
% 2.73/1.01      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 2.73/1.01      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.73/1.01      | r2_hidden(sK0(X0,X1,X2),X1)
% 2.73/1.01      | k4_xboole_0(X0,X1) = X2 ),
% 2.73/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_523,plain,
% 2.73/1.01      ( ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)))
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK2)
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1)
% 2.73/1.01      | k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_4,plain,
% 2.73/1.01      ( r2_hidden(sK0(X0,X1,X2),X0)
% 2.73/1.01      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.73/1.01      | k4_xboole_0(X0,X1) = X2 ),
% 2.73/1.01      inference(cnf_transformation,[],[f31]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_520,plain,
% 2.73/1.01      ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)))
% 2.73/1.01      | r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK1)
% 2.73/1.01      | k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_3,plain,
% 2.73/1.01      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 2.73/1.01      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.73/1.01      | k4_xboole_0(X0,X1) = X2 ),
% 2.73/1.01      inference(cnf_transformation,[],[f32]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_517,plain,
% 2.73/1.01      ( r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)))
% 2.73/1.01      | ~ r2_hidden(sK0(sK1,sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),sK2)
% 2.73/1.01      | k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_18,negated_conjecture,
% 2.73/1.01      ( k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
% 2.73/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(contradiction,plain,
% 2.73/1.01      ( $false ),
% 2.73/1.01      inference(minisat,
% 2.73/1.01                [status(thm)],
% 2.73/1.01                [c_7304,c_5917,c_5913,c_4187,c_2407,c_1041,c_1019,c_832,
% 2.73/1.01                 c_628,c_566,c_556,c_523,c_520,c_517,c_18]) ).
% 2.73/1.01  
% 2.73/1.01  
% 2.73/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.73/1.01  
% 2.73/1.01  ------                               Statistics
% 2.73/1.01  
% 2.73/1.01  ------ General
% 2.73/1.01  
% 2.73/1.01  abstr_ref_over_cycles:                  0
% 2.73/1.01  abstr_ref_under_cycles:                 0
% 2.73/1.01  gc_basic_clause_elim:                   0
% 2.73/1.01  forced_gc_time:                         0
% 2.73/1.01  parsing_time:                           0.009
% 2.73/1.01  unif_index_cands_time:                  0.
% 2.73/1.01  unif_index_add_time:                    0.
% 2.73/1.01  orderings_time:                         0.
% 2.73/1.01  out_proof_time:                         0.009
% 2.73/1.01  total_time:                             0.219
% 2.73/1.01  num_of_symbols:                         39
% 2.73/1.01  num_of_terms:                           8108
% 2.73/1.01  
% 2.73/1.01  ------ Preprocessing
% 2.73/1.01  
% 2.73/1.01  num_of_splits:                          0
% 2.73/1.01  num_of_split_atoms:                     0
% 2.73/1.01  num_of_reused_defs:                     0
% 2.73/1.01  num_eq_ax_congr_red:                    10
% 2.73/1.01  num_of_sem_filtered_clauses:            1
% 2.73/1.01  num_of_subtypes:                        0
% 2.73/1.01  monotx_restored_types:                  0
% 2.73/1.01  sat_num_of_epr_types:                   0
% 2.73/1.01  sat_num_of_non_cyclic_types:            0
% 2.73/1.01  sat_guarded_non_collapsed_types:        0
% 2.73/1.01  num_pure_diseq_elim:                    0
% 2.73/1.01  simp_replaced_by:                       0
% 2.73/1.01  res_preprocessed:                       84
% 2.73/1.01  prep_upred:                             0
% 2.73/1.01  prep_unflattend:                        2
% 2.73/1.01  smt_new_axioms:                         0
% 2.73/1.01  pred_elim_cands:                        1
% 2.73/1.01  pred_elim:                              1
% 2.73/1.01  pred_elim_cl:                           1
% 2.73/1.01  pred_elim_cycles:                       3
% 2.73/1.01  merged_defs:                            0
% 2.73/1.01  merged_defs_ncl:                        0
% 2.73/1.01  bin_hyper_res:                          0
% 2.73/1.01  prep_cycles:                            4
% 2.73/1.01  pred_elim_time:                         0.001
% 2.73/1.01  splitting_time:                         0.
% 2.73/1.01  sem_filter_time:                        0.
% 2.73/1.01  monotx_time:                            0.001
% 2.73/1.01  subtype_inf_time:                       0.
% 2.73/1.01  
% 2.73/1.01  ------ Problem properties
% 2.73/1.01  
% 2.73/1.01  clauses:                                18
% 2.73/1.01  conjectures:                            1
% 2.73/1.01  epr:                                    0
% 2.73/1.01  horn:                                   11
% 2.73/1.01  ground:                                 1
% 2.73/1.01  unary:                                  8
% 2.73/1.01  binary:                                 2
% 2.73/1.01  lits:                                   37
% 2.73/1.01  lits_eq:                                11
% 2.73/1.01  fd_pure:                                0
% 2.73/1.01  fd_pseudo:                              0
% 2.73/1.01  fd_cond:                                0
% 2.73/1.01  fd_pseudo_cond:                         3
% 2.73/1.01  ac_symbols:                             0
% 2.73/1.01  
% 2.73/1.01  ------ Propositional Solver
% 2.73/1.01  
% 2.73/1.01  prop_solver_calls:                      27
% 2.73/1.01  prop_fast_solver_calls:                 401
% 2.73/1.01  smt_solver_calls:                       0
% 2.73/1.01  smt_fast_solver_calls:                  0
% 2.73/1.01  prop_num_of_clauses:                    2247
% 2.73/1.01  prop_preprocess_simplified:             4822
% 2.73/1.01  prop_fo_subsumed:                       0
% 2.73/1.01  prop_solver_time:                       0.
% 2.73/1.01  smt_solver_time:                        0.
% 2.73/1.01  smt_fast_solver_time:                   0.
% 2.73/1.01  prop_fast_solver_time:                  0.
% 2.73/1.01  prop_unsat_core_time:                   0.
% 2.73/1.01  
% 2.73/1.01  ------ QBF
% 2.73/1.01  
% 2.73/1.01  qbf_q_res:                              0
% 2.73/1.01  qbf_num_tautologies:                    0
% 2.73/1.01  qbf_prep_cycles:                        0
% 2.73/1.01  
% 2.73/1.01  ------ BMC1
% 2.73/1.01  
% 2.73/1.01  bmc1_current_bound:                     -1
% 2.73/1.01  bmc1_last_solved_bound:                 -1
% 2.73/1.01  bmc1_unsat_core_size:                   -1
% 2.73/1.01  bmc1_unsat_core_parents_size:           -1
% 2.73/1.01  bmc1_merge_next_fun:                    0
% 2.73/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.73/1.01  
% 2.73/1.01  ------ Instantiation
% 2.73/1.01  
% 2.73/1.01  inst_num_of_clauses:                    419
% 2.73/1.01  inst_num_in_passive:                    275
% 2.73/1.01  inst_num_in_active:                     143
% 2.73/1.01  inst_num_in_unprocessed:                0
% 2.73/1.01  inst_num_of_loops:                      182
% 2.73/1.01  inst_num_of_learning_restarts:          0
% 2.73/1.01  inst_num_moves_active_passive:          37
% 2.73/1.01  inst_lit_activity:                      0
% 2.73/1.01  inst_lit_activity_moves:                0
% 2.73/1.01  inst_num_tautologies:                   0
% 2.73/1.01  inst_num_prop_implied:                  0
% 2.73/1.01  inst_num_existing_simplified:           0
% 2.73/1.01  inst_num_eq_res_simplified:             0
% 2.73/1.01  inst_num_child_elim:                    0
% 2.73/1.01  inst_num_of_dismatching_blockings:      524
% 2.73/1.01  inst_num_of_non_proper_insts:           402
% 2.73/1.01  inst_num_of_duplicates:                 0
% 2.73/1.01  inst_inst_num_from_inst_to_res:         0
% 2.73/1.01  inst_dismatching_checking_time:         0.
% 2.73/1.01  
% 2.73/1.01  ------ Resolution
% 2.73/1.01  
% 2.73/1.01  res_num_of_clauses:                     0
% 2.73/1.01  res_num_in_passive:                     0
% 2.73/1.01  res_num_in_active:                      0
% 2.73/1.01  res_num_of_loops:                       88
% 2.73/1.01  res_forward_subset_subsumed:            14
% 2.73/1.01  res_backward_subset_subsumed:           0
% 2.73/1.01  res_forward_subsumed:                   0
% 2.73/1.01  res_backward_subsumed:                  0
% 2.73/1.01  res_forward_subsumption_resolution:     0
% 2.73/1.01  res_backward_subsumption_resolution:    0
% 2.73/1.01  res_clause_to_clause_subsumption:       3640
% 2.73/1.01  res_orphan_elimination:                 0
% 2.73/1.01  res_tautology_del:                      11
% 2.73/1.01  res_num_eq_res_simplified:              0
% 2.73/1.01  res_num_sel_changes:                    0
% 2.73/1.01  res_moves_from_active_to_pass:          0
% 2.73/1.01  
% 2.73/1.01  ------ Superposition
% 2.73/1.01  
% 2.73/1.01  sup_time_total:                         0.
% 2.73/1.01  sup_time_generating:                    0.
% 2.73/1.01  sup_time_sim_full:                      0.
% 2.73/1.01  sup_time_sim_immed:                     0.
% 2.73/1.01  
% 2.73/1.01  sup_num_of_clauses:                     405
% 2.73/1.01  sup_num_in_active:                      36
% 2.73/1.01  sup_num_in_passive:                     369
% 2.73/1.01  sup_num_of_loops:                       36
% 2.73/1.01  sup_fw_superposition:                   591
% 2.73/1.01  sup_bw_superposition:                   485
% 2.73/1.01  sup_immediate_simplified:               617
% 2.73/1.01  sup_given_eliminated:                   0
% 2.73/1.01  comparisons_done:                       0
% 2.73/1.01  comparisons_avoided:                    0
% 2.73/1.01  
% 2.73/1.01  ------ Simplifications
% 2.73/1.01  
% 2.73/1.01  
% 2.73/1.01  sim_fw_subset_subsumed:                 3
% 2.73/1.01  sim_bw_subset_subsumed:                 0
% 2.73/1.01  sim_fw_subsumed:                        49
% 2.73/1.01  sim_bw_subsumed:                        7
% 2.73/1.01  sim_fw_subsumption_res:                 2
% 2.73/1.01  sim_bw_subsumption_res:                 0
% 2.73/1.01  sim_tautology_del:                      10
% 2.73/1.01  sim_eq_tautology_del:                   114
% 2.73/1.01  sim_eq_res_simp:                        0
% 2.73/1.01  sim_fw_demodulated:                     318
% 2.73/1.01  sim_bw_demodulated:                     22
% 2.73/1.01  sim_light_normalised:                   281
% 2.73/1.01  sim_joinable_taut:                      0
% 2.73/1.01  sim_joinable_simp:                      0
% 2.73/1.01  sim_ac_normalised:                      0
% 2.73/1.01  sim_smt_subsumption:                    0
% 2.73/1.01  
%------------------------------------------------------------------------------
