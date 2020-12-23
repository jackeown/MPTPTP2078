%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0037+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:18 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 280 expanded)
%              Number of clauses        :   36 (  64 expanded)
%              Number of leaves         :    7 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  297 (1943 expanded)
%              Number of equality atoms :   41 ( 283 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(k2_xboole_0(X0,X2),X1) = k2_xboole_0(X0,k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => k3_xboole_0(k2_xboole_0(X0,X2),X1) = k2_xboole_0(X0,k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_xboole_0(X0,X2),X1) != k2_xboole_0(X0,k3_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(k2_xboole_0(X0,X2),X1) != k2_xboole_0(X0,k3_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(k2_xboole_0(sK2,sK4),sK3) != k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( k3_xboole_0(k2_xboole_0(sK2,sK4),sK3) != k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f20])).

fof(f37,plain,(
    k3_xboole_0(k2_xboole_0(sK2,sK4),sK3) != k2_xboole_0(sK2,k3_xboole_0(sK4,sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f26])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2299,plain,
    ( r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k2_xboole_0(sK2,X0))
    | ~ r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_6384,plain,
    ( r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k2_xboole_0(sK2,k3_xboole_0(sK4,sK3)))
    | ~ r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_2299])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_818,plain,
    ( ~ r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),X0)
    | r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,X0))
    | ~ r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3749,plain,
    ( r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,sK3))
    | ~ r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK3)
    | ~ r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK4) ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_10,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_14,negated_conjecture,
    ( k3_xboole_0(k2_xboole_0(sK2,sK4),sK3) != k2_xboole_0(sK2,k3_xboole_0(sK4,sK3)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2203,plain,
    ( r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k2_xboole_0(sK2,k3_xboole_0(sK4,sK3)))
    | r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k2_xboole_0(sK2,sK4)) ),
    inference(resolution,[status(thm)],[c_10,c_14])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2662,plain,
    ( r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k2_xboole_0(sK2,sK4))
    | r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,sK3))
    | r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK2) ),
    inference(resolution,[status(thm)],[c_2203,c_7])).

cnf(c_727,plain,
    ( ~ r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k2_xboole_0(sK2,k3_xboole_0(sK4,sK3)))
    | r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,sK3))
    | r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_805,plain,
    ( r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k2_xboole_0(X0,sK4))
    | ~ r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_807,plain,
    ( r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k2_xboole_0(sK2,sK4))
    | ~ r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK4) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1082,plain,
    ( ~ r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,sK3))
    | r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2888,plain,
    ( r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k2_xboole_0(sK2,sK4))
    | r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2662,c_727,c_807,c_1082,c_2203])).

cnf(c_2894,plain,
    ( r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k2_xboole_0(sK2,sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2888,c_6])).

cnf(c_2902,plain,
    ( r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK4)
    | r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK2) ),
    inference(resolution,[status(thm)],[c_2894,c_7])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1124,plain,
    ( r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k2_xboole_0(sK2,k3_xboole_0(sK4,sK3)))
    | r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK3) ),
    inference(resolution,[status(thm)],[c_9,c_14])).

cnf(c_1613,plain,
    ( r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,sK3))
    | r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK3)
    | r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK2) ),
    inference(resolution,[status(thm)],[c_7,c_1124])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1079,plain,
    ( ~ r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,sK3))
    | r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1711,plain,
    ( r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK3)
    | r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1613,c_1079])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_156,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_157,plain,
    ( r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_156])).

cnf(c_1717,plain,
    ( r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1711,c_157])).

cnf(c_1061,plain,
    ( r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k2_xboole_0(X0,k3_xboole_0(sK4,sK3)))
    | ~ r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1063,plain,
    ( r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k2_xboole_0(sK2,k3_xboole_0(sK4,sK3)))
    | ~ r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k3_xboole_0(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_8,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_730,plain,
    ( ~ r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k2_xboole_0(sK2,k3_xboole_0(sK4,sK3)))
    | ~ r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),k2_xboole_0(sK2,sK4))
    | ~ r2_hidden(sK1(k2_xboole_0(sK2,sK4),sK3,k2_xboole_0(sK2,k3_xboole_0(sK4,sK3))),sK3)
    | k3_xboole_0(k2_xboole_0(sK2,sK4),sK3) = k2_xboole_0(sK2,k3_xboole_0(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6384,c_3749,c_2902,c_2894,c_1717,c_1063,c_730,c_14])).


%------------------------------------------------------------------------------
