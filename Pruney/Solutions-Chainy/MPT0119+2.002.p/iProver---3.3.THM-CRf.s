%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:09 EST 2020

% Result     : Theorem 7.86s
% Output     : CNFRefutation 7.86s
% Verified   : 
% Statistics : Number of formulae       :  101 (2696 expanded)
%              Number of clauses        :   73 ( 725 expanded)
%              Number of leaves         :    8 ( 576 expanded)
%              Depth                    :   25
%              Number of atoms          :  361 (16178 expanded)
%              Number of equality atoms :   70 (2369 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f7])).

fof(f9,plain,(
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
    inference(rectify,[],[f8])).

fof(f10,plain,(
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

fof(f11,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) != k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) != k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))
   => k3_xboole_0(k5_xboole_0(sK1,sK3),sK2) != k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    k3_xboole_0(k5_xboole_0(sK1,sK3),sK2) != k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f6,f13])).

fof(f25,plain,(
    k3_xboole_0(k5_xboole_0(sK1,sK3),sK2) != k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f16,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f17,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f17])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_2159,plain,
    ( ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X3)),X2)
    | ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X3)),X0)
    | ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X3)),X1)
    | r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X3)),X3)
    | k3_xboole_0(X0,X1) = k5_xboole_0(X2,X3) ),
    inference(resolution,[status(thm)],[c_0,c_7])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_10,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(sK1,sK3),sK2) != k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_725,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK2) ),
    inference(resolution,[status(thm)],[c_1,c_10])).

cnf(c_1010,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK2) ),
    inference(resolution,[status(thm)],[c_9,c_725])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1016,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1010,c_4,c_4])).

cnf(c_16289,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | k3_xboole_0(k5_xboole_0(sK1,sK3),sK2) = k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)) ),
    inference(resolution,[status(thm)],[c_2159,c_1016])).

cnf(c_116,plain,
    ( X0 != X1
    | X2 != X3
    | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_115,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2139,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
    | r2_hidden(X3,k5_xboole_0(X4,X5))
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    inference(resolution,[status(thm)],[c_116,c_115])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_1880,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3)) ),
    inference(resolution,[status(thm)],[c_2,c_10])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_2352,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_1880,c_8])).

cnf(c_12005,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X2))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | X0 != sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))
    | X2 != sK3
    | X1 != sK1 ),
    inference(resolution,[status(thm)],[c_2139,c_2352])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_601,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0)
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1332,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3) ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_2351,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_1880,c_9])).

cnf(c_2364,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
    inference(resolution,[status(thm)],[c_2351,c_8])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_497,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0)
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,X0))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_499,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK2)
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3) ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_2604,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2364,c_499,c_1016])).

cnf(c_2605,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3) ),
    inference(renaming,[status(thm)],[c_2604])).

cnf(c_2587,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
    inference(resolution,[status(thm)],[c_2352,c_8])).

cnf(c_2790,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2605,c_2587])).

cnf(c_3023,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2790,c_5])).

cnf(c_13710,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12005,c_1332,c_3023])).

cnf(c_13711,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_13710])).

cnf(c_19502,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16289,c_10,c_13711])).

cnf(c_19503,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2)) ),
    inference(renaming,[status(thm)],[c_19502])).

cnf(c_12000,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X2))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | X0 != sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))
    | X2 != k3_xboole_0(sK3,sK2)
    | X1 != k3_xboole_0(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_2139,c_1880])).

cnf(c_112,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_12787,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(X0,X1))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | X1 != k3_xboole_0(sK3,sK2)
    | X0 != k3_xboole_0(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_12000,c_112])).

cnf(c_13264,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0)
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X1)
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | X1 != k3_xboole_0(sK3,sK2)
    | X0 != k3_xboole_0(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_12787,c_8])).

cnf(c_1303,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_115,c_112])).

cnf(c_733,plain,
    ( r2_hidden(sK0(X0,X1,X1),X1)
    | k3_xboole_0(X0,X1) = X1 ),
    inference(factoring,[status(thm)],[c_1])).

cnf(c_1433,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(X2,X0,X0),X0)
    | r2_hidden(k3_xboole_0(X2,X0),X1) ),
    inference(resolution,[status(thm)],[c_1303,c_733])).

cnf(c_1447,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | r2_hidden(sK0(X3,X0,X0),X0)
    | r2_hidden(k3_xboole_0(X3,X0),X2) ),
    inference(resolution,[status(thm)],[c_1433,c_4])).

cnf(c_2796,plain,
    ( r2_hidden(sK0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
    | r2_hidden(k3_xboole_0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),sK2) ),
    inference(resolution,[status(thm)],[c_2605,c_1447])).

cnf(c_3036,plain,
    ( ~ r2_hidden(sK0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),X0)
    | ~ r2_hidden(sK0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
    | r2_hidden(k3_xboole_0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),sK2)
    | k3_xboole_0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))) = sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))) ),
    inference(resolution,[status(thm)],[c_2796,c_0])).

cnf(c_3172,plain,
    ( ~ r2_hidden(sK0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),X0)
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
    | r2_hidden(k3_xboole_0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),sK2)
    | k3_xboole_0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))) = sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3036,c_2796])).

cnf(c_3207,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(X0,X1),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),X0)
    | r2_hidden(sK0(k5_xboole_0(X0,X1),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),X1)
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
    | r2_hidden(k3_xboole_0(k5_xboole_0(X0,X1),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),sK2)
    | k3_xboole_0(k5_xboole_0(X0,X1),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))) = sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))) ),
    inference(resolution,[status(thm)],[c_3172,c_7])).

cnf(c_4379,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),X0)
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
    | r2_hidden(k3_xboole_0(k5_xboole_0(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),sK2)
    | k3_xboole_0(k5_xboole_0(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))) = sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))) ),
    inference(resolution,[status(thm)],[c_3207,c_733])).

cnf(c_12819,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),X0)
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
    | r2_hidden(k3_xboole_0(k5_xboole_0(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),k5_xboole_0(X1,X2))
    | r2_hidden(k3_xboole_0(k5_xboole_0(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),sK2)
    | X2 != k3_xboole_0(sK3,sK2)
    | X1 != k3_xboole_0(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_12000,c_4379])).

cnf(c_3046,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK2)
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
    inference(resolution,[status(thm)],[c_3023,c_3])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_483,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0)
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(X0,sK3))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_11160,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_16421,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12819,c_1016,c_3046,c_11160])).

cnf(c_13263,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0)
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X1)
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | X1 != k3_xboole_0(sK3,sK2)
    | X0 != k3_xboole_0(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_12787,c_9])).

cnf(c_16976,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0)
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | X0 != k3_xboole_0(sK1,sK2)
    | k3_xboole_0(sK3,sK2) != k3_xboole_0(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_13263,c_13711])).

cnf(c_16977,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0)
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | X0 != k3_xboole_0(sK1,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_16976])).

cnf(c_17212,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X1)
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | X1 != k3_xboole_0(sK3,sK2)
    | X0 != k3_xboole_0(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13264,c_1016,c_1332,c_2351,c_3046,c_11160,c_16977])).

cnf(c_17213,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0)
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | X0 != k3_xboole_0(sK3,sK2)
    | X1 != k3_xboole_0(sK1,sK2) ),
    inference(renaming,[status(thm)],[c_17212])).

cnf(c_17584,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | X0 != k3_xboole_0(sK1,sK2)
    | k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)) != k3_xboole_0(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_17213,c_1880])).

cnf(c_17643,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)) != k3_xboole_0(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_17584,c_112])).

cnf(c_19537,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)) != k3_xboole_0(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_19503,c_17643])).

cnf(c_8893,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,X0))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_8927,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
    inference(instantiation,[status(thm)],[c_8893])).

cnf(c_19530,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
    inference(resolution,[status(thm)],[c_19503,c_7])).

cnf(c_19547,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19537,c_3023,c_8927,c_19530])).

cnf(c_19902,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK2)
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
    inference(resolution,[status(thm)],[c_19547,c_3])).

cnf(c_2161,plain,
    ( ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X3)),X0)
    | ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X3)),X1)
    | r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X3)),X2)
    | k3_xboole_0(X0,X1) = k5_xboole_0(X2,X3) ),
    inference(resolution,[status(thm)],[c_0,c_6])).

cnf(c_17923,plain,
    ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | k3_xboole_0(k5_xboole_0(sK1,sK3),sK2) = k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)) ),
    inference(resolution,[status(thm)],[c_2161,c_1016])).

cnf(c_2363,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
    inference(resolution,[status(thm)],[c_2351,c_9])).

cnf(c_2591,plain,
    ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
    | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2363,c_1332])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19902,c_19547,c_17923,c_11160,c_2591,c_1016,c_499,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:35:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.86/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.86/1.49  
% 7.86/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.86/1.49  
% 7.86/1.49  ------  iProver source info
% 7.86/1.49  
% 7.86/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.86/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.86/1.49  git: non_committed_changes: false
% 7.86/1.49  git: last_make_outside_of_git: false
% 7.86/1.49  
% 7.86/1.49  ------ 
% 7.86/1.49  ------ Parsing...
% 7.86/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.86/1.49  
% 7.86/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.86/1.49  
% 7.86/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.86/1.49  
% 7.86/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.86/1.49  ------ Proving...
% 7.86/1.49  ------ Problem Properties 
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  clauses                                 11
% 7.86/1.49  conjectures                             1
% 7.86/1.49  EPR                                     0
% 7.86/1.49  Horn                                    6
% 7.86/1.49  unary                                   1
% 7.86/1.49  binary                                  2
% 7.86/1.49  lits                                    30
% 7.86/1.49  lits eq                                 4
% 7.86/1.49  fd_pure                                 0
% 7.86/1.49  fd_pseudo                               0
% 7.86/1.49  fd_cond                                 0
% 7.86/1.49  fd_pseudo_cond                          3
% 7.86/1.49  AC symbols                              0
% 7.86/1.49  
% 7.86/1.49  ------ Input Options Time Limit: Unbounded
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  ------ 
% 7.86/1.49  Current options:
% 7.86/1.49  ------ 
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  ------ Proving...
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  % SZS status Theorem for theBenchmark.p
% 7.86/1.49  
% 7.86/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.86/1.49  
% 7.86/1.49  fof(f1,axiom,(
% 7.86/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.86/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f7,plain,(
% 7.86/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.86/1.49    inference(nnf_transformation,[],[f1])).
% 7.86/1.49  
% 7.86/1.49  fof(f8,plain,(
% 7.86/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.86/1.49    inference(flattening,[],[f7])).
% 7.86/1.49  
% 7.86/1.49  fof(f9,plain,(
% 7.86/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.86/1.49    inference(rectify,[],[f8])).
% 7.86/1.49  
% 7.86/1.49  fof(f10,plain,(
% 7.86/1.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.86/1.49    introduced(choice_axiom,[])).
% 7.86/1.49  
% 7.86/1.49  fof(f11,plain,(
% 7.86/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.86/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).
% 7.86/1.49  
% 7.86/1.49  fof(f20,plain,(
% 7.86/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f11])).
% 7.86/1.49  
% 7.86/1.49  fof(f2,axiom,(
% 7.86/1.49    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 7.86/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f5,plain,(
% 7.86/1.49    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 7.86/1.49    inference(ennf_transformation,[],[f2])).
% 7.86/1.49  
% 7.86/1.49  fof(f12,plain,(
% 7.86/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 7.86/1.49    inference(nnf_transformation,[],[f5])).
% 7.86/1.49  
% 7.86/1.49  fof(f23,plain,(
% 7.86/1.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f12])).
% 7.86/1.49  
% 7.86/1.49  fof(f21,plain,(
% 7.86/1.49    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 7.86/1.49    inference(cnf_transformation,[],[f12])).
% 7.86/1.49  
% 7.86/1.49  fof(f19,plain,(
% 7.86/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f11])).
% 7.86/1.49  
% 7.86/1.49  fof(f3,conjecture,(
% 7.86/1.49    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 7.86/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f4,negated_conjecture,(
% 7.86/1.49    ~! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 7.86/1.49    inference(negated_conjecture,[],[f3])).
% 7.86/1.49  
% 7.86/1.49  fof(f6,plain,(
% 7.86/1.49    ? [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) != k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 7.86/1.49    inference(ennf_transformation,[],[f4])).
% 7.86/1.49  
% 7.86/1.49  fof(f13,plain,(
% 7.86/1.49    ? [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) != k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) => k3_xboole_0(k5_xboole_0(sK1,sK3),sK2) != k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),
% 7.86/1.49    introduced(choice_axiom,[])).
% 7.86/1.49  
% 7.86/1.49  fof(f14,plain,(
% 7.86/1.49    k3_xboole_0(k5_xboole_0(sK1,sK3),sK2) != k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),
% 7.86/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f6,f13])).
% 7.86/1.49  
% 7.86/1.49  fof(f25,plain,(
% 7.86/1.49    k3_xboole_0(k5_xboole_0(sK1,sK3),sK2) != k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),
% 7.86/1.49    inference(cnf_transformation,[],[f14])).
% 7.86/1.49  
% 7.86/1.49  fof(f16,plain,(
% 7.86/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.86/1.49    inference(cnf_transformation,[],[f11])).
% 7.86/1.49  
% 7.86/1.49  fof(f27,plain,(
% 7.86/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 7.86/1.49    inference(equality_resolution,[],[f16])).
% 7.86/1.49  
% 7.86/1.49  fof(f18,plain,(
% 7.86/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f11])).
% 7.86/1.49  
% 7.86/1.49  fof(f22,plain,(
% 7.86/1.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 7.86/1.49    inference(cnf_transformation,[],[f12])).
% 7.86/1.49  
% 7.86/1.49  fof(f15,plain,(
% 7.86/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.86/1.49    inference(cnf_transformation,[],[f11])).
% 7.86/1.49  
% 7.86/1.49  fof(f28,plain,(
% 7.86/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 7.86/1.49    inference(equality_resolution,[],[f15])).
% 7.86/1.49  
% 7.86/1.49  fof(f17,plain,(
% 7.86/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 7.86/1.49    inference(cnf_transformation,[],[f11])).
% 7.86/1.49  
% 7.86/1.49  fof(f26,plain,(
% 7.86/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.86/1.49    inference(equality_resolution,[],[f17])).
% 7.86/1.49  
% 7.86/1.49  fof(f24,plain,(
% 7.86/1.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f12])).
% 7.86/1.49  
% 7.86/1.49  cnf(c_0,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 7.86/1.49      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 7.86/1.49      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 7.86/1.49      | k3_xboole_0(X0,X1) = X2 ),
% 7.86/1.49      inference(cnf_transformation,[],[f20]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_7,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,X1)
% 7.86/1.49      | r2_hidden(X0,X2)
% 7.86/1.49      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 7.86/1.49      inference(cnf_transformation,[],[f23]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2159,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X3)),X2)
% 7.86/1.49      | ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X3)),X0)
% 7.86/1.49      | ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X3)),X1)
% 7.86/1.49      | r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X3)),X3)
% 7.86/1.49      | k3_xboole_0(X0,X1) = k5_xboole_0(X2,X3) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_0,c_7]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_9,plain,
% 7.86/1.49      ( r2_hidden(X0,X1)
% 7.86/1.49      | r2_hidden(X0,X2)
% 7.86/1.49      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 7.86/1.49      inference(cnf_transformation,[],[f21]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1,plain,
% 7.86/1.49      ( r2_hidden(sK0(X0,X1,X2),X1)
% 7.86/1.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.86/1.49      | k3_xboole_0(X0,X1) = X2 ),
% 7.86/1.49      inference(cnf_transformation,[],[f19]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_10,negated_conjecture,
% 7.86/1.49      ( k3_xboole_0(k5_xboole_0(sK1,sK3),sK2) != k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)) ),
% 7.86/1.49      inference(cnf_transformation,[],[f25]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_725,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK2) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_1,c_10]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1010,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK2) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_9,c_725]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_4,plain,
% 7.86/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 7.86/1.49      inference(cnf_transformation,[],[f27]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1016,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK2) ),
% 7.86/1.49      inference(forward_subsumption_resolution,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_1010,c_4,c_4]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_16289,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | k3_xboole_0(k5_xboole_0(sK1,sK3),sK2) = k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_2159,c_1016]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_116,plain,
% 7.86/1.49      ( X0 != X1 | X2 != X3 | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
% 7.86/1.49      theory(equality) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_115,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.86/1.49      theory(equality) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2139,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
% 7.86/1.49      | r2_hidden(X3,k5_xboole_0(X4,X5))
% 7.86/1.49      | X3 != X0
% 7.86/1.49      | X4 != X1
% 7.86/1.49      | X5 != X2 ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_116,c_115]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2,plain,
% 7.86/1.49      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.86/1.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.86/1.49      | k3_xboole_0(X0,X1) = X2 ),
% 7.86/1.49      inference(cnf_transformation,[],[f18]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1880,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3)) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_2,c_10]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_8,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,X1)
% 7.86/1.49      | ~ r2_hidden(X0,X2)
% 7.86/1.49      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 7.86/1.49      inference(cnf_transformation,[],[f22]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2352,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2)) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_1880,c_8]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_12005,plain,
% 7.86/1.49      ( r2_hidden(X0,k5_xboole_0(X1,X2))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | X0 != sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))
% 7.86/1.49      | X2 != sK3
% 7.86/1.49      | X1 != sK1 ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_2139,c_2352]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_5,plain,
% 7.86/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 7.86/1.49      inference(cnf_transformation,[],[f28]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_601,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0)
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(X0,X1)) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1332,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_601]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2351,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2)) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_1880,c_9]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2364,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_2351,c_8]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_3,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,X1)
% 7.86/1.49      | ~ r2_hidden(X0,X2)
% 7.86/1.49      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 7.86/1.49      inference(cnf_transformation,[],[f26]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_497,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0)
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,X0))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_499,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK2)
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_497]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2604,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2)) ),
% 7.86/1.49      inference(global_propositional_subsumption,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_2364,c_499,c_1016]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2605,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3) ),
% 7.86/1.49      inference(renaming,[status(thm)],[c_2604]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2587,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_2352,c_8]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2790,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
% 7.86/1.49      inference(backward_subsumption_resolution,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_2605,c_2587]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_3023,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3) ),
% 7.86/1.49      inference(forward_subsumption_resolution,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_2790,c_5]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_13710,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2)) ),
% 7.86/1.49      inference(global_propositional_subsumption,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_12005,c_1332,c_3023]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_13711,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2)) ),
% 7.86/1.49      inference(renaming,[status(thm)],[c_13710]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_19502,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3)) ),
% 7.86/1.49      inference(global_propositional_subsumption,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_16289,c_10,c_13711]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_19503,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2)) ),
% 7.86/1.49      inference(renaming,[status(thm)],[c_19502]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_12000,plain,
% 7.86/1.49      ( r2_hidden(X0,k5_xboole_0(X1,X2))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | X0 != sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))
% 7.86/1.49      | X2 != k3_xboole_0(sK3,sK2)
% 7.86/1.49      | X1 != k3_xboole_0(sK1,sK2) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_2139,c_1880]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_112,plain,( X0 = X0 ),theory(equality) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_12787,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(X0,X1))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | X1 != k3_xboole_0(sK3,sK2)
% 7.86/1.49      | X0 != k3_xboole_0(sK1,sK2) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_12000,c_112]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_13264,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0)
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X1)
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | X1 != k3_xboole_0(sK3,sK2)
% 7.86/1.49      | X0 != k3_xboole_0(sK1,sK2) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_12787,c_8]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1303,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_115,c_112]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_733,plain,
% 7.86/1.49      ( r2_hidden(sK0(X0,X1,X1),X1) | k3_xboole_0(X0,X1) = X1 ),
% 7.86/1.49      inference(factoring,[status(thm)],[c_1]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1433,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,X1)
% 7.86/1.49      | r2_hidden(sK0(X2,X0,X0),X0)
% 7.86/1.49      | r2_hidden(k3_xboole_0(X2,X0),X1) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_1303,c_733]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1447,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 7.86/1.49      | r2_hidden(sK0(X3,X0,X0),X0)
% 7.86/1.49      | r2_hidden(k3_xboole_0(X3,X0),X2) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_1433,c_4]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2796,plain,
% 7.86/1.49      ( r2_hidden(sK0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
% 7.86/1.49      | r2_hidden(k3_xboole_0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),sK2) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_2605,c_1447]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_3036,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),X0)
% 7.86/1.49      | ~ r2_hidden(sK0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
% 7.86/1.49      | r2_hidden(k3_xboole_0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),sK2)
% 7.86/1.49      | k3_xboole_0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))) = sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_2796,c_0]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_3172,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),X0)
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
% 7.86/1.49      | r2_hidden(k3_xboole_0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),sK2)
% 7.86/1.49      | k3_xboole_0(X0,sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))) = sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))) ),
% 7.86/1.49      inference(global_propositional_subsumption,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_3036,c_2796]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_3207,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(X0,X1),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),X0)
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(X0,X1),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),X1)
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
% 7.86/1.49      | r2_hidden(k3_xboole_0(k5_xboole_0(X0,X1),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),sK2)
% 7.86/1.49      | k3_xboole_0(k5_xboole_0(X0,X1),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))) = sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_3172,c_7]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_4379,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),X0)
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
% 7.86/1.49      | r2_hidden(k3_xboole_0(k5_xboole_0(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),sK2)
% 7.86/1.49      | k3_xboole_0(k5_xboole_0(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))) = sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_3207,c_733]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_12819,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),X0)
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
% 7.86/1.49      | r2_hidden(k3_xboole_0(k5_xboole_0(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),k5_xboole_0(X1,X2))
% 7.86/1.49      | r2_hidden(k3_xboole_0(k5_xboole_0(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0),sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)))),sK2)
% 7.86/1.49      | X2 != k3_xboole_0(sK3,sK2)
% 7.86/1.49      | X1 != k3_xboole_0(sK1,sK2) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_12000,c_4379]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_3046,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK2)
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_3023,c_3]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_6,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,X1)
% 7.86/1.49      | r2_hidden(X0,X2)
% 7.86/1.49      | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 7.86/1.49      inference(cnf_transformation,[],[f24]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_483,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0)
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(X0,sK3))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_11160,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_483]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_16421,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3) ),
% 7.86/1.49      inference(global_propositional_subsumption,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_12819,c_1016,c_3046,c_11160]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_13263,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0)
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X1)
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | X1 != k3_xboole_0(sK3,sK2)
% 7.86/1.49      | X0 != k3_xboole_0(sK1,sK2) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_12787,c_9]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_16976,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0)
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | X0 != k3_xboole_0(sK1,sK2)
% 7.86/1.49      | k3_xboole_0(sK3,sK2) != k3_xboole_0(sK3,sK2) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_13263,c_13711]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_16977,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0)
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | X0 != k3_xboole_0(sK1,sK2) ),
% 7.86/1.49      inference(equality_resolution_simp,[status(thm)],[c_16976]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_17212,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X1)
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | X1 != k3_xboole_0(sK3,sK2)
% 7.86/1.49      | X0 != k3_xboole_0(sK1,sK2) ),
% 7.86/1.49      inference(global_propositional_subsumption,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_13264,c_1016,c_1332,c_2351,c_3046,c_11160,c_16977]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_17213,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),X0)
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | X0 != k3_xboole_0(sK3,sK2)
% 7.86/1.49      | X1 != k3_xboole_0(sK1,sK2) ),
% 7.86/1.49      inference(renaming,[status(thm)],[c_17212]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_17584,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | X0 != k3_xboole_0(sK1,sK2)
% 7.86/1.49      | k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)) != k3_xboole_0(sK3,sK2) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_17213,c_1880]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_17643,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)) != k3_xboole_0(sK3,sK2) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_17584,c_112]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_19537,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)) != k3_xboole_0(sK3,sK2) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_19503,c_17643]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_8893,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,X0))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_601]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_8927,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_8893]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_19530,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_19503,c_7]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_19547,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2)) ),
% 7.86/1.49      inference(global_propositional_subsumption,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_19537,c_3023,c_8927,c_19530]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_19902,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK2)
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_19547,c_3]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2161,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X3)),X3)
% 7.86/1.49      | ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X3)),X0)
% 7.86/1.49      | ~ r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X3)),X1)
% 7.86/1.49      | r2_hidden(sK0(X0,X1,k5_xboole_0(X2,X3)),X2)
% 7.86/1.49      | k3_xboole_0(X0,X1) = k5_xboole_0(X2,X3) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_0,c_6]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_17923,plain,
% 7.86/1.49      ( ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,sK3))
% 7.86/1.49      | ~ r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | k3_xboole_0(k5_xboole_0(sK1,sK3),sK2) = k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2)) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_2161,c_1016]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2363,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK3,sK2))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
% 7.86/1.49      inference(resolution,[status(thm)],[c_2351,c_9]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2591,plain,
% 7.86/1.49      ( r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),k3_xboole_0(sK1,sK2))
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK3)
% 7.86/1.49      | r2_hidden(sK0(k5_xboole_0(sK1,sK3),sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,sK2))),sK1) ),
% 7.86/1.49      inference(global_propositional_subsumption,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_2363,c_1332]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(contradiction,plain,
% 7.86/1.49      ( $false ),
% 7.86/1.49      inference(minisat,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_19902,c_19547,c_17923,c_11160,c_2591,c_1016,c_499,
% 7.86/1.49                 c_10]) ).
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.86/1.49  
% 7.86/1.49  ------                               Statistics
% 7.86/1.49  
% 7.86/1.49  ------ Selected
% 7.86/1.49  
% 7.86/1.49  total_time:                             0.83
% 7.86/1.49  
%------------------------------------------------------------------------------
