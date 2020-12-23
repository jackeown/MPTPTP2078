%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0492+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:26 EST 2020

% Result     : Theorem 0.90s
% Output     : CNFRefutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   45 (  84 expanded)
%              Number of clauses        :   22 (  24 expanded)
%              Number of leaves         :    5 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  188 ( 416 expanded)
%              Number of equality atoms :   29 (  65 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,X0))
        & v1_relat_1(X1) )
   => ( k3_xboole_0(k1_relat_1(sK2),sK1) != k1_relat_1(k7_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( k3_xboole_0(k1_relat_1(sK2),sK1) != k1_relat_1(k7_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f6,f14])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    k3_xboole_0(k1_relat_1(sK2),sK1) != k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_127,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_128,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
    | ~ r2_hidden(X0,k1_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_127])).

cnf(c_502,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),X0)
    | r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,X0)))
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_598,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_502])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_115,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_116,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) ),
    inference(unflattening,[status(thm)],[c_115])).

cnf(c_526,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
    | r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_142,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_10])).

cnf(c_143,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
    | r2_hidden(X0,k1_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_142])).

cnf(c_527,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
    | r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_143])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_479,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),sK1)
    | k3_xboole_0(k1_relat_1(sK2),sK1) = k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_476,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
    | r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | k3_xboole_0(k1_relat_1(sK2),sK1) = k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_473,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
    | r2_hidden(sK0(k1_relat_1(sK2),sK1,k1_relat_1(k7_relat_1(sK2,sK1))),sK1)
    | k3_xboole_0(k1_relat_1(sK2),sK1) = k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_9,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(sK2),sK1) != k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_598,c_526,c_527,c_479,c_476,c_473,c_9])).


%------------------------------------------------------------------------------
