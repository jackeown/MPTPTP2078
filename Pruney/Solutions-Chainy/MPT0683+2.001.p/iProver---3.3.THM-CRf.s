%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:26 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 340 expanded)
%              Number of clauses        :   55 (  96 expanded)
%              Number of leaves         :    6 (  62 expanded)
%              Depth                    :   17
%              Number of atoms          :  395 (1917 expanded)
%              Number of equality atoms :   83 ( 327 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1)
            & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1)
                | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1)
                  & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) != k10_relat_1(X2,k3_xboole_0(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) != k10_relat_1(X2,k3_xboole_0(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) != k10_relat_1(X2,k3_xboole_0(X0,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) != k10_relat_1(sK8,k3_xboole_0(sK6,sK7))
      & v1_funct_1(sK8)
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) != k10_relat_1(sK8,k3_xboole_0(sK6,sK7))
    & v1_funct_1(sK8)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f12,f33])).

fof(f58,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f34])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) != k10_relat_1(sK8,k3_xboole_0(sK6,sK7)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1575,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),X0)
    | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(X0,sK7))
    | ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3147,plain,
    ( r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7))
    | ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7)
    | ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK6) ),
    inference(instantiation,[status(thm)],[c_1575])).

cnf(c_3148,plain,
    ( r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7)) = iProver_top
    | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7) != iProver_top
    | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3147])).

cnf(c_19,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2))
    | ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_371,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2))
    | ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_372,plain,
    ( r2_hidden(X0,k10_relat_1(sK8,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k1_funct_1(sK8,X0),X1)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_376,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,X0),X1)
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(X0,k10_relat_1(sK8,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_372,c_24])).

cnf(c_377,plain,
    ( r2_hidden(X0,k10_relat_1(sK8,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k1_funct_1(sK8,X0),X1) ),
    inference(renaming,[status(thm)],[c_376])).

cnf(c_1604,plain,
    ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,X0))
    | ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8))
    | ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),X0) ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(c_2519,plain,
    ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))
    | ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8))
    | ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_1604])).

cnf(c_2520,plain,
    ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))) = iProver_top
    | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2519])).

cnf(c_2516,plain,
    ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK6))
    | ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8))
    | ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK6) ),
    inference(instantiation,[status(thm)],[c_1604])).

cnf(c_2517,plain,
    ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK6)) = iProver_top
    | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2516])).

cnf(c_2513,plain,
    ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7))
    | ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8))
    | ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7) ),
    inference(instantiation,[status(thm)],[c_1604])).

cnf(c_2514,plain,
    ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7)) = iProver_top
    | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2513])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2391,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7))
    | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2392,plain,
    ( r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2391])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2388,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7))
    | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2389,plain,
    ( r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2388])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_353,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_23])).

cnf(c_354,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
    | r2_hidden(k1_funct_1(sK8,X0),X1)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_358,plain,
    ( r2_hidden(k1_funct_1(sK8,X0),X1)
    | ~ r2_hidden(X0,k10_relat_1(sK8,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_24])).

cnf(c_359,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
    | r2_hidden(k1_funct_1(sK8,X0),X1) ),
    inference(renaming,[status(thm)],[c_358])).

cnf(c_1411,plain,
    ( ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))
    | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_1415,plain,
    ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))) != iProver_top
    | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1411])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_335,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_23])).

cnf(c_336,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
    | r2_hidden(X0,k1_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_340,plain,
    ( r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X0,k10_relat_1(sK8,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_336,c_24])).

cnf(c_341,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
    | r2_hidden(X0,k1_relat_1(sK8)) ),
    inference(renaming,[status(thm)],[c_340])).

cnf(c_1412,plain,
    ( ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))
    | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_1413,plain,
    ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))) != iProver_top
    | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1412])).

cnf(c_1369,plain,
    ( ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK6))
    | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK6) ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_1373,plain,
    ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1369])).

cnf(c_1333,plain,
    ( ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7))
    | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7) ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_1337,plain,
    ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1333])).

cnf(c_1334,plain,
    ( ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7))
    | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_1335,plain,
    ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7)) != iProver_top
    | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1334])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1310,plain,
    ( ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))
    | ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7))
    | ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK6))
    | k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) = k10_relat_1(sK8,k3_xboole_0(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1311,plain,
    ( k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) = k10_relat_1(sK8,k3_xboole_0(sK6,sK7))
    | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))) != iProver_top
    | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7)) != iProver_top
    | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1310])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1307,plain,
    ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))
    | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK6))
    | k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) = k10_relat_1(sK8,k3_xboole_0(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1308,plain,
    ( k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) = k10_relat_1(sK8,k3_xboole_0(sK6,sK7))
    | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))) = iProver_top
    | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1307])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1304,plain,
    ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))
    | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7))
    | k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) = k10_relat_1(sK8,k3_xboole_0(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1305,plain,
    ( k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) = k10_relat_1(sK8,k3_xboole_0(sK6,sK7))
    | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))) = iProver_top
    | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1304])).

cnf(c_22,negated_conjecture,
    ( k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) != k10_relat_1(sK8,k3_xboole_0(sK6,sK7)) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3148,c_2520,c_2517,c_2514,c_2392,c_2389,c_1415,c_1413,c_1373,c_1337,c_1335,c_1311,c_1308,c_1305,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:36:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.51/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/0.95  
% 2.51/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.51/0.95  
% 2.51/0.95  ------  iProver source info
% 2.51/0.95  
% 2.51/0.95  git: date: 2020-06-30 10:37:57 +0100
% 2.51/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.51/0.95  git: non_committed_changes: false
% 2.51/0.95  git: last_make_outside_of_git: false
% 2.51/0.95  
% 2.51/0.95  ------ 
% 2.51/0.95  
% 2.51/0.95  ------ Input Options
% 2.51/0.95  
% 2.51/0.95  --out_options                           all
% 2.51/0.95  --tptp_safe_out                         true
% 2.51/0.95  --problem_path                          ""
% 2.51/0.95  --include_path                          ""
% 2.51/0.95  --clausifier                            res/vclausify_rel
% 2.51/0.95  --clausifier_options                    --mode clausify
% 2.51/0.95  --stdin                                 false
% 2.51/0.95  --stats_out                             all
% 2.51/0.95  
% 2.51/0.95  ------ General Options
% 2.51/0.95  
% 2.51/0.95  --fof                                   false
% 2.51/0.95  --time_out_real                         305.
% 2.51/0.95  --time_out_virtual                      -1.
% 2.51/0.95  --symbol_type_check                     false
% 2.51/0.95  --clausify_out                          false
% 2.51/0.95  --sig_cnt_out                           false
% 2.51/0.95  --trig_cnt_out                          false
% 2.51/0.95  --trig_cnt_out_tolerance                1.
% 2.51/0.95  --trig_cnt_out_sk_spl                   false
% 2.51/0.95  --abstr_cl_out                          false
% 2.51/0.95  
% 2.51/0.95  ------ Global Options
% 2.51/0.95  
% 2.51/0.95  --schedule                              default
% 2.51/0.95  --add_important_lit                     false
% 2.51/0.95  --prop_solver_per_cl                    1000
% 2.51/0.95  --min_unsat_core                        false
% 2.51/0.95  --soft_assumptions                      false
% 2.51/0.95  --soft_lemma_size                       3
% 2.51/0.95  --prop_impl_unit_size                   0
% 2.51/0.95  --prop_impl_unit                        []
% 2.51/0.95  --share_sel_clauses                     true
% 2.51/0.95  --reset_solvers                         false
% 2.51/0.95  --bc_imp_inh                            [conj_cone]
% 2.51/0.95  --conj_cone_tolerance                   3.
% 2.51/0.95  --extra_neg_conj                        none
% 2.51/0.95  --large_theory_mode                     true
% 2.51/0.95  --prolific_symb_bound                   200
% 2.51/0.95  --lt_threshold                          2000
% 2.51/0.95  --clause_weak_htbl                      true
% 2.51/0.95  --gc_record_bc_elim                     false
% 2.51/0.95  
% 2.51/0.95  ------ Preprocessing Options
% 2.51/0.95  
% 2.51/0.95  --preprocessing_flag                    true
% 2.51/0.95  --time_out_prep_mult                    0.1
% 2.51/0.95  --splitting_mode                        input
% 2.51/0.95  --splitting_grd                         true
% 2.51/0.95  --splitting_cvd                         false
% 2.51/0.95  --splitting_cvd_svl                     false
% 2.51/0.95  --splitting_nvd                         32
% 2.51/0.95  --sub_typing                            true
% 2.51/0.95  --prep_gs_sim                           true
% 2.51/0.95  --prep_unflatten                        true
% 2.51/0.95  --prep_res_sim                          true
% 2.51/0.95  --prep_upred                            true
% 2.51/0.95  --prep_sem_filter                       exhaustive
% 2.51/0.95  --prep_sem_filter_out                   false
% 2.51/0.95  --pred_elim                             true
% 2.51/0.95  --res_sim_input                         true
% 2.51/0.95  --eq_ax_congr_red                       true
% 2.51/0.95  --pure_diseq_elim                       true
% 2.51/0.95  --brand_transform                       false
% 2.51/0.95  --non_eq_to_eq                          false
% 2.51/0.95  --prep_def_merge                        true
% 2.51/0.95  --prep_def_merge_prop_impl              false
% 2.51/0.95  --prep_def_merge_mbd                    true
% 2.51/0.95  --prep_def_merge_tr_red                 false
% 2.51/0.95  --prep_def_merge_tr_cl                  false
% 2.51/0.95  --smt_preprocessing                     true
% 2.51/0.95  --smt_ac_axioms                         fast
% 2.51/0.95  --preprocessed_out                      false
% 2.51/0.95  --preprocessed_stats                    false
% 2.51/0.95  
% 2.51/0.95  ------ Abstraction refinement Options
% 2.51/0.95  
% 2.51/0.95  --abstr_ref                             []
% 2.51/0.95  --abstr_ref_prep                        false
% 2.51/0.95  --abstr_ref_until_sat                   false
% 2.51/0.95  --abstr_ref_sig_restrict                funpre
% 2.51/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.51/0.95  --abstr_ref_under                       []
% 2.51/0.95  
% 2.51/0.95  ------ SAT Options
% 2.51/0.95  
% 2.51/0.95  --sat_mode                              false
% 2.51/0.95  --sat_fm_restart_options                ""
% 2.51/0.95  --sat_gr_def                            false
% 2.51/0.95  --sat_epr_types                         true
% 2.51/0.95  --sat_non_cyclic_types                  false
% 2.51/0.95  --sat_finite_models                     false
% 2.51/0.95  --sat_fm_lemmas                         false
% 2.51/0.95  --sat_fm_prep                           false
% 2.51/0.95  --sat_fm_uc_incr                        true
% 2.51/0.95  --sat_out_model                         small
% 2.51/0.95  --sat_out_clauses                       false
% 2.51/0.95  
% 2.51/0.95  ------ QBF Options
% 2.51/0.95  
% 2.51/0.95  --qbf_mode                              false
% 2.51/0.95  --qbf_elim_univ                         false
% 2.51/0.95  --qbf_dom_inst                          none
% 2.51/0.95  --qbf_dom_pre_inst                      false
% 2.51/0.95  --qbf_sk_in                             false
% 2.51/0.95  --qbf_pred_elim                         true
% 2.51/0.95  --qbf_split                             512
% 2.51/0.95  
% 2.51/0.95  ------ BMC1 Options
% 2.51/0.95  
% 2.51/0.95  --bmc1_incremental                      false
% 2.51/0.95  --bmc1_axioms                           reachable_all
% 2.51/0.95  --bmc1_min_bound                        0
% 2.51/0.95  --bmc1_max_bound                        -1
% 2.51/0.95  --bmc1_max_bound_default                -1
% 2.51/0.95  --bmc1_symbol_reachability              true
% 2.51/0.95  --bmc1_property_lemmas                  false
% 2.51/0.95  --bmc1_k_induction                      false
% 2.51/0.95  --bmc1_non_equiv_states                 false
% 2.51/0.95  --bmc1_deadlock                         false
% 2.51/0.95  --bmc1_ucm                              false
% 2.51/0.95  --bmc1_add_unsat_core                   none
% 2.51/0.95  --bmc1_unsat_core_children              false
% 2.51/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.51/0.95  --bmc1_out_stat                         full
% 2.51/0.95  --bmc1_ground_init                      false
% 2.51/0.95  --bmc1_pre_inst_next_state              false
% 2.51/0.95  --bmc1_pre_inst_state                   false
% 2.51/0.95  --bmc1_pre_inst_reach_state             false
% 2.51/0.95  --bmc1_out_unsat_core                   false
% 2.51/0.95  --bmc1_aig_witness_out                  false
% 2.51/0.95  --bmc1_verbose                          false
% 2.51/0.95  --bmc1_dump_clauses_tptp                false
% 2.51/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.51/0.95  --bmc1_dump_file                        -
% 2.51/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.51/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.51/0.95  --bmc1_ucm_extend_mode                  1
% 2.51/0.95  --bmc1_ucm_init_mode                    2
% 2.51/0.95  --bmc1_ucm_cone_mode                    none
% 2.51/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.51/0.95  --bmc1_ucm_relax_model                  4
% 2.51/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.51/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.51/0.95  --bmc1_ucm_layered_model                none
% 2.51/0.95  --bmc1_ucm_max_lemma_size               10
% 2.51/0.95  
% 2.51/0.95  ------ AIG Options
% 2.51/0.95  
% 2.51/0.95  --aig_mode                              false
% 2.51/0.95  
% 2.51/0.95  ------ Instantiation Options
% 2.51/0.95  
% 2.51/0.95  --instantiation_flag                    true
% 2.51/0.95  --inst_sos_flag                         false
% 2.51/0.95  --inst_sos_phase                        true
% 2.51/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.51/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.51/0.95  --inst_lit_sel_side                     num_symb
% 2.51/0.95  --inst_solver_per_active                1400
% 2.51/0.95  --inst_solver_calls_frac                1.
% 2.51/0.95  --inst_passive_queue_type               priority_queues
% 2.51/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.51/0.95  --inst_passive_queues_freq              [25;2]
% 2.51/0.95  --inst_dismatching                      true
% 2.51/0.95  --inst_eager_unprocessed_to_passive     true
% 2.51/0.95  --inst_prop_sim_given                   true
% 2.51/0.95  --inst_prop_sim_new                     false
% 2.51/0.95  --inst_subs_new                         false
% 2.51/0.95  --inst_eq_res_simp                      false
% 2.51/0.95  --inst_subs_given                       false
% 2.51/0.95  --inst_orphan_elimination               true
% 2.51/0.95  --inst_learning_loop_flag               true
% 2.51/0.95  --inst_learning_start                   3000
% 2.51/0.95  --inst_learning_factor                  2
% 2.51/0.95  --inst_start_prop_sim_after_learn       3
% 2.51/0.95  --inst_sel_renew                        solver
% 2.51/0.95  --inst_lit_activity_flag                true
% 2.51/0.95  --inst_restr_to_given                   false
% 2.51/0.95  --inst_activity_threshold               500
% 2.51/0.95  --inst_out_proof                        true
% 2.51/0.95  
% 2.51/0.95  ------ Resolution Options
% 2.51/0.95  
% 2.51/0.95  --resolution_flag                       true
% 2.51/0.95  --res_lit_sel                           adaptive
% 2.51/0.95  --res_lit_sel_side                      none
% 2.51/0.95  --res_ordering                          kbo
% 2.51/0.95  --res_to_prop_solver                    active
% 2.51/0.95  --res_prop_simpl_new                    false
% 2.51/0.95  --res_prop_simpl_given                  true
% 2.51/0.95  --res_passive_queue_type                priority_queues
% 2.51/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.51/0.95  --res_passive_queues_freq               [15;5]
% 2.51/0.95  --res_forward_subs                      full
% 2.51/0.95  --res_backward_subs                     full
% 2.51/0.95  --res_forward_subs_resolution           true
% 2.51/0.95  --res_backward_subs_resolution          true
% 2.51/0.95  --res_orphan_elimination                true
% 2.51/0.95  --res_time_limit                        2.
% 2.51/0.95  --res_out_proof                         true
% 2.51/0.95  
% 2.51/0.95  ------ Superposition Options
% 2.51/0.95  
% 2.51/0.95  --superposition_flag                    true
% 2.51/0.95  --sup_passive_queue_type                priority_queues
% 2.51/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.51/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.51/0.95  --demod_completeness_check              fast
% 2.51/0.95  --demod_use_ground                      true
% 2.51/0.95  --sup_to_prop_solver                    passive
% 2.51/0.95  --sup_prop_simpl_new                    true
% 2.51/0.95  --sup_prop_simpl_given                  true
% 2.51/0.95  --sup_fun_splitting                     false
% 2.51/0.95  --sup_smt_interval                      50000
% 2.51/0.95  
% 2.51/0.95  ------ Superposition Simplification Setup
% 2.51/0.95  
% 2.51/0.95  --sup_indices_passive                   []
% 2.51/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.51/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.95  --sup_full_bw                           [BwDemod]
% 2.51/0.95  --sup_immed_triv                        [TrivRules]
% 2.51/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.51/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.95  --sup_immed_bw_main                     []
% 2.51/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.51/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/0.95  
% 2.51/0.95  ------ Combination Options
% 2.51/0.95  
% 2.51/0.95  --comb_res_mult                         3
% 2.51/0.95  --comb_sup_mult                         2
% 2.51/0.95  --comb_inst_mult                        10
% 2.51/0.95  
% 2.51/0.95  ------ Debug Options
% 2.51/0.95  
% 2.51/0.95  --dbg_backtrace                         false
% 2.51/0.95  --dbg_dump_prop_clauses                 false
% 2.51/0.95  --dbg_dump_prop_clauses_file            -
% 2.51/0.95  --dbg_out_stat                          false
% 2.51/0.95  ------ Parsing...
% 2.51/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.51/0.95  
% 2.51/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.51/0.95  
% 2.51/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.51/0.95  
% 2.51/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.51/0.95  ------ Proving...
% 2.51/0.95  ------ Problem Properties 
% 2.51/0.95  
% 2.51/0.95  
% 2.51/0.95  clauses                                 22
% 2.51/0.95  conjectures                             1
% 2.51/0.95  EPR                                     0
% 2.51/0.95  Horn                                    16
% 2.51/0.95  unary                                   1
% 2.51/0.95  binary                                  9
% 2.51/0.95  lits                                    58
% 2.51/0.95  lits eq                                 10
% 2.51/0.95  fd_pure                                 0
% 2.51/0.95  fd_pseudo                               0
% 2.51/0.95  fd_cond                                 0
% 2.51/0.95  fd_pseudo_cond                          9
% 2.51/0.95  AC symbols                              0
% 2.51/0.95  
% 2.51/0.95  ------ Schedule dynamic 5 is on 
% 2.51/0.95  
% 2.51/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.51/0.95  
% 2.51/0.95  
% 2.51/0.95  ------ 
% 2.51/0.95  Current options:
% 2.51/0.95  ------ 
% 2.51/0.95  
% 2.51/0.95  ------ Input Options
% 2.51/0.95  
% 2.51/0.95  --out_options                           all
% 2.51/0.95  --tptp_safe_out                         true
% 2.51/0.95  --problem_path                          ""
% 2.51/0.95  --include_path                          ""
% 2.51/0.95  --clausifier                            res/vclausify_rel
% 2.51/0.95  --clausifier_options                    --mode clausify
% 2.51/0.95  --stdin                                 false
% 2.51/0.95  --stats_out                             all
% 2.51/0.95  
% 2.51/0.95  ------ General Options
% 2.51/0.95  
% 2.51/0.95  --fof                                   false
% 2.51/0.95  --time_out_real                         305.
% 2.51/0.95  --time_out_virtual                      -1.
% 2.51/0.95  --symbol_type_check                     false
% 2.51/0.95  --clausify_out                          false
% 2.51/0.95  --sig_cnt_out                           false
% 2.51/0.95  --trig_cnt_out                          false
% 2.51/0.95  --trig_cnt_out_tolerance                1.
% 2.51/0.95  --trig_cnt_out_sk_spl                   false
% 2.51/0.95  --abstr_cl_out                          false
% 2.51/0.95  
% 2.51/0.95  ------ Global Options
% 2.51/0.95  
% 2.51/0.95  --schedule                              default
% 2.51/0.95  --add_important_lit                     false
% 2.51/0.95  --prop_solver_per_cl                    1000
% 2.51/0.95  --min_unsat_core                        false
% 2.51/0.95  --soft_assumptions                      false
% 2.51/0.95  --soft_lemma_size                       3
% 2.51/0.95  --prop_impl_unit_size                   0
% 2.51/0.95  --prop_impl_unit                        []
% 2.51/0.95  --share_sel_clauses                     true
% 2.51/0.95  --reset_solvers                         false
% 2.51/0.95  --bc_imp_inh                            [conj_cone]
% 2.51/0.95  --conj_cone_tolerance                   3.
% 2.51/0.95  --extra_neg_conj                        none
% 2.51/0.95  --large_theory_mode                     true
% 2.51/0.95  --prolific_symb_bound                   200
% 2.51/0.95  --lt_threshold                          2000
% 2.51/0.95  --clause_weak_htbl                      true
% 2.51/0.95  --gc_record_bc_elim                     false
% 2.51/0.95  
% 2.51/0.95  ------ Preprocessing Options
% 2.51/0.95  
% 2.51/0.95  --preprocessing_flag                    true
% 2.51/0.95  --time_out_prep_mult                    0.1
% 2.51/0.95  --splitting_mode                        input
% 2.51/0.95  --splitting_grd                         true
% 2.51/0.95  --splitting_cvd                         false
% 2.51/0.95  --splitting_cvd_svl                     false
% 2.51/0.95  --splitting_nvd                         32
% 2.51/0.95  --sub_typing                            true
% 2.51/0.95  --prep_gs_sim                           true
% 2.51/0.95  --prep_unflatten                        true
% 2.51/0.95  --prep_res_sim                          true
% 2.51/0.95  --prep_upred                            true
% 2.51/0.95  --prep_sem_filter                       exhaustive
% 2.51/0.95  --prep_sem_filter_out                   false
% 2.51/0.95  --pred_elim                             true
% 2.51/0.95  --res_sim_input                         true
% 2.51/0.95  --eq_ax_congr_red                       true
% 2.51/0.95  --pure_diseq_elim                       true
% 2.51/0.95  --brand_transform                       false
% 2.51/0.95  --non_eq_to_eq                          false
% 2.51/0.95  --prep_def_merge                        true
% 2.51/0.95  --prep_def_merge_prop_impl              false
% 2.51/0.95  --prep_def_merge_mbd                    true
% 2.51/0.95  --prep_def_merge_tr_red                 false
% 2.51/0.95  --prep_def_merge_tr_cl                  false
% 2.51/0.95  --smt_preprocessing                     true
% 2.51/0.95  --smt_ac_axioms                         fast
% 2.51/0.95  --preprocessed_out                      false
% 2.51/0.95  --preprocessed_stats                    false
% 2.51/0.95  
% 2.51/0.95  ------ Abstraction refinement Options
% 2.51/0.95  
% 2.51/0.95  --abstr_ref                             []
% 2.51/0.95  --abstr_ref_prep                        false
% 2.51/0.95  --abstr_ref_until_sat                   false
% 2.51/0.95  --abstr_ref_sig_restrict                funpre
% 2.51/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.51/0.95  --abstr_ref_under                       []
% 2.51/0.95  
% 2.51/0.95  ------ SAT Options
% 2.51/0.95  
% 2.51/0.95  --sat_mode                              false
% 2.51/0.95  --sat_fm_restart_options                ""
% 2.51/0.95  --sat_gr_def                            false
% 2.51/0.95  --sat_epr_types                         true
% 2.51/0.95  --sat_non_cyclic_types                  false
% 2.51/0.95  --sat_finite_models                     false
% 2.51/0.95  --sat_fm_lemmas                         false
% 2.51/0.95  --sat_fm_prep                           false
% 2.51/0.95  --sat_fm_uc_incr                        true
% 2.51/0.95  --sat_out_model                         small
% 2.51/0.95  --sat_out_clauses                       false
% 2.51/0.95  
% 2.51/0.95  ------ QBF Options
% 2.51/0.95  
% 2.51/0.95  --qbf_mode                              false
% 2.51/0.95  --qbf_elim_univ                         false
% 2.51/0.95  --qbf_dom_inst                          none
% 2.51/0.95  --qbf_dom_pre_inst                      false
% 2.51/0.95  --qbf_sk_in                             false
% 2.51/0.95  --qbf_pred_elim                         true
% 2.51/0.95  --qbf_split                             512
% 2.51/0.95  
% 2.51/0.95  ------ BMC1 Options
% 2.51/0.95  
% 2.51/0.95  --bmc1_incremental                      false
% 2.51/0.95  --bmc1_axioms                           reachable_all
% 2.51/0.95  --bmc1_min_bound                        0
% 2.51/0.95  --bmc1_max_bound                        -1
% 2.51/0.95  --bmc1_max_bound_default                -1
% 2.51/0.95  --bmc1_symbol_reachability              true
% 2.51/0.95  --bmc1_property_lemmas                  false
% 2.51/0.95  --bmc1_k_induction                      false
% 2.51/0.95  --bmc1_non_equiv_states                 false
% 2.51/0.95  --bmc1_deadlock                         false
% 2.51/0.95  --bmc1_ucm                              false
% 2.51/0.95  --bmc1_add_unsat_core                   none
% 2.51/0.95  --bmc1_unsat_core_children              false
% 2.51/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.51/0.95  --bmc1_out_stat                         full
% 2.51/0.95  --bmc1_ground_init                      false
% 2.51/0.95  --bmc1_pre_inst_next_state              false
% 2.51/0.95  --bmc1_pre_inst_state                   false
% 2.51/0.95  --bmc1_pre_inst_reach_state             false
% 2.51/0.95  --bmc1_out_unsat_core                   false
% 2.51/0.95  --bmc1_aig_witness_out                  false
% 2.51/0.95  --bmc1_verbose                          false
% 2.51/0.95  --bmc1_dump_clauses_tptp                false
% 2.51/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.51/0.95  --bmc1_dump_file                        -
% 2.51/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.51/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.51/0.95  --bmc1_ucm_extend_mode                  1
% 2.51/0.95  --bmc1_ucm_init_mode                    2
% 2.51/0.95  --bmc1_ucm_cone_mode                    none
% 2.51/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.51/0.95  --bmc1_ucm_relax_model                  4
% 2.51/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.51/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.51/0.95  --bmc1_ucm_layered_model                none
% 2.51/0.95  --bmc1_ucm_max_lemma_size               10
% 2.51/0.95  
% 2.51/0.95  ------ AIG Options
% 2.51/0.95  
% 2.51/0.95  --aig_mode                              false
% 2.51/0.95  
% 2.51/0.95  ------ Instantiation Options
% 2.51/0.95  
% 2.51/0.95  --instantiation_flag                    true
% 2.51/0.95  --inst_sos_flag                         false
% 2.51/0.95  --inst_sos_phase                        true
% 2.51/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.51/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.51/0.95  --inst_lit_sel_side                     none
% 2.51/0.95  --inst_solver_per_active                1400
% 2.51/0.95  --inst_solver_calls_frac                1.
% 2.51/0.95  --inst_passive_queue_type               priority_queues
% 2.51/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.51/0.95  --inst_passive_queues_freq              [25;2]
% 2.51/0.95  --inst_dismatching                      true
% 2.51/0.95  --inst_eager_unprocessed_to_passive     true
% 2.51/0.95  --inst_prop_sim_given                   true
% 2.51/0.95  --inst_prop_sim_new                     false
% 2.51/0.95  --inst_subs_new                         false
% 2.51/0.95  --inst_eq_res_simp                      false
% 2.51/0.95  --inst_subs_given                       false
% 2.51/0.95  --inst_orphan_elimination               true
% 2.51/0.95  --inst_learning_loop_flag               true
% 2.51/0.95  --inst_learning_start                   3000
% 2.51/0.95  --inst_learning_factor                  2
% 2.51/0.95  --inst_start_prop_sim_after_learn       3
% 2.51/0.95  --inst_sel_renew                        solver
% 2.51/0.95  --inst_lit_activity_flag                true
% 2.51/0.95  --inst_restr_to_given                   false
% 2.51/0.95  --inst_activity_threshold               500
% 2.51/0.95  --inst_out_proof                        true
% 2.51/0.95  
% 2.51/0.95  ------ Resolution Options
% 2.51/0.95  
% 2.51/0.95  --resolution_flag                       false
% 2.51/0.95  --res_lit_sel                           adaptive
% 2.51/0.95  --res_lit_sel_side                      none
% 2.51/0.95  --res_ordering                          kbo
% 2.51/0.95  --res_to_prop_solver                    active
% 2.51/0.95  --res_prop_simpl_new                    false
% 2.51/0.95  --res_prop_simpl_given                  true
% 2.51/0.95  --res_passive_queue_type                priority_queues
% 2.51/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.51/0.95  --res_passive_queues_freq               [15;5]
% 2.51/0.95  --res_forward_subs                      full
% 2.51/0.95  --res_backward_subs                     full
% 2.51/0.95  --res_forward_subs_resolution           true
% 2.51/0.95  --res_backward_subs_resolution          true
% 2.51/0.95  --res_orphan_elimination                true
% 2.51/0.95  --res_time_limit                        2.
% 2.51/0.95  --res_out_proof                         true
% 2.51/0.95  
% 2.51/0.95  ------ Superposition Options
% 2.51/0.95  
% 2.51/0.95  --superposition_flag                    true
% 2.51/0.95  --sup_passive_queue_type                priority_queues
% 2.51/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.51/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.51/0.95  --demod_completeness_check              fast
% 2.51/0.95  --demod_use_ground                      true
% 2.51/0.95  --sup_to_prop_solver                    passive
% 2.51/0.95  --sup_prop_simpl_new                    true
% 2.51/0.95  --sup_prop_simpl_given                  true
% 2.51/0.95  --sup_fun_splitting                     false
% 2.51/0.95  --sup_smt_interval                      50000
% 2.51/0.95  
% 2.51/0.95  ------ Superposition Simplification Setup
% 2.51/0.95  
% 2.51/0.95  --sup_indices_passive                   []
% 2.51/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.51/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.95  --sup_full_bw                           [BwDemod]
% 2.51/0.95  --sup_immed_triv                        [TrivRules]
% 2.51/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.51/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.95  --sup_immed_bw_main                     []
% 2.51/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.51/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/0.95  
% 2.51/0.95  ------ Combination Options
% 2.51/0.95  
% 2.51/0.95  --comb_res_mult                         3
% 2.51/0.95  --comb_sup_mult                         2
% 2.51/0.95  --comb_inst_mult                        10
% 2.51/0.95  
% 2.51/0.95  ------ Debug Options
% 2.51/0.95  
% 2.51/0.95  --dbg_backtrace                         false
% 2.51/0.95  --dbg_dump_prop_clauses                 false
% 2.51/0.95  --dbg_dump_prop_clauses_file            -
% 2.51/0.95  --dbg_out_stat                          false
% 2.51/0.95  
% 2.51/0.95  
% 2.51/0.95  
% 2.51/0.95  
% 2.51/0.95  ------ Proving...
% 2.51/0.95  
% 2.51/0.95  
% 2.51/0.95  % SZS status Theorem for theBenchmark.p
% 2.51/0.95  
% 2.51/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 2.51/0.95  
% 2.51/0.95  fof(f1,axiom,(
% 2.51/0.95    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.51/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.95  
% 2.51/0.95  fof(f13,plain,(
% 2.51/0.95    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.51/0.95    inference(nnf_transformation,[],[f1])).
% 2.51/0.95  
% 2.51/0.95  fof(f14,plain,(
% 2.51/0.95    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.51/0.95    inference(flattening,[],[f13])).
% 2.51/0.95  
% 2.51/0.95  fof(f15,plain,(
% 2.51/0.95    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.51/0.95    inference(rectify,[],[f14])).
% 2.51/0.95  
% 2.51/0.95  fof(f16,plain,(
% 2.51/0.95    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.51/0.95    introduced(choice_axiom,[])).
% 2.51/0.95  
% 2.51/0.95  fof(f17,plain,(
% 2.51/0.95    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.51/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 2.51/0.95  
% 2.51/0.95  fof(f37,plain,(
% 2.51/0.95    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 2.51/0.95    inference(cnf_transformation,[],[f17])).
% 2.51/0.95  
% 2.51/0.95  fof(f60,plain,(
% 2.51/0.95    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.51/0.95    inference(equality_resolution,[],[f37])).
% 2.51/0.95  
% 2.51/0.95  fof(f4,axiom,(
% 2.51/0.95    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.51/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.95  
% 2.51/0.95  fof(f9,plain,(
% 2.51/0.95    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.51/0.95    inference(ennf_transformation,[],[f4])).
% 2.51/0.95  
% 2.51/0.95  fof(f10,plain,(
% 2.51/0.95    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/0.95    inference(flattening,[],[f9])).
% 2.51/0.95  
% 2.51/0.95  fof(f28,plain,(
% 2.51/0.95    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/0.95    inference(nnf_transformation,[],[f10])).
% 2.51/0.95  
% 2.51/0.95  fof(f29,plain,(
% 2.51/0.95    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/0.95    inference(flattening,[],[f28])).
% 2.51/0.95  
% 2.51/0.95  fof(f30,plain,(
% 2.51/0.95    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/0.95    inference(rectify,[],[f29])).
% 2.51/0.95  
% 2.51/0.95  fof(f31,plain,(
% 2.51/0.95    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1) | ~r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.51/0.95    introduced(choice_axiom,[])).
% 2.51/0.95  
% 2.51/0.95  fof(f32,plain,(
% 2.51/0.95    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((~r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1) | ~r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.51/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 2.51/0.95  
% 2.51/0.95  fof(f53,plain,(
% 2.51/0.95    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0)) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.51/0.95    inference(cnf_transformation,[],[f32])).
% 2.51/0.95  
% 2.51/0.95  fof(f66,plain,(
% 2.51/0.95    ( ! [X4,X0,X1] : (r2_hidden(X4,k10_relat_1(X0,X1)) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.51/0.95    inference(equality_resolution,[],[f53])).
% 2.51/0.95  
% 2.51/0.95  fof(f5,conjecture,(
% 2.51/0.95    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)))),
% 2.51/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.51/0.95  
% 2.51/0.95  fof(f6,negated_conjecture,(
% 2.51/0.95    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k3_xboole_0(X0,X1)))),
% 2.51/0.95    inference(negated_conjecture,[],[f5])).
% 2.51/0.95  
% 2.51/0.95  fof(f11,plain,(
% 2.51/0.95    ? [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) != k10_relat_1(X2,k3_xboole_0(X0,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 2.51/0.95    inference(ennf_transformation,[],[f6])).
% 2.51/0.95  
% 2.51/0.95  fof(f12,plain,(
% 2.51/0.95    ? [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) != k10_relat_1(X2,k3_xboole_0(X0,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.51/0.95    inference(flattening,[],[f11])).
% 2.51/0.95  
% 2.51/0.95  fof(f33,plain,(
% 2.51/0.95    ? [X0,X1,X2] : (k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) != k10_relat_1(X2,k3_xboole_0(X0,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) != k10_relat_1(sK8,k3_xboole_0(sK6,sK7)) & v1_funct_1(sK8) & v1_relat_1(sK8))),
% 2.51/0.95    introduced(choice_axiom,[])).
% 2.51/0.95  
% 2.51/0.95  fof(f34,plain,(
% 2.51/0.95    k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) != k10_relat_1(sK8,k3_xboole_0(sK6,sK7)) & v1_funct_1(sK8) & v1_relat_1(sK8)),
% 2.51/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f12,f33])).
% 2.51/0.95  
% 2.51/0.95  fof(f58,plain,(
% 2.51/0.95    v1_funct_1(sK8)),
% 2.51/0.95    inference(cnf_transformation,[],[f34])).
% 2.51/0.95  
% 2.51/0.95  fof(f57,plain,(
% 2.51/0.95    v1_relat_1(sK8)),
% 2.51/0.95    inference(cnf_transformation,[],[f34])).
% 2.51/0.95  
% 2.51/0.95  fof(f35,plain,(
% 2.51/0.95    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.51/0.95    inference(cnf_transformation,[],[f17])).
% 2.51/0.95  
% 2.51/0.95  fof(f62,plain,(
% 2.51/0.95    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 2.51/0.95    inference(equality_resolution,[],[f35])).
% 2.51/0.95  
% 2.51/0.95  fof(f36,plain,(
% 2.51/0.95    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.51/0.95    inference(cnf_transformation,[],[f17])).
% 2.51/0.95  
% 2.51/0.95  fof(f61,plain,(
% 2.51/0.95    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 2.51/0.95    inference(equality_resolution,[],[f36])).
% 2.51/0.95  
% 2.51/0.95  fof(f52,plain,(
% 2.51/0.95    ( ! [X4,X2,X0,X1] : (r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.51/0.95    inference(cnf_transformation,[],[f32])).
% 2.51/0.95  
% 2.51/0.95  fof(f67,plain,(
% 2.51/0.95    ( ! [X4,X0,X1] : (r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.51/0.95    inference(equality_resolution,[],[f52])).
% 2.51/0.95  
% 2.51/0.95  fof(f51,plain,(
% 2.51/0.95    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.51/0.95    inference(cnf_transformation,[],[f32])).
% 2.51/0.95  
% 2.51/0.95  fof(f68,plain,(
% 2.51/0.95    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.51/0.95    inference(equality_resolution,[],[f51])).
% 2.51/0.95  
% 2.51/0.95  fof(f40,plain,(
% 2.51/0.95    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.51/0.95    inference(cnf_transformation,[],[f17])).
% 2.51/0.95  
% 2.51/0.95  fof(f38,plain,(
% 2.51/0.95    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.51/0.95    inference(cnf_transformation,[],[f17])).
% 2.51/0.95  
% 2.51/0.95  fof(f39,plain,(
% 2.51/0.95    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.51/0.95    inference(cnf_transformation,[],[f17])).
% 2.51/0.95  
% 2.51/0.95  fof(f59,plain,(
% 2.51/0.95    k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) != k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),
% 2.51/0.95    inference(cnf_transformation,[],[f34])).
% 2.51/0.95  
% 2.51/0.95  cnf(c_3,plain,
% 2.51/0.95      ( ~ r2_hidden(X0,X1)
% 2.51/0.95      | ~ r2_hidden(X0,X2)
% 2.51/0.95      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 2.51/0.95      inference(cnf_transformation,[],[f60]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1575,plain,
% 2.51/0.95      ( ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),X0)
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(X0,sK7))
% 2.51/0.95      | ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7) ),
% 2.51/0.95      inference(instantiation,[status(thm)],[c_3]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_3147,plain,
% 2.51/0.95      ( r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7))
% 2.51/0.95      | ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7)
% 2.51/0.95      | ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK6) ),
% 2.51/0.95      inference(instantiation,[status(thm)],[c_1575]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_3148,plain,
% 2.51/0.95      ( r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7)) = iProver_top
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7) != iProver_top
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK6) != iProver_top ),
% 2.51/0.95      inference(predicate_to_equality,[status(thm)],[c_3147]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_19,plain,
% 2.51/0.95      ( r2_hidden(X0,k10_relat_1(X1,X2))
% 2.51/0.95      | ~ r2_hidden(X0,k1_relat_1(X1))
% 2.51/0.95      | ~ r2_hidden(k1_funct_1(X1,X0),X2)
% 2.51/0.95      | ~ v1_funct_1(X1)
% 2.51/0.95      | ~ v1_relat_1(X1) ),
% 2.51/0.95      inference(cnf_transformation,[],[f66]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_23,negated_conjecture,
% 2.51/0.95      ( v1_funct_1(sK8) ),
% 2.51/0.95      inference(cnf_transformation,[],[f58]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_371,plain,
% 2.51/0.95      ( r2_hidden(X0,k10_relat_1(X1,X2))
% 2.51/0.95      | ~ r2_hidden(X0,k1_relat_1(X1))
% 2.51/0.95      | ~ r2_hidden(k1_funct_1(X1,X0),X2)
% 2.51/0.95      | ~ v1_relat_1(X1)
% 2.51/0.95      | sK8 != X1 ),
% 2.51/0.95      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_372,plain,
% 2.51/0.95      ( r2_hidden(X0,k10_relat_1(sK8,X1))
% 2.51/0.95      | ~ r2_hidden(X0,k1_relat_1(sK8))
% 2.51/0.95      | ~ r2_hidden(k1_funct_1(sK8,X0),X1)
% 2.51/0.95      | ~ v1_relat_1(sK8) ),
% 2.51/0.95      inference(unflattening,[status(thm)],[c_371]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_24,negated_conjecture,
% 2.51/0.95      ( v1_relat_1(sK8) ),
% 2.51/0.95      inference(cnf_transformation,[],[f57]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_376,plain,
% 2.51/0.95      ( ~ r2_hidden(k1_funct_1(sK8,X0),X1)
% 2.51/0.95      | ~ r2_hidden(X0,k1_relat_1(sK8))
% 2.51/0.95      | r2_hidden(X0,k10_relat_1(sK8,X1)) ),
% 2.51/0.95      inference(global_propositional_subsumption,
% 2.51/0.95                [status(thm)],
% 2.51/0.95                [c_372,c_24]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_377,plain,
% 2.51/0.95      ( r2_hidden(X0,k10_relat_1(sK8,X1))
% 2.51/0.95      | ~ r2_hidden(X0,k1_relat_1(sK8))
% 2.51/0.95      | ~ r2_hidden(k1_funct_1(sK8,X0),X1) ),
% 2.51/0.95      inference(renaming,[status(thm)],[c_376]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1604,plain,
% 2.51/0.95      ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,X0))
% 2.51/0.95      | ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8))
% 2.51/0.95      | ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),X0) ),
% 2.51/0.95      inference(instantiation,[status(thm)],[c_377]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_2519,plain,
% 2.51/0.95      ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))
% 2.51/0.95      | ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8))
% 2.51/0.95      | ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7)) ),
% 2.51/0.95      inference(instantiation,[status(thm)],[c_1604]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_2520,plain,
% 2.51/0.95      ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))) = iProver_top
% 2.51/0.95      | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8)) != iProver_top
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7)) != iProver_top ),
% 2.51/0.95      inference(predicate_to_equality,[status(thm)],[c_2519]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_2516,plain,
% 2.51/0.95      ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK6))
% 2.51/0.95      | ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8))
% 2.51/0.95      | ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK6) ),
% 2.51/0.95      inference(instantiation,[status(thm)],[c_1604]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_2517,plain,
% 2.51/0.95      ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK6)) = iProver_top
% 2.51/0.95      | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8)) != iProver_top
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK6) != iProver_top ),
% 2.51/0.95      inference(predicate_to_equality,[status(thm)],[c_2516]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_2513,plain,
% 2.51/0.95      ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7))
% 2.51/0.95      | ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8))
% 2.51/0.95      | ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7) ),
% 2.51/0.95      inference(instantiation,[status(thm)],[c_1604]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_2514,plain,
% 2.51/0.95      ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7)) = iProver_top
% 2.51/0.95      | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8)) != iProver_top
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7) != iProver_top ),
% 2.51/0.95      inference(predicate_to_equality,[status(thm)],[c_2513]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_5,plain,
% 2.51/0.95      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 2.51/0.95      inference(cnf_transformation,[],[f62]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_2391,plain,
% 2.51/0.95      ( ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7))
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK6) ),
% 2.51/0.95      inference(instantiation,[status(thm)],[c_5]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_2392,plain,
% 2.51/0.95      ( r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7)) != iProver_top
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK6) = iProver_top ),
% 2.51/0.95      inference(predicate_to_equality,[status(thm)],[c_2391]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_4,plain,
% 2.51/0.95      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 2.51/0.95      inference(cnf_transformation,[],[f61]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_2388,plain,
% 2.51/0.95      ( ~ r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7))
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7) ),
% 2.51/0.95      inference(instantiation,[status(thm)],[c_4]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_2389,plain,
% 2.51/0.95      ( r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7)) != iProver_top
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7) = iProver_top ),
% 2.51/0.95      inference(predicate_to_equality,[status(thm)],[c_2388]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_20,plain,
% 2.51/0.95      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 2.51/0.95      | r2_hidden(k1_funct_1(X1,X0),X2)
% 2.51/0.95      | ~ v1_funct_1(X1)
% 2.51/0.95      | ~ v1_relat_1(X1) ),
% 2.51/0.95      inference(cnf_transformation,[],[f67]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_353,plain,
% 2.51/0.95      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 2.51/0.95      | r2_hidden(k1_funct_1(X1,X0),X2)
% 2.51/0.95      | ~ v1_relat_1(X1)
% 2.51/0.95      | sK8 != X1 ),
% 2.51/0.95      inference(resolution_lifted,[status(thm)],[c_20,c_23]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_354,plain,
% 2.51/0.95      ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,X0),X1)
% 2.51/0.95      | ~ v1_relat_1(sK8) ),
% 2.51/0.95      inference(unflattening,[status(thm)],[c_353]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_358,plain,
% 2.51/0.95      ( r2_hidden(k1_funct_1(sK8,X0),X1)
% 2.51/0.95      | ~ r2_hidden(X0,k10_relat_1(sK8,X1)) ),
% 2.51/0.95      inference(global_propositional_subsumption,
% 2.51/0.95                [status(thm)],
% 2.51/0.95                [c_354,c_24]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_359,plain,
% 2.51/0.95      ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,X0),X1) ),
% 2.51/0.95      inference(renaming,[status(thm)],[c_358]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1411,plain,
% 2.51/0.95      ( ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7)) ),
% 2.51/0.95      inference(instantiation,[status(thm)],[c_359]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1415,plain,
% 2.51/0.95      ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))) != iProver_top
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),k3_xboole_0(sK6,sK7)) = iProver_top ),
% 2.51/0.95      inference(predicate_to_equality,[status(thm)],[c_1411]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_21,plain,
% 2.51/0.95      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 2.51/0.95      | r2_hidden(X0,k1_relat_1(X1))
% 2.51/0.95      | ~ v1_funct_1(X1)
% 2.51/0.95      | ~ v1_relat_1(X1) ),
% 2.51/0.95      inference(cnf_transformation,[],[f68]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_335,plain,
% 2.51/0.95      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 2.51/0.95      | r2_hidden(X0,k1_relat_1(X1))
% 2.51/0.95      | ~ v1_relat_1(X1)
% 2.51/0.95      | sK8 != X1 ),
% 2.51/0.95      inference(resolution_lifted,[status(thm)],[c_21,c_23]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_336,plain,
% 2.51/0.95      ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
% 2.51/0.95      | r2_hidden(X0,k1_relat_1(sK8))
% 2.51/0.95      | ~ v1_relat_1(sK8) ),
% 2.51/0.95      inference(unflattening,[status(thm)],[c_335]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_340,plain,
% 2.51/0.95      ( r2_hidden(X0,k1_relat_1(sK8))
% 2.51/0.95      | ~ r2_hidden(X0,k10_relat_1(sK8,X1)) ),
% 2.51/0.95      inference(global_propositional_subsumption,
% 2.51/0.95                [status(thm)],
% 2.51/0.95                [c_336,c_24]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_341,plain,
% 2.51/0.95      ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
% 2.51/0.95      | r2_hidden(X0,k1_relat_1(sK8)) ),
% 2.51/0.95      inference(renaming,[status(thm)],[c_340]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1412,plain,
% 2.51/0.95      ( ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))
% 2.51/0.95      | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8)) ),
% 2.51/0.95      inference(instantiation,[status(thm)],[c_341]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1413,plain,
% 2.51/0.95      ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))) != iProver_top
% 2.51/0.95      | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8)) = iProver_top ),
% 2.51/0.95      inference(predicate_to_equality,[status(thm)],[c_1412]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1369,plain,
% 2.51/0.95      ( ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK6))
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK6) ),
% 2.51/0.95      inference(instantiation,[status(thm)],[c_359]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1373,plain,
% 2.51/0.95      ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK6)) != iProver_top
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK6) = iProver_top ),
% 2.51/0.95      inference(predicate_to_equality,[status(thm)],[c_1369]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1333,plain,
% 2.51/0.95      ( ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7))
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7) ),
% 2.51/0.95      inference(instantiation,[status(thm)],[c_359]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1337,plain,
% 2.51/0.95      ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7)) != iProver_top
% 2.51/0.95      | r2_hidden(k1_funct_1(sK8,sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))),sK7) = iProver_top ),
% 2.51/0.95      inference(predicate_to_equality,[status(thm)],[c_1333]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1334,plain,
% 2.51/0.95      ( ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7))
% 2.51/0.95      | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8)) ),
% 2.51/0.95      inference(instantiation,[status(thm)],[c_341]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1335,plain,
% 2.51/0.95      ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7)) != iProver_top
% 2.51/0.95      | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k1_relat_1(sK8)) = iProver_top ),
% 2.51/0.95      inference(predicate_to_equality,[status(thm)],[c_1334]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_0,plain,
% 2.51/0.95      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 2.51/0.95      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 2.51/0.95      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.51/0.95      | k3_xboole_0(X0,X1) = X2 ),
% 2.51/0.95      inference(cnf_transformation,[],[f40]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1310,plain,
% 2.51/0.95      ( ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))
% 2.51/0.95      | ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7))
% 2.51/0.95      | ~ r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK6))
% 2.51/0.95      | k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) = k10_relat_1(sK8,k3_xboole_0(sK6,sK7)) ),
% 2.51/0.95      inference(instantiation,[status(thm)],[c_0]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1311,plain,
% 2.51/0.95      ( k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) = k10_relat_1(sK8,k3_xboole_0(sK6,sK7))
% 2.51/0.95      | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))) != iProver_top
% 2.51/0.95      | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7)) != iProver_top
% 2.51/0.95      | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK6)) != iProver_top ),
% 2.51/0.95      inference(predicate_to_equality,[status(thm)],[c_1310]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_2,plain,
% 2.51/0.95      ( r2_hidden(sK0(X0,X1,X2),X0)
% 2.51/0.95      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.51/0.95      | k3_xboole_0(X0,X1) = X2 ),
% 2.51/0.95      inference(cnf_transformation,[],[f38]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1307,plain,
% 2.51/0.95      ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))
% 2.51/0.95      | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK6))
% 2.51/0.95      | k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) = k10_relat_1(sK8,k3_xboole_0(sK6,sK7)) ),
% 2.51/0.95      inference(instantiation,[status(thm)],[c_2]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1308,plain,
% 2.51/0.95      ( k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) = k10_relat_1(sK8,k3_xboole_0(sK6,sK7))
% 2.51/0.95      | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))) = iProver_top
% 2.51/0.95      | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK6)) = iProver_top ),
% 2.51/0.95      inference(predicate_to_equality,[status(thm)],[c_1307]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1,plain,
% 2.51/0.95      ( r2_hidden(sK0(X0,X1,X2),X1)
% 2.51/0.95      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.51/0.95      | k3_xboole_0(X0,X1) = X2 ),
% 2.51/0.95      inference(cnf_transformation,[],[f39]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1304,plain,
% 2.51/0.95      ( r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7)))
% 2.51/0.95      | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7))
% 2.51/0.95      | k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) = k10_relat_1(sK8,k3_xboole_0(sK6,sK7)) ),
% 2.51/0.95      inference(instantiation,[status(thm)],[c_1]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_1305,plain,
% 2.51/0.95      ( k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) = k10_relat_1(sK8,k3_xboole_0(sK6,sK7))
% 2.51/0.95      | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))) = iProver_top
% 2.51/0.95      | r2_hidden(sK0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7),k10_relat_1(sK8,k3_xboole_0(sK6,sK7))),k10_relat_1(sK8,sK7)) = iProver_top ),
% 2.51/0.95      inference(predicate_to_equality,[status(thm)],[c_1304]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(c_22,negated_conjecture,
% 2.51/0.95      ( k3_xboole_0(k10_relat_1(sK8,sK6),k10_relat_1(sK8,sK7)) != k10_relat_1(sK8,k3_xboole_0(sK6,sK7)) ),
% 2.51/0.95      inference(cnf_transformation,[],[f59]) ).
% 2.51/0.95  
% 2.51/0.95  cnf(contradiction,plain,
% 2.51/0.95      ( $false ),
% 2.51/0.95      inference(minisat,
% 2.51/0.95                [status(thm)],
% 2.51/0.95                [c_3148,c_2520,c_2517,c_2514,c_2392,c_2389,c_1415,c_1413,
% 2.51/0.95                 c_1373,c_1337,c_1335,c_1311,c_1308,c_1305,c_22]) ).
% 2.51/0.95  
% 2.51/0.95  
% 2.51/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 2.51/0.95  
% 2.51/0.95  ------                               Statistics
% 2.51/0.95  
% 2.51/0.95  ------ General
% 2.51/0.95  
% 2.51/0.95  abstr_ref_over_cycles:                  0
% 2.51/0.95  abstr_ref_under_cycles:                 0
% 2.51/0.95  gc_basic_clause_elim:                   0
% 2.51/0.95  forced_gc_time:                         0
% 2.51/0.95  parsing_time:                           0.029
% 2.51/0.95  unif_index_cands_time:                  0.
% 2.51/0.95  unif_index_add_time:                    0.
% 2.51/0.95  orderings_time:                         0.
% 2.51/0.95  out_proof_time:                         0.018
% 2.51/0.95  total_time:                             0.172
% 2.51/0.95  num_of_symbols:                         49
% 2.51/0.95  num_of_terms:                           3908
% 2.51/0.95  
% 2.51/0.95  ------ Preprocessing
% 2.51/0.95  
% 2.51/0.95  num_of_splits:                          0
% 2.51/0.95  num_of_split_atoms:                     0
% 2.51/0.95  num_of_reused_defs:                     0
% 2.51/0.95  num_eq_ax_congr_red:                    47
% 2.51/0.95  num_of_sem_filtered_clauses:            1
% 2.51/0.95  num_of_subtypes:                        0
% 2.51/0.95  monotx_restored_types:                  0
% 2.51/0.95  sat_num_of_epr_types:                   0
% 2.51/0.95  sat_num_of_non_cyclic_types:            0
% 2.51/0.95  sat_guarded_non_collapsed_types:        0
% 2.51/0.95  num_pure_diseq_elim:                    0
% 2.51/0.95  simp_replaced_by:                       0
% 2.51/0.95  res_preprocessed:                       119
% 2.51/0.95  prep_upred:                             0
% 2.51/0.95  prep_unflattend:                        15
% 2.51/0.95  smt_new_axioms:                         0
% 2.51/0.95  pred_elim_cands:                        1
% 2.51/0.95  pred_elim:                              2
% 2.51/0.95  pred_elim_cl:                           2
% 2.51/0.95  pred_elim_cycles:                       4
% 2.51/0.95  merged_defs:                            0
% 2.51/0.95  merged_defs_ncl:                        0
% 2.51/0.95  bin_hyper_res:                          0
% 2.51/0.95  prep_cycles:                            4
% 2.51/0.95  pred_elim_time:                         0.005
% 2.51/0.95  splitting_time:                         0.
% 2.51/0.95  sem_filter_time:                        0.
% 2.51/0.95  monotx_time:                            0.001
% 2.51/0.95  subtype_inf_time:                       0.
% 2.51/0.95  
% 2.51/0.95  ------ Problem properties
% 2.51/0.95  
% 2.51/0.95  clauses:                                22
% 2.51/0.95  conjectures:                            1
% 2.51/0.95  epr:                                    0
% 2.51/0.95  horn:                                   16
% 2.51/0.95  ground:                                 1
% 2.51/0.95  unary:                                  1
% 2.51/0.95  binary:                                 9
% 2.51/0.95  lits:                                   58
% 2.51/0.95  lits_eq:                                10
% 2.51/0.95  fd_pure:                                0
% 2.51/0.95  fd_pseudo:                              0
% 2.51/0.95  fd_cond:                                0
% 2.51/0.95  fd_pseudo_cond:                         9
% 2.51/0.95  ac_symbols:                             0
% 2.51/0.95  
% 2.51/0.95  ------ Propositional Solver
% 2.51/0.95  
% 2.51/0.95  prop_solver_calls:                      26
% 2.51/0.95  prop_fast_solver_calls:                 799
% 2.51/0.95  smt_solver_calls:                       0
% 2.51/0.95  smt_fast_solver_calls:                  0
% 2.51/0.95  prop_num_of_clauses:                    1432
% 2.51/0.95  prop_preprocess_simplified:             5273
% 2.51/0.95  prop_fo_subsumed:                       7
% 2.51/0.95  prop_solver_time:                       0.
% 2.51/0.95  smt_solver_time:                        0.
% 2.51/0.95  smt_fast_solver_time:                   0.
% 2.51/0.95  prop_fast_solver_time:                  0.
% 2.51/0.95  prop_unsat_core_time:                   0.
% 2.51/0.95  
% 2.51/0.95  ------ QBF
% 2.51/0.95  
% 2.51/0.95  qbf_q_res:                              0
% 2.51/0.95  qbf_num_tautologies:                    0
% 2.51/0.95  qbf_prep_cycles:                        0
% 2.51/0.95  
% 2.51/0.95  ------ BMC1
% 2.51/0.95  
% 2.51/0.95  bmc1_current_bound:                     -1
% 2.51/0.95  bmc1_last_solved_bound:                 -1
% 2.51/0.95  bmc1_unsat_core_size:                   -1
% 2.51/0.95  bmc1_unsat_core_parents_size:           -1
% 2.51/0.95  bmc1_merge_next_fun:                    0
% 2.51/0.95  bmc1_unsat_core_clauses_time:           0.
% 2.51/0.95  
% 2.51/0.95  ------ Instantiation
% 2.51/0.95  
% 2.51/0.95  inst_num_of_clauses:                    322
% 2.51/0.95  inst_num_in_passive:                    25
% 2.51/0.95  inst_num_in_active:                     135
% 2.51/0.95  inst_num_in_unprocessed:                162
% 2.51/0.95  inst_num_of_loops:                      161
% 2.51/0.95  inst_num_of_learning_restarts:          0
% 2.51/0.95  inst_num_moves_active_passive:          24
% 2.51/0.95  inst_lit_activity:                      0
% 2.51/0.95  inst_lit_activity_moves:                0
% 2.51/0.95  inst_num_tautologies:                   0
% 2.51/0.95  inst_num_prop_implied:                  0
% 2.51/0.95  inst_num_existing_simplified:           0
% 2.51/0.95  inst_num_eq_res_simplified:             0
% 2.51/0.95  inst_num_child_elim:                    0
% 2.51/0.95  inst_num_of_dismatching_blockings:      51
% 2.51/0.95  inst_num_of_non_proper_insts:           133
% 2.51/0.95  inst_num_of_duplicates:                 0
% 2.51/0.95  inst_inst_num_from_inst_to_res:         0
% 2.51/0.95  inst_dismatching_checking_time:         0.
% 2.51/0.95  
% 2.51/0.95  ------ Resolution
% 2.51/0.95  
% 2.51/0.95  res_num_of_clauses:                     0
% 2.51/0.95  res_num_in_passive:                     0
% 2.51/0.95  res_num_in_active:                      0
% 2.51/0.95  res_num_of_loops:                       123
% 2.51/0.95  res_forward_subset_subsumed:            6
% 2.51/0.95  res_backward_subset_subsumed:           0
% 2.51/0.95  res_forward_subsumed:                   0
% 2.51/0.95  res_backward_subsumed:                  0
% 2.51/0.95  res_forward_subsumption_resolution:     0
% 2.51/0.95  res_backward_subsumption_resolution:    0
% 2.51/0.95  res_clause_to_clause_subsumption:       434
% 2.51/0.95  res_orphan_elimination:                 0
% 2.51/0.95  res_tautology_del:                      2
% 2.51/0.95  res_num_eq_res_simplified:              0
% 2.51/0.95  res_num_sel_changes:                    0
% 2.51/0.95  res_moves_from_active_to_pass:          0
% 2.51/0.95  
% 2.51/0.95  ------ Superposition
% 2.51/0.95  
% 2.51/0.95  sup_time_total:                         0.
% 2.51/0.95  sup_time_generating:                    0.
% 2.51/0.95  sup_time_sim_full:                      0.
% 2.51/0.95  sup_time_sim_immed:                     0.
% 2.51/0.95  
% 2.51/0.95  sup_num_of_clauses:                     122
% 2.51/0.95  sup_num_in_active:                      32
% 2.51/0.95  sup_num_in_passive:                     90
% 2.51/0.95  sup_num_of_loops:                       32
% 2.51/0.95  sup_fw_superposition:                   38
% 2.51/0.95  sup_bw_superposition:                   72
% 2.51/0.95  sup_immediate_simplified:               4
% 2.51/0.95  sup_given_eliminated:                   0
% 2.51/0.95  comparisons_done:                       0
% 2.51/0.95  comparisons_avoided:                    0
% 2.51/0.95  
% 2.51/0.95  ------ Simplifications
% 2.51/0.95  
% 2.51/0.95  
% 2.51/0.95  sim_fw_subset_subsumed:                 2
% 2.51/0.95  sim_bw_subset_subsumed:                 0
% 2.51/0.95  sim_fw_subsumed:                        2
% 2.51/0.95  sim_bw_subsumed:                        0
% 2.51/0.95  sim_fw_subsumption_res:                 0
% 2.51/0.95  sim_bw_subsumption_res:                 0
% 2.51/0.95  sim_tautology_del:                      9
% 2.51/0.95  sim_eq_tautology_del:                   0
% 2.51/0.95  sim_eq_res_simp:                        3
% 2.51/0.95  sim_fw_demodulated:                     0
% 2.51/0.95  sim_bw_demodulated:                     0
% 2.51/0.95  sim_light_normalised:                   0
% 2.51/0.95  sim_joinable_taut:                      0
% 2.51/0.95  sim_joinable_simp:                      0
% 2.51/0.95  sim_ac_normalised:                      0
% 2.51/0.95  sim_smt_subsumption:                    0
% 2.51/0.95  
%------------------------------------------------------------------------------
