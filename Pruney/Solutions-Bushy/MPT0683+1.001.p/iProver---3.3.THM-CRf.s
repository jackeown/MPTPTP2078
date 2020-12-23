%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0683+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:53 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 340 expanded)
%              Number of clauses        :   68 (  96 expanded)
%              Number of leaves         :    6 (  62 expanded)
%              Depth                    :   17
%              Number of atoms          :  459 (1923 expanded)
%              Number of equality atoms :   98 ( 339 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

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
    inference(nnf_transformation,[],[f2])).

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
    inference(flattening,[],[f14])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f1,axiom,(
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

fof(f5,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f9,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
            & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
                | ~ r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
                  & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k10_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k10_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( k10_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f8,f19])).

fof(f34,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    k10_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1122,plain,
    ( ~ r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),X0)
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k3_xboole_0(X0,k10_relat_1(sK4,sK3)))
    | ~ r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5423,plain,
    ( r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))
    | ~ r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3))
    | ~ r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_1122])).

cnf(c_5424,plain,
    ( r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))) = iProver_top
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3)) != iProver_top
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5423])).

cnf(c_829,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),X0)
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k3_xboole_0(X0,sK3))
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1857,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k3_xboole_0(sK2,sK3))
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3)
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_1858,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k3_xboole_0(sK2,sK3)) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1857])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_242,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_243,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(k1_funct_1(sK4,X0),X1)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_247,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),X1)
    | ~ r2_hidden(X0,k10_relat_1(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_243,c_14])).

cnf(c_248,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(k1_funct_1(sK4,X0),X1) ),
    inference(renaming,[status(thm)],[c_247])).

cnf(c_1210,plain,
    ( ~ r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2))
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_1214,plain,
    ( r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1210])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_224,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_225,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_229,plain,
    ( r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(X0,k10_relat_1(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_225,c_14])).

cnf(c_230,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(X0,k1_relat_1(sK4)) ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_1211,plain,
    ( ~ r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2))
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_1212,plain,
    ( r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2)) != iProver_top
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1211])).

cnf(c_1131,plain,
    ( ~ r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3))
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3) ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_1135,plain,
    ( r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1131])).

cnf(c_3,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2))
    | ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_260,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2))
    | ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_261,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,X0),X1)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_265,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,X0),X1)
    | ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(X0,k10_relat_1(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_261,c_14])).

cnf(c_266,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,X0),X1) ),
    inference(renaming,[status(thm)],[c_265])).

cnf(c_734,plain,
    ( r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,X0))
    | ~ r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),X0) ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_892,plain,
    ( r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2))
    | ~ r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_893,plain,
    ( r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2)) = iProver_top
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_892])).

cnf(c_889,plain,
    ( r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3))
    | ~ r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3) ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_890,plain,
    ( r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3)) = iProver_top
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_889])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_768,plain,
    ( ~ r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_769,plain,
    ( r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))) != iProver_top
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_765,plain,
    ( ~ r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_766,plain,
    ( r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))) != iProver_top
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_765])).

cnf(c_752,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k3_xboole_0(sK2,sK3))
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_753,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k3_xboole_0(sK2,sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_749,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k3_xboole_0(sK2,sK3))
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_750,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k3_xboole_0(sK2,sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_749])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
    | ~ r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_200,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
    | ~ r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_201,plain,
    ( ~ r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ r2_hidden(sK0(sK4,X0,X1),k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,X0,X1)),X0)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_205,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,X0,X1)),X0)
    | ~ r2_hidden(sK0(sK4,X0,X1),k1_relat_1(sK4))
    | ~ r2_hidden(sK0(sK4,X0,X1),X1)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_201,c_14])).

cnf(c_206,plain,
    ( ~ r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ r2_hidden(sK0(sK4,X0,X1),k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,X0,X1)),X0)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(renaming,[status(thm)],[c_205])).

cnf(c_708,plain,
    ( ~ r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))
    | ~ r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k3_xboole_0(sK2,sK3))
    | k10_relat_1(sK4,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_206])).

cnf(c_709,plain,
    ( k10_relat_1(sK4,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))) != iProver_top
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_179,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_13])).

cnf(c_180,plain,
    ( r2_hidden(sK0(sK4,X0,X1),X1)
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,X0,X1)),X0)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_179])).

cnf(c_184,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(sK4,X0,X1)),X0)
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_180,c_14])).

cnf(c_185,plain,
    ( r2_hidden(sK0(sK4,X0,X1),X1)
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,X0,X1)),X0)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(renaming,[status(thm)],[c_184])).

cnf(c_705,plain,
    ( r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k3_xboole_0(sK2,sK3))
    | k10_relat_1(sK4,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_706,plain,
    ( k10_relat_1(sK4,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_158,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_159,plain,
    ( r2_hidden(sK0(sK4,X0,X1),X1)
    | r2_hidden(sK0(sK4,X0,X1),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_158])).

cnf(c_163,plain,
    ( r2_hidden(sK0(sK4,X0,X1),k1_relat_1(sK4))
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_159,c_14])).

cnf(c_164,plain,
    ( r2_hidden(sK0(sK4,X0,X1),X1)
    | r2_hidden(sK0(sK4,X0,X1),k1_relat_1(sK4))
    | k10_relat_1(sK4,X0) = X1 ),
    inference(renaming,[status(thm)],[c_163])).

cnf(c_702,plain,
    ( r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4))
    | k10_relat_1(sK4,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_703,plain,
    ( k10_relat_1(sK4,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))) = iProver_top
    | r2_hidden(sK0(sK4,k3_xboole_0(sK2,sK3),k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_702])).

cnf(c_12,negated_conjecture,
    ( k10_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k3_xboole_0(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5424,c_1858,c_1214,c_1212,c_1135,c_893,c_890,c_769,c_766,c_753,c_750,c_709,c_706,c_703,c_12])).


%------------------------------------------------------------------------------
