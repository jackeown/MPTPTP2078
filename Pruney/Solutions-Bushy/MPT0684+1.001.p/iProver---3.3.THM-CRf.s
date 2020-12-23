%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0684+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:53 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 361 expanded)
%              Number of clauses        :   71 (  99 expanded)
%              Number of leaves         :    7 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :  478 (1962 expanded)
%              Number of equality atoms :  103 ( 357 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
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

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k6_subset_1(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f41])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

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
    inference(nnf_transformation,[],[f7])).

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
    inference(flattening,[],[f10])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k10_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k10_relat_1(sK4,k6_subset_1(sK2,sK3)) != k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( k10_relat_1(sK4,k6_subset_1(sK2,sK3)) != k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f20])).

fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f28,f34])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    k10_relat_1(sK4,k6_subset_1(sK2,sK3)) != k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1071,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),X0)
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k6_subset_1(sK2,X0))
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2522,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k6_subset_1(sK2,sK3))
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3)
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) ),
    inference(instantiation,[status(thm)],[c_1071])).

cnf(c_2523,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k6_subset_1(sK2,sK3)) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2522])).

cnf(c_720,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,k6_subset_1(k10_relat_1(sK4,X2),X1))
    | ~ r2_hidden(X0,k10_relat_1(sK4,X2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1018,plain,
    ( r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),X0)
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k6_subset_1(k10_relat_1(sK4,sK2),X0))
    | ~ r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_2417,plain,
    ( r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3))
    | ~ r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_1018])).

cnf(c_2418,plain,
    ( r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))) = iProver_top
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3)) = iProver_top
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2417])).

cnf(c_3,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2))
    | ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_258,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2))
    | ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_259,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,X0),X1)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_263,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,X0),X1)
    | ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(X0,k10_relat_1(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_259,c_14])).

cnf(c_264,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,X0),X1) ),
    inference(renaming,[status(thm)],[c_263])).

cnf(c_649,plain,
    ( r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,X0))
    | ~ r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),X0) ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_1829,plain,
    ( r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3))
    | ~ r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3) ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_1830,plain,
    ( r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3)) = iProver_top
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1829])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_240,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_241,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(k1_funct_1(sK4,X0),X1)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_245,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),X1)
    | ~ r2_hidden(X0,k10_relat_1(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_241,c_14])).

cnf(c_246,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(k1_funct_1(sK4,X0),X1) ),
    inference(renaming,[status(thm)],[c_245])).

cnf(c_1267,plain,
    ( ~ r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,X0))
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),X0) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_1812,plain,
    ( ~ r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3))
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3) ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_1813,plain,
    ( r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1812])).

cnf(c_1096,plain,
    ( r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2))
    | ~ r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_1097,plain,
    ( r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2)) = iProver_top
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1096])).

cnf(c_1023,plain,
    ( ~ r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2))
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_1027,plain,
    ( r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1023])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_222,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_223,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_227,plain,
    ( r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(X0,k10_relat_1(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_223,c_14])).

cnf(c_228,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(X0,k1_relat_1(sK4)) ),
    inference(renaming,[status(thm)],[c_227])).

cnf(c_1024,plain,
    ( ~ r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2))
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_1025,plain,
    ( r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2)) != iProver_top
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1024])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_800,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k6_subset_1(sK2,sK3))
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_801,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k6_subset_1(sK2,sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_791,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k6_subset_1(sK2,sK3))
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_792,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k6_subset_1(sK2,sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_618,plain,
    ( ~ r2_hidden(X0,k6_subset_1(k10_relat_1(sK4,X1),X2))
    | r2_hidden(X0,k10_relat_1(sK4,X1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_712,plain,
    ( ~ r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_713,plain,
    ( r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))) != iProver_top
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_666,plain,
    ( ~ r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))
    | ~ r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_667,plain,
    ( r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))) != iProver_top
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k10_relat_1(sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
    | ~ r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_198,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
    | ~ r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_199,plain,
    ( ~ r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ r2_hidden(sK0(sK4,X0,X1),k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,X0,X1)),X0)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_203,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,X0,X1)),X0)
    | ~ r2_hidden(sK0(sK4,X0,X1),k1_relat_1(sK4))
    | ~ r2_hidden(sK0(sK4,X0,X1),X1)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_199,c_14])).

cnf(c_204,plain,
    ( ~ r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ r2_hidden(sK0(sK4,X0,X1),k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,X0,X1)),X0)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(renaming,[status(thm)],[c_203])).

cnf(c_646,plain,
    ( ~ r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))
    | ~ r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k6_subset_1(sK2,sK3))
    | k10_relat_1(sK4,k6_subset_1(sK2,sK3)) = k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_647,plain,
    ( k10_relat_1(sK4,k6_subset_1(sK2,sK3)) = k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))) != iProver_top
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k6_subset_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_646])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_177,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k1_funct_1(X0,sK0(X0,X1,X2)),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_13])).

cnf(c_178,plain,
    ( r2_hidden(sK0(sK4,X0,X1),X1)
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,X0,X1)),X0)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_177])).

cnf(c_182,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(sK4,X0,X1)),X0)
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_178,c_14])).

cnf(c_183,plain,
    ( r2_hidden(sK0(sK4,X0,X1),X1)
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,X0,X1)),X0)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(renaming,[status(thm)],[c_182])).

cnf(c_643,plain,
    ( r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k6_subset_1(sK2,sK3))
    | k10_relat_1(sK4,k6_subset_1(sK2,sK3)) = k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_644,plain,
    ( k10_relat_1(sK4,k6_subset_1(sK2,sK3)) = k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))) = iProver_top
    | r2_hidden(k1_funct_1(sK4,sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))),k6_subset_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_156,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_157,plain,
    ( r2_hidden(sK0(sK4,X0,X1),X1)
    | r2_hidden(sK0(sK4,X0,X1),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_156])).

cnf(c_161,plain,
    ( r2_hidden(sK0(sK4,X0,X1),k1_relat_1(sK4))
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | k10_relat_1(sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_157,c_14])).

cnf(c_162,plain,
    ( r2_hidden(sK0(sK4,X0,X1),X1)
    | r2_hidden(sK0(sK4,X0,X1),k1_relat_1(sK4))
    | k10_relat_1(sK4,X0) = X1 ),
    inference(renaming,[status(thm)],[c_161])).

cnf(c_640,plain,
    ( r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)))
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4))
    | k10_relat_1(sK4,k6_subset_1(sK2,sK3)) = k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_641,plain,
    ( k10_relat_1(sK4,k6_subset_1(sK2,sK3)) = k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))) = iProver_top
    | r2_hidden(sK0(sK4,k6_subset_1(sK2,sK3),k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))),k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_12,negated_conjecture,
    ( k10_relat_1(sK4,k6_subset_1(sK2,sK3)) != k6_subset_1(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2523,c_2418,c_1830,c_1813,c_1097,c_1027,c_1025,c_801,c_792,c_713,c_667,c_647,c_644,c_641,c_12])).


%------------------------------------------------------------------------------
