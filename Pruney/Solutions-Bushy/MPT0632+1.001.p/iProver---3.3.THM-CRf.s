%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0632+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:46 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  137 (3772 expanded)
%              Number of clauses        :   91 ( 958 expanded)
%              Number of leaves         :   12 ( 734 expanded)
%              Depth                    :   34
%              Number of atoms          :  545 (25851 expanded)
%              Number of equality atoms :  311 (13199 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k6_relat_1(X0) = X1
        <=> ( ! [X2] :
                ( r2_hidden(X2,X0)
               => k1_funct_1(X1,X2) = X2 )
            & k1_relat_1(X1) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <~> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <~> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0
        | k6_relat_1(X0) != X1 )
      & ( ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 )
        | k6_relat_1(X0) = X1 )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0
        | k6_relat_1(X0) != X1 )
      & ( ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 )
        | k6_relat_1(X0) = X1 )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0
        | k6_relat_1(X0) != X1 )
      & ( ( ! [X3] :
              ( k1_funct_1(X1,X3) = X3
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X1) = X0 )
        | k6_relat_1(X0) = X1 )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(rectify,[],[f24])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK4) != sK4
        & r2_hidden(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ( ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0
          | k6_relat_1(X0) != X1 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) = X1 )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ? [X2] :
            ( k1_funct_1(sK3,X2) != X2
            & r2_hidden(X2,sK2) )
        | k1_relat_1(sK3) != sK2
        | k6_relat_1(sK2) != sK3 )
      & ( ( ! [X3] :
              ( k1_funct_1(sK3,X3) = X3
              | ~ r2_hidden(X3,sK2) )
          & k1_relat_1(sK3) = sK2 )
        | k6_relat_1(sK2) = sK3 )
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( ( k1_funct_1(sK3,sK4) != sK4
        & r2_hidden(sK4,sK2) )
      | k1_relat_1(sK3) != sK2
      | k6_relat_1(sK2) != sK3 )
    & ( ( ! [X3] :
            ( k1_funct_1(sK3,X3) = X3
            | ~ r2_hidden(X3,sK2) )
        & k1_relat_1(sK3) = sK2 )
      | k6_relat_1(sK2) = sK3 )
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f27,f26])).

fof(f47,plain,
    ( k1_relat_1(sK3) = sK2
    | k6_relat_1(sK2) = sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK0(X0,X1) != sK1(X0,X1)
          | ~ r2_hidden(sK0(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( ( sK0(X0,X1) = sK1(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK0(X0,X1) != sK1(X0,X1)
              | ~ r2_hidden(sK0(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( ( sK0(X0,X1) = sK1(X0,X1)
                & r2_hidden(sK0(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK0(X0,X1),X0)
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,X3) = X3
      | ~ r2_hidden(X3,sK2)
      | k6_relat_1(sK2) = sK3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK0(X0,X1) = sK1(X0,X1)
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK0(X0,X1) != sK1(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X0)
      | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,
    ( r2_hidden(sK4,sK2)
    | k1_relat_1(sK3) != sK2
    | k6_relat_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f31])).

fof(f52,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f50,plain,
    ( k1_funct_1(sK3,sK4) != sK4
    | k1_relat_1(sK3) != sK2
    | k6_relat_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_19,negated_conjecture,
    ( k1_relat_1(sK3) = sK2
    | k6_relat_1(sK2) = sK3 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | ~ v1_relat_1(X1)
    | k6_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1051,plain,
    ( k6_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_197,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_198,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(k4_tarski(X0,X1),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_202,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
    | r2_hidden(X0,k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_198,c_21])).

cnf(c_203,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(k4_tarski(X0,X1),sK3) ),
    inference(renaming,[status(thm)],[c_202])).

cnf(c_1043,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_203])).

cnf(c_1857,plain,
    ( k6_relat_1(X0) = sK3
    | r2_hidden(sK0(X0,sK3),X0) = iProver_top
    | r2_hidden(sK0(X0,sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1051,c_1043])).

cnf(c_22,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2223,plain,
    ( r2_hidden(sK0(X0,sK3),k1_relat_1(sK3)) = iProver_top
    | r2_hidden(sK0(X0,sK3),X0) = iProver_top
    | k6_relat_1(X0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1857,c_22])).

cnf(c_2224,plain,
    ( k6_relat_1(X0) = sK3
    | r2_hidden(sK0(X0,sK3),X0) = iProver_top
    | r2_hidden(sK0(X0,sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2223])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK3,X0) = X0
    | k6_relat_1(sK2) = sK3 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1045,plain,
    ( k1_funct_1(sK3,X0) = X0
    | k6_relat_1(sK2) = sK3
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2233,plain,
    ( k1_funct_1(sK3,sK0(sK2,sK3)) = sK0(sK2,sK3)
    | k6_relat_1(sK2) = sK3
    | r2_hidden(sK0(sK2,sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2224,c_1045])).

cnf(c_1239,plain,
    ( ~ r2_hidden(sK0(sK2,sK3),sK2)
    | k1_funct_1(sK3,sK0(sK2,sK3)) = sK0(sK2,sK3)
    | k6_relat_1(sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1240,plain,
    ( k1_funct_1(sK3,sK0(sK2,sK3)) = sK0(sK2,sK3)
    | k6_relat_1(sK2) = sK3
    | r2_hidden(sK0(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1239])).

cnf(c_2232,plain,
    ( k6_relat_1(X0) = sK3
    | k6_relat_1(sK2) = sK3
    | r2_hidden(sK0(X0,sK3),X0) = iProver_top
    | r2_hidden(sK0(X0,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_2224])).

cnf(c_2267,plain,
    ( k6_relat_1(sK2) = sK3
    | r2_hidden(sK0(sK2,sK3),sK2) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_2232])).

cnf(c_2269,plain,
    ( k6_relat_1(sK2) = sK3
    | r2_hidden(sK0(sK2,sK3),sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2267])).

cnf(c_2337,plain,
    ( k6_relat_1(sK2) = sK3
    | k1_funct_1(sK3,sK0(sK2,sK3)) = sK0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2233,c_1240,c_2269])).

cnf(c_2338,plain,
    ( k1_funct_1(sK3,sK0(sK2,sK3)) = sK0(sK2,sK3)
    | k6_relat_1(sK2) = sK3 ),
    inference(renaming,[status(thm)],[c_2337])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_215,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_216,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_220,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
    | ~ r2_hidden(X0,k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_216,c_21])).

cnf(c_221,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) ),
    inference(renaming,[status(thm)],[c_220])).

cnf(c_1042,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_2343,plain,
    ( k6_relat_1(sK2) = sK3
    | r2_hidden(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),sK3) = iProver_top
    | r2_hidden(sK0(sK2,sK3),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2338,c_1042])).

cnf(c_1,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
    | ~ v1_relat_1(X1)
    | sK1(X0,X1) = sK0(X0,X1)
    | k6_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1052,plain,
    ( sK1(X0,X1) = sK0(X0,X1)
    | k6_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_114,plain,
    ( ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_15])).

cnf(c_115,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_114])).

cnf(c_251,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_115,c_20])).

cnf(c_252,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_256,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
    | k1_funct_1(sK3,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_252,c_21])).

cnf(c_1040,plain,
    ( k1_funct_1(sK3,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_256])).

cnf(c_1901,plain,
    ( k1_funct_1(sK3,sK0(X0,sK3)) = sK1(X0,sK3)
    | sK1(X0,sK3) = sK0(X0,sK3)
    | k6_relat_1(X0) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1052,c_1040])).

cnf(c_1934,plain,
    ( ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(X0,sK3)) = sK1(X0,sK3)
    | sK1(X0,sK3) = sK0(X0,sK3)
    | k6_relat_1(X0) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1901])).

cnf(c_2816,plain,
    ( k6_relat_1(X0) = sK3
    | sK1(X0,sK3) = sK0(X0,sK3)
    | k1_funct_1(sK3,sK0(X0,sK3)) = sK1(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1901,c_21,c_1934])).

cnf(c_2817,plain,
    ( k1_funct_1(sK3,sK0(X0,sK3)) = sK1(X0,sK3)
    | sK1(X0,sK3) = sK0(X0,sK3)
    | k6_relat_1(X0) = sK3 ),
    inference(renaming,[status(thm)],[c_2816])).

cnf(c_1900,plain,
    ( sK1(X0,sK3) = sK0(X0,sK3)
    | k6_relat_1(X0) = sK3
    | r2_hidden(sK0(X0,sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1052,c_1043])).

cnf(c_2537,plain,
    ( r2_hidden(sK0(X0,sK3),k1_relat_1(sK3)) = iProver_top
    | k6_relat_1(X0) = sK3
    | sK1(X0,sK3) = sK0(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1900,c_22])).

cnf(c_2538,plain,
    ( sK1(X0,sK3) = sK0(X0,sK3)
    | k6_relat_1(X0) = sK3
    | r2_hidden(sK0(X0,sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2537])).

cnf(c_2546,plain,
    ( sK1(X0,sK3) = sK0(X0,sK3)
    | k6_relat_1(X0) = sK3
    | k6_relat_1(sK2) = sK3
    | r2_hidden(sK0(X0,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_2538])).

cnf(c_2620,plain,
    ( k1_funct_1(sK3,sK0(X0,sK3)) = sK0(X0,sK3)
    | sK1(X0,sK3) = sK0(X0,sK3)
    | k6_relat_1(X0) = sK3
    | k6_relat_1(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_2546,c_1045])).

cnf(c_2830,plain,
    ( sK1(X0,sK3) = sK0(X0,sK3)
    | k6_relat_1(X0) = sK3
    | k6_relat_1(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_2817,c_2620])).

cnf(c_2829,plain,
    ( sK1(sK2,sK3) = sK0(sK2,sK3)
    | k6_relat_1(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_2817,c_2338])).

cnf(c_0,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | ~ v1_relat_1(X1)
    | sK1(X0,X1) != sK0(X0,X1)
    | k6_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1053,plain,
    ( sK1(X0,X1) != sK0(X0,X1)
    | k6_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) != iProver_top
    | r2_hidden(sK0(X0,X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2853,plain,
    ( k6_relat_1(sK2) = sK3
    | r2_hidden(k4_tarski(sK0(sK2,sK3),sK1(sK2,sK3)),sK3) != iProver_top
    | r2_hidden(sK0(sK2,sK3),sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2829,c_1053])).

cnf(c_3088,plain,
    ( k6_relat_1(sK2) = sK3
    | r2_hidden(k4_tarski(sK0(sK2,sK3),sK1(sK2,sK3)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2853,c_22,c_2269])).

cnf(c_3097,plain,
    ( k6_relat_1(sK2) = sK3
    | r2_hidden(k4_tarski(sK0(sK2,sK3),sK0(sK2,sK3)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2830,c_3088])).

cnf(c_3354,plain,
    ( k6_relat_1(sK2) = sK3
    | r2_hidden(sK0(sK2,sK3),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2343,c_3097])).

cnf(c_3370,plain,
    ( k6_relat_1(sK2) = sK3
    | r2_hidden(sK0(sK2,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_3354])).

cnf(c_3395,plain,
    ( k6_relat_1(sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3370,c_2269])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | k1_relat_1(sK3) != sK2
    | k6_relat_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1046,plain,
    ( k1_relat_1(sK3) != sK2
    | k6_relat_1(sK2) != sK3
    | r2_hidden(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3411,plain,
    ( k1_relat_1(sK3) != sK2
    | sK3 != sK3
    | r2_hidden(sK4,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3395,c_1046])).

cnf(c_3418,plain,
    ( k1_relat_1(sK3) != sK2
    | r2_hidden(sK4,sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3411])).

cnf(c_27,plain,
    ( k1_relat_1(sK3) != sK2
    | k6_relat_1(sK2) != sK3
    | r2_hidden(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_792,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_809,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_1295,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_793,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1282,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_1294,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_1332,plain,
    ( k1_relat_1(k6_relat_1(sK2)) != sK2
    | sK2 = k1_relat_1(k6_relat_1(sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_12,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1333,plain,
    ( k1_relat_1(k6_relat_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1254,plain,
    ( k1_relat_1(sK3) != X0
    | k1_relat_1(sK3) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_1346,plain,
    ( k1_relat_1(sK3) != k1_relat_1(k6_relat_1(sK2))
    | k1_relat_1(sK3) = sK2
    | sK2 != k1_relat_1(k6_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_799,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_1438,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k6_relat_1(sK2))
    | sK3 != k6_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_1557,plain,
    ( k6_relat_1(sK2) != X0
    | sK3 != X0
    | sK3 = k6_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_1558,plain,
    ( k6_relat_1(sK2) != sK3
    | sK3 = k6_relat_1(sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1557])).

cnf(c_4448,plain,
    ( r2_hidden(sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3418,c_27,c_809,c_1295,c_1332,c_1333,c_1346,c_1438,c_1558,c_2269,c_3370])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1))
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1050,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1047,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1115,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,X0),k6_relat_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1050,c_1047])).

cnf(c_3430,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k4_tarski(X0,X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3395,c_1115])).

cnf(c_3763,plain,
    ( k1_funct_1(sK3,X0) = X0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3430,c_1040])).

cnf(c_4620,plain,
    ( k1_funct_1(sK3,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_4448,c_3763])).

cnf(c_16,negated_conjecture,
    ( k1_funct_1(sK3,sK4) != sK4
    | k1_relat_1(sK3) != sK2
    | k6_relat_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4620,c_3395,c_1558,c_1438,c_1346,c_1333,c_1332,c_1295,c_809,c_16])).


%------------------------------------------------------------------------------
