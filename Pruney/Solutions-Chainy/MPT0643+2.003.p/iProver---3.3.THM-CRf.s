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
% DateTime   : Thu Dec  3 11:50:16 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 623 expanded)
%              Number of clauses        :   65 ( 141 expanded)
%              Number of leaves         :   18 ( 166 expanded)
%              Depth                    :   25
%              Number of atoms          :  610 (5030 expanded)
%              Number of equality atoms :  278 (2197 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k5_relat_1(X2,X1) = X1
                & v2_funct_1(X1)
                & r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X0
                & k1_relat_1(X1) = X0 )
             => k6_relat_1(X0) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k6_relat_1(X0) != sK11
        & k5_relat_1(sK11,X1) = X1
        & v2_funct_1(X1)
        & r1_tarski(k2_relat_1(sK11),X0)
        & k1_relat_1(sK11) = X0
        & k1_relat_1(X1) = X0
        & v1_funct_1(sK11)
        & v1_relat_1(sK11) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k6_relat_1(X0) != X2
            & k5_relat_1(X2,X1) = X1
            & v2_funct_1(X1)
            & r1_tarski(k2_relat_1(X2),X0)
            & k1_relat_1(X2) = X0
            & k1_relat_1(X1) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k6_relat_1(sK9) != X2
          & k5_relat_1(X2,sK10) = sK10
          & v2_funct_1(sK10)
          & r1_tarski(k2_relat_1(X2),sK9)
          & k1_relat_1(X2) = sK9
          & k1_relat_1(sK10) = sK9
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK10)
      & v1_relat_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( k6_relat_1(sK9) != sK11
    & k5_relat_1(sK11,sK10) = sK10
    & v2_funct_1(sK10)
    & r1_tarski(k2_relat_1(sK11),sK9)
    & k1_relat_1(sK11) = sK9
    & k1_relat_1(sK10) = sK9
    & v1_funct_1(sK11)
    & v1_relat_1(sK11)
    & v1_funct_1(sK10)
    & v1_relat_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f21,f46,f45])).

fof(f75,plain,(
    k1_relat_1(sK11) = sK9 ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK8(X0,X1)) != sK8(X0,X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK8(X0,X1)) != sK8(X0,X1)
            & r2_hidden(sK8(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f40,f41])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK8(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | r2_hidden(sK8(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f72,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    k6_relat_1(sK9) != sK11 ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).

fof(f49,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f69])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).

fof(f54,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,(
    r1_tarski(k2_relat_1(sK11),sK9) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    k5_relat_1(sK11,sK10) = sK10 ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK6(X0) != sK7(X0)
        & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))
        & r2_hidden(sK7(X0),k1_relat_1(X0))
        & r2_hidden(sK6(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK6(X0) != sK7(X0)
            & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))
            & r2_hidden(sK7(X0),k1_relat_1(X0))
            & r2_hidden(sK6(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f35,f36])).

fof(f57,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    k1_relat_1(sK10) = sK9 ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    v2_funct_1(sK10) ),
    inference(cnf_transformation,[],[f47])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | k1_funct_1(X1,sK8(X0,X1)) != sK8(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f84,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k1_funct_1(X1,sK8(k1_relat_1(X1),X1)) != sK8(k1_relat_1(X1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f66])).

cnf(c_26,negated_conjecture,
    ( k1_relat_1(sK11) = sK9 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_16,plain,
    ( r2_hidden(sK8(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1254,plain,
    ( k6_relat_1(k1_relat_1(X0)) = X0
    | r2_hidden(sK8(k1_relat_1(X0),X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3901,plain,
    ( k6_relat_1(k1_relat_1(sK11)) = sK11
    | r2_hidden(sK8(sK9,sK11),sK9) = iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1254])).

cnf(c_3908,plain,
    ( k6_relat_1(sK9) = sK11
    | r2_hidden(sK8(sK9,sK11),sK9) = iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3901,c_26])).

cnf(c_29,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34,plain,
    ( v1_relat_1(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_35,plain,
    ( v1_funct_1(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_22,negated_conjecture,
    ( k6_relat_1(sK9) != sK11 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4007,plain,
    ( r2_hidden(sK8(sK9,sK11),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3908,c_34,c_35,c_22])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1266,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_20,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1250,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2180,plain,
    ( k1_funct_1(X0,X1) = sK2(X0,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1266,c_1250])).

cnf(c_12288,plain,
    ( k1_funct_1(sK11,X0) = sK2(sK11,X0)
    | r2_hidden(X0,sK9) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_2180])).

cnf(c_12502,plain,
    ( k1_funct_1(sK11,X0) = sK2(sK11,X0)
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12288,c_34,c_35])).

cnf(c_12526,plain,
    ( k1_funct_1(sK11,sK8(sK9,sK11)) = sK2(sK11,sK8(sK9,sK11)) ),
    inference(superposition,[status(thm)],[c_4007,c_12502])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1251,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13136,plain,
    ( r2_hidden(sK8(sK9,sK11),k1_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(sK8(sK9,sK11),sK2(sK11,sK8(sK9,sK11))),sK11) = iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_12526,c_1251])).

cnf(c_13140,plain,
    ( r2_hidden(sK8(sK9,sK11),sK9) != iProver_top
    | r2_hidden(k4_tarski(sK8(sK9,sK11),sK2(sK11,sK8(sK9,sK11))),sK11) = iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13136,c_26])).

cnf(c_13146,plain,
    ( r2_hidden(k4_tarski(sK8(sK9,sK11),sK2(sK11,sK8(sK9,sK11))),sK11) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13140,c_34,c_35,c_22,c_3908])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1263,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13151,plain,
    ( r2_hidden(sK2(sK11,sK8(sK9,sK11)),k2_relat_1(sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13146,c_1263])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK11),sK9) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_309,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k2_relat_1(sK11) != X1
    | sK9 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_25])).

cnf(c_310,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK11))
    | r2_hidden(X0,sK9) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_1244,plain,
    ( r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
    | r2_hidden(X0,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_13669,plain,
    ( r2_hidden(sK2(sK11,sK8(sK9,sK11)),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_13151,c_1244])).

cnf(c_31,negated_conjecture,
    ( v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1245,plain,
    ( v1_relat_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1256,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4425,plain,
    ( k1_funct_1(X0,k1_funct_1(sK11,X1)) = k1_funct_1(k5_relat_1(sK11,X0),X1)
    | r2_hidden(X1,sK9) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1256])).

cnf(c_4530,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_funct_1(X0,k1_funct_1(sK11,X1)) = k1_funct_1(k5_relat_1(sK11,X0),X1)
    | r2_hidden(X1,sK9) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4425,c_34,c_35])).

cnf(c_4531,plain,
    ( k1_funct_1(X0,k1_funct_1(sK11,X1)) = k1_funct_1(k5_relat_1(sK11,X0),X1)
    | r2_hidden(X1,sK9) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4530])).

cnf(c_4549,plain,
    ( k1_funct_1(k5_relat_1(sK11,X0),sK8(sK9,sK11)) = k1_funct_1(X0,k1_funct_1(sK11,sK8(sK9,sK11)))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4007,c_4531])).

cnf(c_4686,plain,
    ( k1_funct_1(sK10,k1_funct_1(sK11,sK8(sK9,sK11))) = k1_funct_1(k5_relat_1(sK11,sK10),sK8(sK9,sK11))
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_1245,c_4549])).

cnf(c_23,negated_conjecture,
    ( k5_relat_1(sK11,sK10) = sK10 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4687,plain,
    ( k1_funct_1(sK10,k1_funct_1(sK11,sK8(sK9,sK11))) = k1_funct_1(sK10,sK8(sK9,sK11))
    | v1_funct_1(sK10) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4686,c_23])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,plain,
    ( v1_funct_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4691,plain,
    ( k1_funct_1(sK10,k1_funct_1(sK11,sK8(sK9,sK11))) = k1_funct_1(sK10,sK8(sK9,sK11)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4687,c_33])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1257,plain,
    ( X0 = X1
    | k1_funct_1(X2,X0) != k1_funct_1(X2,X1)
    | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
    | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4934,plain,
    ( k1_funct_1(sK10,sK8(sK9,sK11)) != k1_funct_1(sK10,X0)
    | k1_funct_1(sK11,sK8(sK9,sK11)) = X0
    | r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
    | r2_hidden(k1_funct_1(sK11,sK8(sK9,sK11)),k1_relat_1(sK10)) != iProver_top
    | v1_relat_1(sK10) != iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v2_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_4691,c_1257])).

cnf(c_27,negated_conjecture,
    ( k1_relat_1(sK10) = sK9 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4938,plain,
    ( k1_funct_1(sK10,sK8(sK9,sK11)) != k1_funct_1(sK10,X0)
    | k1_funct_1(sK11,sK8(sK9,sK11)) = X0
    | r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(k1_funct_1(sK11,sK8(sK9,sK11)),sK9) != iProver_top
    | v1_relat_1(sK10) != iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v2_funct_1(sK10) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4934,c_27])).

cnf(c_32,plain,
    ( v1_relat_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_24,negated_conjecture,
    ( v2_funct_1(sK10) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_37,plain,
    ( v2_funct_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5029,plain,
    ( r2_hidden(k1_funct_1(sK11,sK8(sK9,sK11)),sK9) != iProver_top
    | r2_hidden(X0,sK9) != iProver_top
    | k1_funct_1(sK11,sK8(sK9,sK11)) = X0
    | k1_funct_1(sK10,sK8(sK9,sK11)) != k1_funct_1(sK10,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4938,c_32,c_33,c_37])).

cnf(c_5030,plain,
    ( k1_funct_1(sK10,sK8(sK9,sK11)) != k1_funct_1(sK10,X0)
    | k1_funct_1(sK11,sK8(sK9,sK11)) = X0
    | r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(k1_funct_1(sK11,sK8(sK9,sK11)),sK9) != iProver_top ),
    inference(renaming,[status(thm)],[c_5029])).

cnf(c_5036,plain,
    ( k1_funct_1(sK11,sK8(sK9,sK11)) = sK8(sK9,sK11)
    | r2_hidden(sK8(sK9,sK11),sK9) != iProver_top
    | r2_hidden(k1_funct_1(sK11,sK8(sK9,sK11)),sK9) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5030])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK8(k1_relat_1(X0),X0)) != sK8(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1255,plain,
    ( k1_funct_1(X0,sK8(k1_relat_1(X0),X0)) != sK8(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4348,plain,
    ( k1_funct_1(sK11,sK8(sK9,sK11)) != sK8(k1_relat_1(sK11),sK11)
    | k6_relat_1(k1_relat_1(sK11)) = sK11
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1255])).

cnf(c_4351,plain,
    ( k1_funct_1(sK11,sK8(sK9,sK11)) != sK8(sK9,sK11)
    | k6_relat_1(sK9) = sK11
    | v1_relat_1(sK11) != iProver_top
    | v1_funct_1(sK11) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4348,c_26])).

cnf(c_5388,plain,
    ( r2_hidden(k1_funct_1(sK11,sK8(sK9,sK11)),sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5036,c_34,c_35,c_22,c_3908,c_4351])).

cnf(c_13125,plain,
    ( r2_hidden(sK2(sK11,sK8(sK9,sK11)),sK9) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12526,c_5388])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13669,c_13125])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.44/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.03  
% 3.44/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.44/1.03  
% 3.44/1.03  ------  iProver source info
% 3.44/1.03  
% 3.44/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.44/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.44/1.03  git: non_committed_changes: false
% 3.44/1.03  git: last_make_outside_of_git: false
% 3.44/1.03  
% 3.44/1.03  ------ 
% 3.44/1.03  
% 3.44/1.03  ------ Input Options
% 3.44/1.03  
% 3.44/1.03  --out_options                           all
% 3.44/1.03  --tptp_safe_out                         true
% 3.44/1.03  --problem_path                          ""
% 3.44/1.03  --include_path                          ""
% 3.44/1.03  --clausifier                            res/vclausify_rel
% 3.44/1.03  --clausifier_options                    ""
% 3.44/1.03  --stdin                                 false
% 3.44/1.03  --stats_out                             all
% 3.44/1.03  
% 3.44/1.03  ------ General Options
% 3.44/1.03  
% 3.44/1.03  --fof                                   false
% 3.44/1.03  --time_out_real                         305.
% 3.44/1.03  --time_out_virtual                      -1.
% 3.44/1.03  --symbol_type_check                     false
% 3.44/1.03  --clausify_out                          false
% 3.44/1.03  --sig_cnt_out                           false
% 3.44/1.03  --trig_cnt_out                          false
% 3.44/1.03  --trig_cnt_out_tolerance                1.
% 3.44/1.03  --trig_cnt_out_sk_spl                   false
% 3.44/1.03  --abstr_cl_out                          false
% 3.44/1.03  
% 3.44/1.03  ------ Global Options
% 3.44/1.03  
% 3.44/1.03  --schedule                              default
% 3.44/1.03  --add_important_lit                     false
% 3.44/1.03  --prop_solver_per_cl                    1000
% 3.44/1.03  --min_unsat_core                        false
% 3.44/1.03  --soft_assumptions                      false
% 3.44/1.03  --soft_lemma_size                       3
% 3.44/1.03  --prop_impl_unit_size                   0
% 3.44/1.03  --prop_impl_unit                        []
% 3.44/1.03  --share_sel_clauses                     true
% 3.44/1.03  --reset_solvers                         false
% 3.44/1.03  --bc_imp_inh                            [conj_cone]
% 3.44/1.03  --conj_cone_tolerance                   3.
% 3.44/1.03  --extra_neg_conj                        none
% 3.44/1.03  --large_theory_mode                     true
% 3.44/1.03  --prolific_symb_bound                   200
% 3.44/1.03  --lt_threshold                          2000
% 3.44/1.03  --clause_weak_htbl                      true
% 3.44/1.03  --gc_record_bc_elim                     false
% 3.44/1.03  
% 3.44/1.03  ------ Preprocessing Options
% 3.44/1.03  
% 3.44/1.03  --preprocessing_flag                    true
% 3.44/1.03  --time_out_prep_mult                    0.1
% 3.44/1.03  --splitting_mode                        input
% 3.44/1.03  --splitting_grd                         true
% 3.44/1.03  --splitting_cvd                         false
% 3.44/1.03  --splitting_cvd_svl                     false
% 3.44/1.03  --splitting_nvd                         32
% 3.44/1.03  --sub_typing                            true
% 3.44/1.03  --prep_gs_sim                           true
% 3.44/1.03  --prep_unflatten                        true
% 3.44/1.03  --prep_res_sim                          true
% 3.44/1.03  --prep_upred                            true
% 3.44/1.03  --prep_sem_filter                       exhaustive
% 3.44/1.03  --prep_sem_filter_out                   false
% 3.44/1.03  --pred_elim                             true
% 3.44/1.03  --res_sim_input                         true
% 3.44/1.03  --eq_ax_congr_red                       true
% 3.44/1.03  --pure_diseq_elim                       true
% 3.44/1.03  --brand_transform                       false
% 3.44/1.03  --non_eq_to_eq                          false
% 3.44/1.03  --prep_def_merge                        true
% 3.44/1.03  --prep_def_merge_prop_impl              false
% 3.44/1.03  --prep_def_merge_mbd                    true
% 3.44/1.03  --prep_def_merge_tr_red                 false
% 3.44/1.03  --prep_def_merge_tr_cl                  false
% 3.44/1.03  --smt_preprocessing                     true
% 3.44/1.03  --smt_ac_axioms                         fast
% 3.44/1.03  --preprocessed_out                      false
% 3.44/1.03  --preprocessed_stats                    false
% 3.44/1.03  
% 3.44/1.03  ------ Abstraction refinement Options
% 3.44/1.03  
% 3.44/1.03  --abstr_ref                             []
% 3.44/1.03  --abstr_ref_prep                        false
% 3.44/1.03  --abstr_ref_until_sat                   false
% 3.44/1.03  --abstr_ref_sig_restrict                funpre
% 3.44/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.44/1.03  --abstr_ref_under                       []
% 3.44/1.03  
% 3.44/1.03  ------ SAT Options
% 3.44/1.03  
% 3.44/1.03  --sat_mode                              false
% 3.44/1.03  --sat_fm_restart_options                ""
% 3.44/1.03  --sat_gr_def                            false
% 3.44/1.03  --sat_epr_types                         true
% 3.44/1.03  --sat_non_cyclic_types                  false
% 3.44/1.03  --sat_finite_models                     false
% 3.44/1.03  --sat_fm_lemmas                         false
% 3.44/1.03  --sat_fm_prep                           false
% 3.44/1.03  --sat_fm_uc_incr                        true
% 3.44/1.03  --sat_out_model                         small
% 3.44/1.03  --sat_out_clauses                       false
% 3.44/1.03  
% 3.44/1.03  ------ QBF Options
% 3.44/1.03  
% 3.44/1.03  --qbf_mode                              false
% 3.44/1.03  --qbf_elim_univ                         false
% 3.44/1.03  --qbf_dom_inst                          none
% 3.44/1.03  --qbf_dom_pre_inst                      false
% 3.44/1.03  --qbf_sk_in                             false
% 3.44/1.03  --qbf_pred_elim                         true
% 3.44/1.03  --qbf_split                             512
% 3.44/1.03  
% 3.44/1.03  ------ BMC1 Options
% 3.44/1.03  
% 3.44/1.03  --bmc1_incremental                      false
% 3.44/1.03  --bmc1_axioms                           reachable_all
% 3.44/1.03  --bmc1_min_bound                        0
% 3.44/1.03  --bmc1_max_bound                        -1
% 3.44/1.03  --bmc1_max_bound_default                -1
% 3.44/1.03  --bmc1_symbol_reachability              true
% 3.44/1.03  --bmc1_property_lemmas                  false
% 3.44/1.03  --bmc1_k_induction                      false
% 3.44/1.03  --bmc1_non_equiv_states                 false
% 3.44/1.03  --bmc1_deadlock                         false
% 3.44/1.03  --bmc1_ucm                              false
% 3.44/1.03  --bmc1_add_unsat_core                   none
% 3.44/1.03  --bmc1_unsat_core_children              false
% 3.44/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.44/1.03  --bmc1_out_stat                         full
% 3.44/1.03  --bmc1_ground_init                      false
% 3.44/1.03  --bmc1_pre_inst_next_state              false
% 3.44/1.03  --bmc1_pre_inst_state                   false
% 3.44/1.03  --bmc1_pre_inst_reach_state             false
% 3.44/1.03  --bmc1_out_unsat_core                   false
% 3.44/1.03  --bmc1_aig_witness_out                  false
% 3.44/1.03  --bmc1_verbose                          false
% 3.44/1.03  --bmc1_dump_clauses_tptp                false
% 3.44/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.44/1.03  --bmc1_dump_file                        -
% 3.44/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.44/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.44/1.03  --bmc1_ucm_extend_mode                  1
% 3.44/1.03  --bmc1_ucm_init_mode                    2
% 3.44/1.03  --bmc1_ucm_cone_mode                    none
% 3.44/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.44/1.03  --bmc1_ucm_relax_model                  4
% 3.44/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.44/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.44/1.03  --bmc1_ucm_layered_model                none
% 3.44/1.03  --bmc1_ucm_max_lemma_size               10
% 3.44/1.03  
% 3.44/1.03  ------ AIG Options
% 3.44/1.03  
% 3.44/1.03  --aig_mode                              false
% 3.44/1.03  
% 3.44/1.03  ------ Instantiation Options
% 3.44/1.03  
% 3.44/1.03  --instantiation_flag                    true
% 3.44/1.03  --inst_sos_flag                         true
% 3.44/1.03  --inst_sos_phase                        true
% 3.44/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.44/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.44/1.03  --inst_lit_sel_side                     num_symb
% 3.44/1.03  --inst_solver_per_active                1400
% 3.44/1.03  --inst_solver_calls_frac                1.
% 3.44/1.03  --inst_passive_queue_type               priority_queues
% 3.44/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.44/1.03  --inst_passive_queues_freq              [25;2]
% 3.44/1.03  --inst_dismatching                      true
% 3.44/1.03  --inst_eager_unprocessed_to_passive     true
% 3.44/1.03  --inst_prop_sim_given                   true
% 3.44/1.03  --inst_prop_sim_new                     false
% 3.44/1.03  --inst_subs_new                         false
% 3.44/1.03  --inst_eq_res_simp                      false
% 3.44/1.03  --inst_subs_given                       false
% 3.44/1.03  --inst_orphan_elimination               true
% 3.44/1.03  --inst_learning_loop_flag               true
% 3.44/1.03  --inst_learning_start                   3000
% 3.44/1.03  --inst_learning_factor                  2
% 3.44/1.03  --inst_start_prop_sim_after_learn       3
% 3.44/1.03  --inst_sel_renew                        solver
% 3.44/1.03  --inst_lit_activity_flag                true
% 3.44/1.03  --inst_restr_to_given                   false
% 3.44/1.03  --inst_activity_threshold               500
% 3.44/1.03  --inst_out_proof                        true
% 3.44/1.03  
% 3.44/1.03  ------ Resolution Options
% 3.44/1.03  
% 3.44/1.03  --resolution_flag                       true
% 3.44/1.03  --res_lit_sel                           adaptive
% 3.44/1.03  --res_lit_sel_side                      none
% 3.44/1.03  --res_ordering                          kbo
% 3.44/1.03  --res_to_prop_solver                    active
% 3.44/1.03  --res_prop_simpl_new                    false
% 3.44/1.03  --res_prop_simpl_given                  true
% 3.44/1.03  --res_passive_queue_type                priority_queues
% 3.44/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.44/1.03  --res_passive_queues_freq               [15;5]
% 3.44/1.03  --res_forward_subs                      full
% 3.44/1.03  --res_backward_subs                     full
% 3.44/1.03  --res_forward_subs_resolution           true
% 3.44/1.03  --res_backward_subs_resolution          true
% 3.44/1.03  --res_orphan_elimination                true
% 3.44/1.03  --res_time_limit                        2.
% 3.44/1.03  --res_out_proof                         true
% 3.44/1.03  
% 3.44/1.03  ------ Superposition Options
% 3.44/1.03  
% 3.44/1.03  --superposition_flag                    true
% 3.44/1.03  --sup_passive_queue_type                priority_queues
% 3.44/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.44/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.44/1.03  --demod_completeness_check              fast
% 3.44/1.03  --demod_use_ground                      true
% 3.44/1.03  --sup_to_prop_solver                    passive
% 3.44/1.03  --sup_prop_simpl_new                    true
% 3.44/1.03  --sup_prop_simpl_given                  true
% 3.44/1.03  --sup_fun_splitting                     true
% 3.44/1.03  --sup_smt_interval                      50000
% 3.44/1.03  
% 3.44/1.03  ------ Superposition Simplification Setup
% 3.44/1.03  
% 3.44/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.44/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.44/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.44/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.44/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.44/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.44/1.03  --sup_immed_triv                        [TrivRules]
% 3.44/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.03  --sup_immed_bw_main                     []
% 3.44/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.44/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.44/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.03  --sup_input_bw                          []
% 3.44/1.03  
% 3.44/1.03  ------ Combination Options
% 3.44/1.03  
% 3.44/1.03  --comb_res_mult                         3
% 3.44/1.03  --comb_sup_mult                         2
% 3.44/1.03  --comb_inst_mult                        10
% 3.44/1.03  
% 3.44/1.03  ------ Debug Options
% 3.44/1.03  
% 3.44/1.03  --dbg_backtrace                         false
% 3.44/1.03  --dbg_dump_prop_clauses                 false
% 3.44/1.03  --dbg_dump_prop_clauses_file            -
% 3.44/1.03  --dbg_out_stat                          false
% 3.44/1.03  ------ Parsing...
% 3.44/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.44/1.03  
% 3.44/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.44/1.03  
% 3.44/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.44/1.03  
% 3.44/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/1.03  ------ Proving...
% 3.44/1.03  ------ Problem Properties 
% 3.44/1.03  
% 3.44/1.03  
% 3.44/1.03  clauses                                 30
% 3.44/1.03  conjectures                             9
% 3.44/1.03  EPR                                     5
% 3.44/1.03  Horn                                    24
% 3.44/1.03  unary                                   9
% 3.44/1.03  binary                                  5
% 3.44/1.03  lits                                    83
% 3.44/1.03  lits eq                                 19
% 3.44/1.03  fd_pure                                 0
% 3.44/1.03  fd_pseudo                               0
% 3.44/1.03  fd_cond                                 0
% 3.44/1.03  fd_pseudo_cond                          6
% 3.44/1.03  AC symbols                              0
% 3.44/1.03  
% 3.44/1.03  ------ Schedule dynamic 5 is on 
% 3.44/1.03  
% 3.44/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.44/1.03  
% 3.44/1.03  
% 3.44/1.03  ------ 
% 3.44/1.03  Current options:
% 3.44/1.03  ------ 
% 3.44/1.03  
% 3.44/1.03  ------ Input Options
% 3.44/1.03  
% 3.44/1.03  --out_options                           all
% 3.44/1.03  --tptp_safe_out                         true
% 3.44/1.03  --problem_path                          ""
% 3.44/1.03  --include_path                          ""
% 3.44/1.03  --clausifier                            res/vclausify_rel
% 3.44/1.03  --clausifier_options                    ""
% 3.44/1.03  --stdin                                 false
% 3.44/1.03  --stats_out                             all
% 3.44/1.03  
% 3.44/1.03  ------ General Options
% 3.44/1.03  
% 3.44/1.03  --fof                                   false
% 3.44/1.03  --time_out_real                         305.
% 3.44/1.03  --time_out_virtual                      -1.
% 3.44/1.03  --symbol_type_check                     false
% 3.44/1.03  --clausify_out                          false
% 3.44/1.03  --sig_cnt_out                           false
% 3.44/1.03  --trig_cnt_out                          false
% 3.44/1.03  --trig_cnt_out_tolerance                1.
% 3.44/1.03  --trig_cnt_out_sk_spl                   false
% 3.44/1.03  --abstr_cl_out                          false
% 3.44/1.03  
% 3.44/1.03  ------ Global Options
% 3.44/1.03  
% 3.44/1.03  --schedule                              default
% 3.44/1.03  --add_important_lit                     false
% 3.44/1.03  --prop_solver_per_cl                    1000
% 3.44/1.03  --min_unsat_core                        false
% 3.44/1.03  --soft_assumptions                      false
% 3.44/1.03  --soft_lemma_size                       3
% 3.44/1.03  --prop_impl_unit_size                   0
% 3.44/1.03  --prop_impl_unit                        []
% 3.44/1.03  --share_sel_clauses                     true
% 3.44/1.03  --reset_solvers                         false
% 3.44/1.03  --bc_imp_inh                            [conj_cone]
% 3.44/1.03  --conj_cone_tolerance                   3.
% 3.44/1.03  --extra_neg_conj                        none
% 3.44/1.03  --large_theory_mode                     true
% 3.44/1.03  --prolific_symb_bound                   200
% 3.44/1.03  --lt_threshold                          2000
% 3.44/1.03  --clause_weak_htbl                      true
% 3.44/1.03  --gc_record_bc_elim                     false
% 3.44/1.03  
% 3.44/1.03  ------ Preprocessing Options
% 3.44/1.03  
% 3.44/1.03  --preprocessing_flag                    true
% 3.44/1.03  --time_out_prep_mult                    0.1
% 3.44/1.03  --splitting_mode                        input
% 3.44/1.03  --splitting_grd                         true
% 3.44/1.03  --splitting_cvd                         false
% 3.44/1.03  --splitting_cvd_svl                     false
% 3.44/1.03  --splitting_nvd                         32
% 3.44/1.03  --sub_typing                            true
% 3.44/1.03  --prep_gs_sim                           true
% 3.44/1.03  --prep_unflatten                        true
% 3.44/1.03  --prep_res_sim                          true
% 3.44/1.03  --prep_upred                            true
% 3.44/1.03  --prep_sem_filter                       exhaustive
% 3.44/1.03  --prep_sem_filter_out                   false
% 3.44/1.03  --pred_elim                             true
% 3.44/1.03  --res_sim_input                         true
% 3.44/1.03  --eq_ax_congr_red                       true
% 3.44/1.03  --pure_diseq_elim                       true
% 3.44/1.03  --brand_transform                       false
% 3.44/1.03  --non_eq_to_eq                          false
% 3.44/1.03  --prep_def_merge                        true
% 3.44/1.03  --prep_def_merge_prop_impl              false
% 3.44/1.03  --prep_def_merge_mbd                    true
% 3.44/1.03  --prep_def_merge_tr_red                 false
% 3.44/1.03  --prep_def_merge_tr_cl                  false
% 3.44/1.03  --smt_preprocessing                     true
% 3.44/1.03  --smt_ac_axioms                         fast
% 3.44/1.03  --preprocessed_out                      false
% 3.44/1.03  --preprocessed_stats                    false
% 3.44/1.03  
% 3.44/1.03  ------ Abstraction refinement Options
% 3.44/1.03  
% 3.44/1.03  --abstr_ref                             []
% 3.44/1.03  --abstr_ref_prep                        false
% 3.44/1.03  --abstr_ref_until_sat                   false
% 3.44/1.03  --abstr_ref_sig_restrict                funpre
% 3.44/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.44/1.03  --abstr_ref_under                       []
% 3.44/1.03  
% 3.44/1.03  ------ SAT Options
% 3.44/1.03  
% 3.44/1.03  --sat_mode                              false
% 3.44/1.03  --sat_fm_restart_options                ""
% 3.44/1.03  --sat_gr_def                            false
% 3.44/1.03  --sat_epr_types                         true
% 3.44/1.03  --sat_non_cyclic_types                  false
% 3.44/1.03  --sat_finite_models                     false
% 3.44/1.03  --sat_fm_lemmas                         false
% 3.44/1.03  --sat_fm_prep                           false
% 3.44/1.03  --sat_fm_uc_incr                        true
% 3.44/1.03  --sat_out_model                         small
% 3.44/1.03  --sat_out_clauses                       false
% 3.44/1.03  
% 3.44/1.03  ------ QBF Options
% 3.44/1.03  
% 3.44/1.03  --qbf_mode                              false
% 3.44/1.03  --qbf_elim_univ                         false
% 3.44/1.03  --qbf_dom_inst                          none
% 3.44/1.03  --qbf_dom_pre_inst                      false
% 3.44/1.03  --qbf_sk_in                             false
% 3.44/1.03  --qbf_pred_elim                         true
% 3.44/1.03  --qbf_split                             512
% 3.44/1.03  
% 3.44/1.03  ------ BMC1 Options
% 3.44/1.03  
% 3.44/1.03  --bmc1_incremental                      false
% 3.44/1.03  --bmc1_axioms                           reachable_all
% 3.44/1.03  --bmc1_min_bound                        0
% 3.44/1.03  --bmc1_max_bound                        -1
% 3.44/1.03  --bmc1_max_bound_default                -1
% 3.44/1.03  --bmc1_symbol_reachability              true
% 3.44/1.03  --bmc1_property_lemmas                  false
% 3.44/1.03  --bmc1_k_induction                      false
% 3.44/1.03  --bmc1_non_equiv_states                 false
% 3.44/1.03  --bmc1_deadlock                         false
% 3.44/1.03  --bmc1_ucm                              false
% 3.44/1.03  --bmc1_add_unsat_core                   none
% 3.44/1.03  --bmc1_unsat_core_children              false
% 3.44/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.44/1.03  --bmc1_out_stat                         full
% 3.44/1.03  --bmc1_ground_init                      false
% 3.44/1.03  --bmc1_pre_inst_next_state              false
% 3.44/1.03  --bmc1_pre_inst_state                   false
% 3.44/1.03  --bmc1_pre_inst_reach_state             false
% 3.44/1.03  --bmc1_out_unsat_core                   false
% 3.44/1.03  --bmc1_aig_witness_out                  false
% 3.44/1.03  --bmc1_verbose                          false
% 3.44/1.03  --bmc1_dump_clauses_tptp                false
% 3.44/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.44/1.03  --bmc1_dump_file                        -
% 3.44/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.44/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.44/1.03  --bmc1_ucm_extend_mode                  1
% 3.44/1.03  --bmc1_ucm_init_mode                    2
% 3.44/1.03  --bmc1_ucm_cone_mode                    none
% 3.44/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.44/1.03  --bmc1_ucm_relax_model                  4
% 3.44/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.44/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.44/1.03  --bmc1_ucm_layered_model                none
% 3.44/1.03  --bmc1_ucm_max_lemma_size               10
% 3.44/1.03  
% 3.44/1.03  ------ AIG Options
% 3.44/1.03  
% 3.44/1.03  --aig_mode                              false
% 3.44/1.03  
% 3.44/1.03  ------ Instantiation Options
% 3.44/1.03  
% 3.44/1.03  --instantiation_flag                    true
% 3.44/1.03  --inst_sos_flag                         true
% 3.44/1.03  --inst_sos_phase                        true
% 3.44/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.44/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.44/1.03  --inst_lit_sel_side                     none
% 3.44/1.03  --inst_solver_per_active                1400
% 3.44/1.03  --inst_solver_calls_frac                1.
% 3.44/1.03  --inst_passive_queue_type               priority_queues
% 3.44/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.44/1.03  --inst_passive_queues_freq              [25;2]
% 3.44/1.03  --inst_dismatching                      true
% 3.44/1.03  --inst_eager_unprocessed_to_passive     true
% 3.44/1.03  --inst_prop_sim_given                   true
% 3.44/1.03  --inst_prop_sim_new                     false
% 3.44/1.03  --inst_subs_new                         false
% 3.44/1.03  --inst_eq_res_simp                      false
% 3.44/1.03  --inst_subs_given                       false
% 3.44/1.03  --inst_orphan_elimination               true
% 3.44/1.03  --inst_learning_loop_flag               true
% 3.44/1.03  --inst_learning_start                   3000
% 3.44/1.03  --inst_learning_factor                  2
% 3.44/1.03  --inst_start_prop_sim_after_learn       3
% 3.44/1.03  --inst_sel_renew                        solver
% 3.44/1.03  --inst_lit_activity_flag                true
% 3.44/1.03  --inst_restr_to_given                   false
% 3.44/1.03  --inst_activity_threshold               500
% 3.44/1.03  --inst_out_proof                        true
% 3.44/1.03  
% 3.44/1.03  ------ Resolution Options
% 3.44/1.03  
% 3.44/1.03  --resolution_flag                       false
% 3.44/1.03  --res_lit_sel                           adaptive
% 3.44/1.03  --res_lit_sel_side                      none
% 3.44/1.03  --res_ordering                          kbo
% 3.44/1.03  --res_to_prop_solver                    active
% 3.44/1.03  --res_prop_simpl_new                    false
% 3.44/1.03  --res_prop_simpl_given                  true
% 3.44/1.03  --res_passive_queue_type                priority_queues
% 3.44/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.44/1.03  --res_passive_queues_freq               [15;5]
% 3.44/1.03  --res_forward_subs                      full
% 3.44/1.03  --res_backward_subs                     full
% 3.44/1.03  --res_forward_subs_resolution           true
% 3.44/1.03  --res_backward_subs_resolution          true
% 3.44/1.03  --res_orphan_elimination                true
% 3.44/1.03  --res_time_limit                        2.
% 3.44/1.03  --res_out_proof                         true
% 3.44/1.03  
% 3.44/1.03  ------ Superposition Options
% 3.44/1.03  
% 3.44/1.03  --superposition_flag                    true
% 3.44/1.03  --sup_passive_queue_type                priority_queues
% 3.44/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.44/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.44/1.03  --demod_completeness_check              fast
% 3.44/1.03  --demod_use_ground                      true
% 3.44/1.03  --sup_to_prop_solver                    passive
% 3.44/1.03  --sup_prop_simpl_new                    true
% 3.44/1.03  --sup_prop_simpl_given                  true
% 3.44/1.03  --sup_fun_splitting                     true
% 3.44/1.03  --sup_smt_interval                      50000
% 3.44/1.03  
% 3.44/1.03  ------ Superposition Simplification Setup
% 3.44/1.03  
% 3.44/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.44/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.44/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.44/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.44/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.44/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.44/1.03  --sup_immed_triv                        [TrivRules]
% 3.44/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.03  --sup_immed_bw_main                     []
% 3.44/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.44/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.44/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.03  --sup_input_bw                          []
% 3.44/1.03  
% 3.44/1.03  ------ Combination Options
% 3.44/1.03  
% 3.44/1.03  --comb_res_mult                         3
% 3.44/1.03  --comb_sup_mult                         2
% 3.44/1.03  --comb_inst_mult                        10
% 3.44/1.03  
% 3.44/1.03  ------ Debug Options
% 3.44/1.03  
% 3.44/1.03  --dbg_backtrace                         false
% 3.44/1.03  --dbg_dump_prop_clauses                 false
% 3.44/1.03  --dbg_dump_prop_clauses_file            -
% 3.44/1.03  --dbg_out_stat                          false
% 3.44/1.03  
% 3.44/1.03  
% 3.44/1.03  
% 3.44/1.03  
% 3.44/1.03  ------ Proving...
% 3.44/1.03  
% 3.44/1.03  
% 3.44/1.03  % SZS status Theorem for theBenchmark.p
% 3.44/1.03  
% 3.44/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.44/1.03  
% 3.44/1.03  fof(f8,conjecture,(
% 3.44/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 3.44/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.03  
% 3.44/1.03  fof(f9,negated_conjecture,(
% 3.44/1.03    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 3.44/1.03    inference(negated_conjecture,[],[f8])).
% 3.44/1.03  
% 3.44/1.03  fof(f20,plain,(
% 3.44/1.03    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.44/1.03    inference(ennf_transformation,[],[f9])).
% 3.44/1.03  
% 3.44/1.03  fof(f21,plain,(
% 3.44/1.03    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.44/1.03    inference(flattening,[],[f20])).
% 3.44/1.03  
% 3.44/1.03  fof(f46,plain,(
% 3.44/1.03    ( ! [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k6_relat_1(X0) != sK11 & k5_relat_1(sK11,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(sK11),X0) & k1_relat_1(sK11) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(sK11) & v1_relat_1(sK11))) )),
% 3.44/1.03    introduced(choice_axiom,[])).
% 3.44/1.03  
% 3.44/1.03  fof(f45,plain,(
% 3.44/1.03    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k6_relat_1(sK9) != X2 & k5_relat_1(X2,sK10) = sK10 & v2_funct_1(sK10) & r1_tarski(k2_relat_1(X2),sK9) & k1_relat_1(X2) = sK9 & k1_relat_1(sK10) = sK9 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK10) & v1_relat_1(sK10))),
% 3.44/1.03    introduced(choice_axiom,[])).
% 3.44/1.03  
% 3.44/1.03  fof(f47,plain,(
% 3.44/1.03    (k6_relat_1(sK9) != sK11 & k5_relat_1(sK11,sK10) = sK10 & v2_funct_1(sK10) & r1_tarski(k2_relat_1(sK11),sK9) & k1_relat_1(sK11) = sK9 & k1_relat_1(sK10) = sK9 & v1_funct_1(sK11) & v1_relat_1(sK11)) & v1_funct_1(sK10) & v1_relat_1(sK10)),
% 3.44/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f21,f46,f45])).
% 3.44/1.03  
% 3.44/1.03  fof(f75,plain,(
% 3.44/1.03    k1_relat_1(sK11) = sK9),
% 3.44/1.03    inference(cnf_transformation,[],[f47])).
% 3.44/1.03  
% 3.44/1.03  fof(f6,axiom,(
% 3.44/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 3.44/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.03  
% 3.44/1.03  fof(f16,plain,(
% 3.44/1.03    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.44/1.03    inference(ennf_transformation,[],[f6])).
% 3.44/1.03  
% 3.44/1.03  fof(f17,plain,(
% 3.44/1.03    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.44/1.03    inference(flattening,[],[f16])).
% 3.44/1.03  
% 3.44/1.03  fof(f38,plain,(
% 3.44/1.03    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.44/1.03    inference(nnf_transformation,[],[f17])).
% 3.44/1.03  
% 3.44/1.03  fof(f39,plain,(
% 3.44/1.03    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.44/1.03    inference(flattening,[],[f38])).
% 3.44/1.03  
% 3.44/1.03  fof(f40,plain,(
% 3.44/1.03    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.44/1.03    inference(rectify,[],[f39])).
% 3.44/1.03  
% 3.44/1.03  fof(f41,plain,(
% 3.44/1.03    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK8(X0,X1)) != sK8(X0,X1) & r2_hidden(sK8(X0,X1),X0)))),
% 3.44/1.03    introduced(choice_axiom,[])).
% 3.44/1.03  
% 3.44/1.03  fof(f42,plain,(
% 3.44/1.03    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK8(X0,X1)) != sK8(X0,X1) & r2_hidden(sK8(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.44/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f40,f41])).
% 3.44/1.03  
% 3.44/1.03  fof(f65,plain,(
% 3.44/1.03    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK8(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.44/1.03    inference(cnf_transformation,[],[f42])).
% 3.44/1.03  
% 3.44/1.03  fof(f85,plain,(
% 3.44/1.03    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | r2_hidden(sK8(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.44/1.03    inference(equality_resolution,[],[f65])).
% 3.44/1.03  
% 3.44/1.03  fof(f72,plain,(
% 3.44/1.03    v1_relat_1(sK11)),
% 3.44/1.03    inference(cnf_transformation,[],[f47])).
% 3.44/1.03  
% 3.44/1.03  fof(f73,plain,(
% 3.44/1.03    v1_funct_1(sK11)),
% 3.44/1.03    inference(cnf_transformation,[],[f47])).
% 3.44/1.03  
% 3.44/1.03  fof(f79,plain,(
% 3.44/1.03    k6_relat_1(sK9) != sK11),
% 3.44/1.03    inference(cnf_transformation,[],[f47])).
% 3.44/1.03  
% 3.44/1.03  fof(f2,axiom,(
% 3.44/1.03    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 3.44/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.03  
% 3.44/1.03  fof(f22,plain,(
% 3.44/1.03    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 3.44/1.03    inference(nnf_transformation,[],[f2])).
% 3.44/1.03  
% 3.44/1.03  fof(f23,plain,(
% 3.44/1.03    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.44/1.03    inference(rectify,[],[f22])).
% 3.44/1.03  
% 3.44/1.03  fof(f26,plain,(
% 3.44/1.03    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0))),
% 3.44/1.03    introduced(choice_axiom,[])).
% 3.44/1.03  
% 3.44/1.03  fof(f25,plain,(
% 3.44/1.03    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0))) )),
% 3.44/1.03    introduced(choice_axiom,[])).
% 3.44/1.03  
% 3.44/1.03  fof(f24,plain,(
% 3.44/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.44/1.03    introduced(choice_axiom,[])).
% 3.44/1.03  
% 3.44/1.03  fof(f27,plain,(
% 3.44/1.03    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 3.44/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).
% 3.44/1.03  
% 3.44/1.03  fof(f49,plain,(
% 3.44/1.03    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 3.44/1.03    inference(cnf_transformation,[],[f27])).
% 3.44/1.03  
% 3.44/1.03  fof(f81,plain,(
% 3.44/1.03    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 3.44/1.03    inference(equality_resolution,[],[f49])).
% 3.44/1.03  
% 3.44/1.03  fof(f7,axiom,(
% 3.44/1.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.44/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.03  
% 3.44/1.03  fof(f18,plain,(
% 3.44/1.03    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.44/1.03    inference(ennf_transformation,[],[f7])).
% 3.44/1.03  
% 3.44/1.03  fof(f19,plain,(
% 3.44/1.03    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.44/1.03    inference(flattening,[],[f18])).
% 3.44/1.03  
% 3.44/1.03  fof(f43,plain,(
% 3.44/1.03    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.44/1.03    inference(nnf_transformation,[],[f19])).
% 3.44/1.03  
% 3.44/1.03  fof(f44,plain,(
% 3.44/1.03    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.44/1.03    inference(flattening,[],[f43])).
% 3.44/1.03  
% 3.44/1.03  fof(f68,plain,(
% 3.44/1.03    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.44/1.03    inference(cnf_transformation,[],[f44])).
% 3.44/1.03  
% 3.44/1.03  fof(f69,plain,(
% 3.44/1.03    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.44/1.03    inference(cnf_transformation,[],[f44])).
% 3.44/1.03  
% 3.44/1.03  fof(f88,plain,(
% 3.44/1.03    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.44/1.03    inference(equality_resolution,[],[f69])).
% 3.44/1.03  
% 3.44/1.03  fof(f3,axiom,(
% 3.44/1.03    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.44/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.03  
% 3.44/1.03  fof(f28,plain,(
% 3.44/1.03    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.44/1.03    inference(nnf_transformation,[],[f3])).
% 3.44/1.03  
% 3.44/1.03  fof(f29,plain,(
% 3.44/1.03    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.44/1.03    inference(rectify,[],[f28])).
% 3.44/1.03  
% 3.44/1.03  fof(f32,plain,(
% 3.44/1.03    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 3.44/1.03    introduced(choice_axiom,[])).
% 3.44/1.03  
% 3.44/1.03  fof(f31,plain,(
% 3.44/1.03    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0))) )),
% 3.44/1.03    introduced(choice_axiom,[])).
% 3.44/1.03  
% 3.44/1.03  fof(f30,plain,(
% 3.44/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 3.44/1.03    introduced(choice_axiom,[])).
% 3.44/1.03  
% 3.44/1.03  fof(f33,plain,(
% 3.44/1.03    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.44/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).
% 3.44/1.03  
% 3.44/1.03  fof(f54,plain,(
% 3.44/1.03    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 3.44/1.03    inference(cnf_transformation,[],[f33])).
% 3.44/1.03  
% 3.44/1.03  fof(f82,plain,(
% 3.44/1.03    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 3.44/1.03    inference(equality_resolution,[],[f54])).
% 3.44/1.03  
% 3.44/1.03  fof(f1,axiom,(
% 3.44/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.44/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.03  
% 3.44/1.03  fof(f10,plain,(
% 3.44/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.44/1.03    inference(unused_predicate_definition_removal,[],[f1])).
% 3.44/1.03  
% 3.44/1.03  fof(f11,plain,(
% 3.44/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 3.44/1.03    inference(ennf_transformation,[],[f10])).
% 3.44/1.03  
% 3.44/1.03  fof(f48,plain,(
% 3.44/1.03    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 3.44/1.03    inference(cnf_transformation,[],[f11])).
% 3.44/1.03  
% 3.44/1.03  fof(f76,plain,(
% 3.44/1.03    r1_tarski(k2_relat_1(sK11),sK9)),
% 3.44/1.03    inference(cnf_transformation,[],[f47])).
% 3.44/1.03  
% 3.44/1.03  fof(f70,plain,(
% 3.44/1.03    v1_relat_1(sK10)),
% 3.44/1.03    inference(cnf_transformation,[],[f47])).
% 3.44/1.03  
% 3.44/1.03  fof(f5,axiom,(
% 3.44/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 3.44/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.03  
% 3.44/1.03  fof(f14,plain,(
% 3.44/1.03    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.44/1.03    inference(ennf_transformation,[],[f5])).
% 3.44/1.03  
% 3.44/1.03  fof(f15,plain,(
% 3.44/1.03    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.44/1.03    inference(flattening,[],[f14])).
% 3.44/1.03  
% 3.44/1.03  fof(f62,plain,(
% 3.44/1.03    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.44/1.03    inference(cnf_transformation,[],[f15])).
% 3.44/1.03  
% 3.44/1.03  fof(f78,plain,(
% 3.44/1.03    k5_relat_1(sK11,sK10) = sK10),
% 3.44/1.03    inference(cnf_transformation,[],[f47])).
% 3.44/1.03  
% 3.44/1.03  fof(f71,plain,(
% 3.44/1.03    v1_funct_1(sK10)),
% 3.44/1.03    inference(cnf_transformation,[],[f47])).
% 3.44/1.03  
% 3.44/1.03  fof(f4,axiom,(
% 3.44/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 3.44/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.03  
% 3.44/1.03  fof(f12,plain,(
% 3.44/1.03    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.44/1.03    inference(ennf_transformation,[],[f4])).
% 3.44/1.03  
% 3.44/1.03  fof(f13,plain,(
% 3.44/1.03    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.44/1.03    inference(flattening,[],[f12])).
% 3.44/1.03  
% 3.44/1.03  fof(f34,plain,(
% 3.44/1.03    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.44/1.03    inference(nnf_transformation,[],[f13])).
% 3.44/1.03  
% 3.44/1.03  fof(f35,plain,(
% 3.44/1.03    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.44/1.03    inference(rectify,[],[f34])).
% 3.44/1.03  
% 3.44/1.03  fof(f36,plain,(
% 3.44/1.03    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK6(X0) != sK7(X0) & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0))))),
% 3.44/1.03    introduced(choice_axiom,[])).
% 3.44/1.03  
% 3.44/1.03  fof(f37,plain,(
% 3.44/1.03    ! [X0] : (((v2_funct_1(X0) | (sK6(X0) != sK7(X0) & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.44/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f35,f36])).
% 3.44/1.03  
% 3.44/1.03  fof(f57,plain,(
% 3.44/1.03    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.44/1.03    inference(cnf_transformation,[],[f37])).
% 3.44/1.03  
% 3.44/1.03  fof(f74,plain,(
% 3.44/1.03    k1_relat_1(sK10) = sK9),
% 3.44/1.03    inference(cnf_transformation,[],[f47])).
% 3.44/1.03  
% 3.44/1.03  fof(f77,plain,(
% 3.44/1.03    v2_funct_1(sK10)),
% 3.44/1.03    inference(cnf_transformation,[],[f47])).
% 3.44/1.03  
% 3.44/1.03  fof(f66,plain,(
% 3.44/1.03    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | k1_funct_1(X1,sK8(X0,X1)) != sK8(X0,X1) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.44/1.03    inference(cnf_transformation,[],[f42])).
% 3.44/1.03  
% 3.44/1.03  fof(f84,plain,(
% 3.44/1.03    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k1_funct_1(X1,sK8(k1_relat_1(X1),X1)) != sK8(k1_relat_1(X1),X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.44/1.03    inference(equality_resolution,[],[f66])).
% 3.44/1.03  
% 3.44/1.03  cnf(c_26,negated_conjecture,
% 3.44/1.03      ( k1_relat_1(sK11) = sK9 ),
% 3.44/1.03      inference(cnf_transformation,[],[f75]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_16,plain,
% 3.44/1.03      ( r2_hidden(sK8(k1_relat_1(X0),X0),k1_relat_1(X0))
% 3.44/1.03      | ~ v1_relat_1(X0)
% 3.44/1.03      | ~ v1_funct_1(X0)
% 3.44/1.03      | k6_relat_1(k1_relat_1(X0)) = X0 ),
% 3.44/1.03      inference(cnf_transformation,[],[f85]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_1254,plain,
% 3.44/1.03      ( k6_relat_1(k1_relat_1(X0)) = X0
% 3.44/1.03      | r2_hidden(sK8(k1_relat_1(X0),X0),k1_relat_1(X0)) = iProver_top
% 3.44/1.03      | v1_relat_1(X0) != iProver_top
% 3.44/1.03      | v1_funct_1(X0) != iProver_top ),
% 3.44/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_3901,plain,
% 3.44/1.03      ( k6_relat_1(k1_relat_1(sK11)) = sK11
% 3.44/1.03      | r2_hidden(sK8(sK9,sK11),sK9) = iProver_top
% 3.44/1.03      | v1_relat_1(sK11) != iProver_top
% 3.44/1.03      | v1_funct_1(sK11) != iProver_top ),
% 3.44/1.03      inference(superposition,[status(thm)],[c_26,c_1254]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_3908,plain,
% 3.44/1.03      ( k6_relat_1(sK9) = sK11
% 3.44/1.03      | r2_hidden(sK8(sK9,sK11),sK9) = iProver_top
% 3.44/1.03      | v1_relat_1(sK11) != iProver_top
% 3.44/1.03      | v1_funct_1(sK11) != iProver_top ),
% 3.44/1.03      inference(light_normalisation,[status(thm)],[c_3901,c_26]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_29,negated_conjecture,
% 3.44/1.03      ( v1_relat_1(sK11) ),
% 3.44/1.03      inference(cnf_transformation,[],[f72]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_34,plain,
% 3.44/1.03      ( v1_relat_1(sK11) = iProver_top ),
% 3.44/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_28,negated_conjecture,
% 3.44/1.03      ( v1_funct_1(sK11) ),
% 3.44/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_35,plain,
% 3.44/1.03      ( v1_funct_1(sK11) = iProver_top ),
% 3.44/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_22,negated_conjecture,
% 3.44/1.03      ( k6_relat_1(sK9) != sK11 ),
% 3.44/1.03      inference(cnf_transformation,[],[f79]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_4007,plain,
% 3.44/1.03      ( r2_hidden(sK8(sK9,sK11),sK9) = iProver_top ),
% 3.44/1.03      inference(global_propositional_subsumption,
% 3.44/1.03                [status(thm)],
% 3.44/1.03                [c_3908,c_34,c_35,c_22]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_4,plain,
% 3.44/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.44/1.03      | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
% 3.44/1.03      inference(cnf_transformation,[],[f81]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_1266,plain,
% 3.44/1.03      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.44/1.03      | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) = iProver_top ),
% 3.44/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_20,plain,
% 3.44/1.03      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.44/1.03      | ~ v1_relat_1(X2)
% 3.44/1.03      | ~ v1_funct_1(X2)
% 3.44/1.03      | k1_funct_1(X2,X0) = X1 ),
% 3.44/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_1250,plain,
% 3.44/1.03      ( k1_funct_1(X0,X1) = X2
% 3.44/1.03      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 3.44/1.03      | v1_relat_1(X0) != iProver_top
% 3.44/1.03      | v1_funct_1(X0) != iProver_top ),
% 3.44/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_2180,plain,
% 3.44/1.03      ( k1_funct_1(X0,X1) = sK2(X0,X1)
% 3.44/1.03      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.44/1.03      | v1_relat_1(X0) != iProver_top
% 3.44/1.03      | v1_funct_1(X0) != iProver_top ),
% 3.44/1.03      inference(superposition,[status(thm)],[c_1266,c_1250]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_12288,plain,
% 3.44/1.03      ( k1_funct_1(sK11,X0) = sK2(sK11,X0)
% 3.44/1.03      | r2_hidden(X0,sK9) != iProver_top
% 3.44/1.03      | v1_relat_1(sK11) != iProver_top
% 3.44/1.03      | v1_funct_1(sK11) != iProver_top ),
% 3.44/1.03      inference(superposition,[status(thm)],[c_26,c_2180]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_12502,plain,
% 3.44/1.03      ( k1_funct_1(sK11,X0) = sK2(sK11,X0)
% 3.44/1.03      | r2_hidden(X0,sK9) != iProver_top ),
% 3.44/1.03      inference(global_propositional_subsumption,
% 3.44/1.03                [status(thm)],
% 3.44/1.03                [c_12288,c_34,c_35]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_12526,plain,
% 3.44/1.03      ( k1_funct_1(sK11,sK8(sK9,sK11)) = sK2(sK11,sK8(sK9,sK11)) ),
% 3.44/1.03      inference(superposition,[status(thm)],[c_4007,c_12502]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_19,plain,
% 3.44/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.44/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.44/1.03      | ~ v1_relat_1(X1)
% 3.44/1.03      | ~ v1_funct_1(X1) ),
% 3.44/1.03      inference(cnf_transformation,[],[f88]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_1251,plain,
% 3.44/1.03      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.44/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
% 3.44/1.03      | v1_relat_1(X1) != iProver_top
% 3.44/1.03      | v1_funct_1(X1) != iProver_top ),
% 3.44/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_13136,plain,
% 3.44/1.03      ( r2_hidden(sK8(sK9,sK11),k1_relat_1(sK11)) != iProver_top
% 3.44/1.03      | r2_hidden(k4_tarski(sK8(sK9,sK11),sK2(sK11,sK8(sK9,sK11))),sK11) = iProver_top
% 3.44/1.03      | v1_relat_1(sK11) != iProver_top
% 3.44/1.03      | v1_funct_1(sK11) != iProver_top ),
% 3.44/1.03      inference(superposition,[status(thm)],[c_12526,c_1251]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_13140,plain,
% 3.44/1.03      ( r2_hidden(sK8(sK9,sK11),sK9) != iProver_top
% 3.44/1.03      | r2_hidden(k4_tarski(sK8(sK9,sK11),sK2(sK11,sK8(sK9,sK11))),sK11) = iProver_top
% 3.44/1.03      | v1_relat_1(sK11) != iProver_top
% 3.44/1.03      | v1_funct_1(sK11) != iProver_top ),
% 3.44/1.03      inference(light_normalisation,[status(thm)],[c_13136,c_26]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_13146,plain,
% 3.44/1.03      ( r2_hidden(k4_tarski(sK8(sK9,sK11),sK2(sK11,sK8(sK9,sK11))),sK11) = iProver_top ),
% 3.44/1.03      inference(global_propositional_subsumption,
% 3.44/1.03                [status(thm)],
% 3.44/1.03                [c_13140,c_34,c_35,c_22,c_3908]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_7,plain,
% 3.44/1.03      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 3.44/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_1263,plain,
% 3.44/1.03      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 3.44/1.03      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top ),
% 3.44/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_13151,plain,
% 3.44/1.03      ( r2_hidden(sK2(sK11,sK8(sK9,sK11)),k2_relat_1(sK11)) = iProver_top ),
% 3.44/1.03      inference(superposition,[status(thm)],[c_13146,c_1263]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_0,plain,
% 3.44/1.03      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.44/1.03      inference(cnf_transformation,[],[f48]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_25,negated_conjecture,
% 3.44/1.03      ( r1_tarski(k2_relat_1(sK11),sK9) ),
% 3.44/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_309,plain,
% 3.44/1.03      ( ~ r2_hidden(X0,X1)
% 3.44/1.03      | r2_hidden(X0,X2)
% 3.44/1.03      | k2_relat_1(sK11) != X1
% 3.44/1.03      | sK9 != X2 ),
% 3.44/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_25]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_310,plain,
% 3.44/1.03      ( ~ r2_hidden(X0,k2_relat_1(sK11)) | r2_hidden(X0,sK9) ),
% 3.44/1.03      inference(unflattening,[status(thm)],[c_309]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_1244,plain,
% 3.44/1.03      ( r2_hidden(X0,k2_relat_1(sK11)) != iProver_top
% 3.44/1.03      | r2_hidden(X0,sK9) = iProver_top ),
% 3.44/1.03      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_13669,plain,
% 3.44/1.03      ( r2_hidden(sK2(sK11,sK8(sK9,sK11)),sK9) = iProver_top ),
% 3.44/1.03      inference(superposition,[status(thm)],[c_13151,c_1244]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_31,negated_conjecture,
% 3.44/1.03      ( v1_relat_1(sK10) ),
% 3.44/1.03      inference(cnf_transformation,[],[f70]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_1245,plain,
% 3.44/1.03      ( v1_relat_1(sK10) = iProver_top ),
% 3.44/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_14,plain,
% 3.44/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.44/1.03      | ~ v1_relat_1(X2)
% 3.44/1.03      | ~ v1_relat_1(X1)
% 3.44/1.03      | ~ v1_funct_1(X2)
% 3.44/1.03      | ~ v1_funct_1(X1)
% 3.44/1.03      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 3.44/1.03      inference(cnf_transformation,[],[f62]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_1256,plain,
% 3.44/1.03      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 3.44/1.03      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 3.44/1.03      | v1_relat_1(X0) != iProver_top
% 3.44/1.03      | v1_relat_1(X1) != iProver_top
% 3.44/1.03      | v1_funct_1(X0) != iProver_top
% 3.44/1.03      | v1_funct_1(X1) != iProver_top ),
% 3.44/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_4425,plain,
% 3.44/1.03      ( k1_funct_1(X0,k1_funct_1(sK11,X1)) = k1_funct_1(k5_relat_1(sK11,X0),X1)
% 3.44/1.03      | r2_hidden(X1,sK9) != iProver_top
% 3.44/1.03      | v1_relat_1(X0) != iProver_top
% 3.44/1.03      | v1_relat_1(sK11) != iProver_top
% 3.44/1.03      | v1_funct_1(X0) != iProver_top
% 3.44/1.03      | v1_funct_1(sK11) != iProver_top ),
% 3.44/1.03      inference(superposition,[status(thm)],[c_26,c_1256]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_4530,plain,
% 3.44/1.03      ( v1_funct_1(X0) != iProver_top
% 3.44/1.03      | k1_funct_1(X0,k1_funct_1(sK11,X1)) = k1_funct_1(k5_relat_1(sK11,X0),X1)
% 3.44/1.03      | r2_hidden(X1,sK9) != iProver_top
% 3.44/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.44/1.03      inference(global_propositional_subsumption,
% 3.44/1.03                [status(thm)],
% 3.44/1.03                [c_4425,c_34,c_35]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_4531,plain,
% 3.44/1.03      ( k1_funct_1(X0,k1_funct_1(sK11,X1)) = k1_funct_1(k5_relat_1(sK11,X0),X1)
% 3.44/1.03      | r2_hidden(X1,sK9) != iProver_top
% 3.44/1.03      | v1_relat_1(X0) != iProver_top
% 3.44/1.03      | v1_funct_1(X0) != iProver_top ),
% 3.44/1.03      inference(renaming,[status(thm)],[c_4530]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_4549,plain,
% 3.44/1.03      ( k1_funct_1(k5_relat_1(sK11,X0),sK8(sK9,sK11)) = k1_funct_1(X0,k1_funct_1(sK11,sK8(sK9,sK11)))
% 3.44/1.03      | v1_relat_1(X0) != iProver_top
% 3.44/1.03      | v1_funct_1(X0) != iProver_top ),
% 3.44/1.03      inference(superposition,[status(thm)],[c_4007,c_4531]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_4686,plain,
% 3.44/1.03      ( k1_funct_1(sK10,k1_funct_1(sK11,sK8(sK9,sK11))) = k1_funct_1(k5_relat_1(sK11,sK10),sK8(sK9,sK11))
% 3.44/1.03      | v1_funct_1(sK10) != iProver_top ),
% 3.44/1.03      inference(superposition,[status(thm)],[c_1245,c_4549]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_23,negated_conjecture,
% 3.44/1.03      ( k5_relat_1(sK11,sK10) = sK10 ),
% 3.44/1.03      inference(cnf_transformation,[],[f78]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_4687,plain,
% 3.44/1.03      ( k1_funct_1(sK10,k1_funct_1(sK11,sK8(sK9,sK11))) = k1_funct_1(sK10,sK8(sK9,sK11))
% 3.44/1.03      | v1_funct_1(sK10) != iProver_top ),
% 3.44/1.03      inference(light_normalisation,[status(thm)],[c_4686,c_23]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_30,negated_conjecture,
% 3.44/1.03      ( v1_funct_1(sK10) ),
% 3.44/1.03      inference(cnf_transformation,[],[f71]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_33,plain,
% 3.44/1.03      ( v1_funct_1(sK10) = iProver_top ),
% 3.44/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_4691,plain,
% 3.44/1.03      ( k1_funct_1(sK10,k1_funct_1(sK11,sK8(sK9,sK11))) = k1_funct_1(sK10,sK8(sK9,sK11)) ),
% 3.44/1.03      inference(global_propositional_subsumption,
% 3.44/1.03                [status(thm)],
% 3.44/1.03                [c_4687,c_33]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_13,plain,
% 3.44/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.44/1.03      | ~ r2_hidden(X2,k1_relat_1(X1))
% 3.44/1.03      | ~ v1_relat_1(X1)
% 3.44/1.03      | ~ v1_funct_1(X1)
% 3.44/1.03      | ~ v2_funct_1(X1)
% 3.44/1.03      | X0 = X2
% 3.44/1.03      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 3.44/1.03      inference(cnf_transformation,[],[f57]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_1257,plain,
% 3.44/1.03      ( X0 = X1
% 3.44/1.03      | k1_funct_1(X2,X0) != k1_funct_1(X2,X1)
% 3.44/1.03      | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
% 3.44/1.03      | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
% 3.44/1.03      | v1_relat_1(X2) != iProver_top
% 3.44/1.03      | v1_funct_1(X2) != iProver_top
% 3.44/1.03      | v2_funct_1(X2) != iProver_top ),
% 3.44/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_4934,plain,
% 3.44/1.03      ( k1_funct_1(sK10,sK8(sK9,sK11)) != k1_funct_1(sK10,X0)
% 3.44/1.03      | k1_funct_1(sK11,sK8(sK9,sK11)) = X0
% 3.44/1.03      | r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
% 3.44/1.03      | r2_hidden(k1_funct_1(sK11,sK8(sK9,sK11)),k1_relat_1(sK10)) != iProver_top
% 3.44/1.03      | v1_relat_1(sK10) != iProver_top
% 3.44/1.03      | v1_funct_1(sK10) != iProver_top
% 3.44/1.03      | v2_funct_1(sK10) != iProver_top ),
% 3.44/1.03      inference(superposition,[status(thm)],[c_4691,c_1257]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_27,negated_conjecture,
% 3.44/1.03      ( k1_relat_1(sK10) = sK9 ),
% 3.44/1.03      inference(cnf_transformation,[],[f74]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_4938,plain,
% 3.44/1.03      ( k1_funct_1(sK10,sK8(sK9,sK11)) != k1_funct_1(sK10,X0)
% 3.44/1.03      | k1_funct_1(sK11,sK8(sK9,sK11)) = X0
% 3.44/1.03      | r2_hidden(X0,sK9) != iProver_top
% 3.44/1.03      | r2_hidden(k1_funct_1(sK11,sK8(sK9,sK11)),sK9) != iProver_top
% 3.44/1.03      | v1_relat_1(sK10) != iProver_top
% 3.44/1.03      | v1_funct_1(sK10) != iProver_top
% 3.44/1.03      | v2_funct_1(sK10) != iProver_top ),
% 3.44/1.03      inference(light_normalisation,[status(thm)],[c_4934,c_27]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_32,plain,
% 3.44/1.03      ( v1_relat_1(sK10) = iProver_top ),
% 3.44/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_24,negated_conjecture,
% 3.44/1.03      ( v2_funct_1(sK10) ),
% 3.44/1.03      inference(cnf_transformation,[],[f77]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_37,plain,
% 3.44/1.03      ( v2_funct_1(sK10) = iProver_top ),
% 3.44/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_5029,plain,
% 3.44/1.03      ( r2_hidden(k1_funct_1(sK11,sK8(sK9,sK11)),sK9) != iProver_top
% 3.44/1.03      | r2_hidden(X0,sK9) != iProver_top
% 3.44/1.03      | k1_funct_1(sK11,sK8(sK9,sK11)) = X0
% 3.44/1.03      | k1_funct_1(sK10,sK8(sK9,sK11)) != k1_funct_1(sK10,X0) ),
% 3.44/1.03      inference(global_propositional_subsumption,
% 3.44/1.03                [status(thm)],
% 3.44/1.03                [c_4938,c_32,c_33,c_37]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_5030,plain,
% 3.44/1.03      ( k1_funct_1(sK10,sK8(sK9,sK11)) != k1_funct_1(sK10,X0)
% 3.44/1.03      | k1_funct_1(sK11,sK8(sK9,sK11)) = X0
% 3.44/1.03      | r2_hidden(X0,sK9) != iProver_top
% 3.44/1.03      | r2_hidden(k1_funct_1(sK11,sK8(sK9,sK11)),sK9) != iProver_top ),
% 3.44/1.03      inference(renaming,[status(thm)],[c_5029]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_5036,plain,
% 3.44/1.03      ( k1_funct_1(sK11,sK8(sK9,sK11)) = sK8(sK9,sK11)
% 3.44/1.03      | r2_hidden(sK8(sK9,sK11),sK9) != iProver_top
% 3.44/1.03      | r2_hidden(k1_funct_1(sK11,sK8(sK9,sK11)),sK9) != iProver_top ),
% 3.44/1.03      inference(equality_resolution,[status(thm)],[c_5030]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_15,plain,
% 3.44/1.03      ( ~ v1_relat_1(X0)
% 3.44/1.03      | ~ v1_funct_1(X0)
% 3.44/1.03      | k1_funct_1(X0,sK8(k1_relat_1(X0),X0)) != sK8(k1_relat_1(X0),X0)
% 3.44/1.03      | k6_relat_1(k1_relat_1(X0)) = X0 ),
% 3.44/1.03      inference(cnf_transformation,[],[f84]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_1255,plain,
% 3.44/1.03      ( k1_funct_1(X0,sK8(k1_relat_1(X0),X0)) != sK8(k1_relat_1(X0),X0)
% 3.44/1.03      | k6_relat_1(k1_relat_1(X0)) = X0
% 3.44/1.03      | v1_relat_1(X0) != iProver_top
% 3.44/1.03      | v1_funct_1(X0) != iProver_top ),
% 3.44/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_4348,plain,
% 3.44/1.03      ( k1_funct_1(sK11,sK8(sK9,sK11)) != sK8(k1_relat_1(sK11),sK11)
% 3.44/1.03      | k6_relat_1(k1_relat_1(sK11)) = sK11
% 3.44/1.03      | v1_relat_1(sK11) != iProver_top
% 3.44/1.03      | v1_funct_1(sK11) != iProver_top ),
% 3.44/1.03      inference(superposition,[status(thm)],[c_26,c_1255]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_4351,plain,
% 3.44/1.03      ( k1_funct_1(sK11,sK8(sK9,sK11)) != sK8(sK9,sK11)
% 3.44/1.03      | k6_relat_1(sK9) = sK11
% 3.44/1.03      | v1_relat_1(sK11) != iProver_top
% 3.44/1.03      | v1_funct_1(sK11) != iProver_top ),
% 3.44/1.03      inference(light_normalisation,[status(thm)],[c_4348,c_26]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_5388,plain,
% 3.44/1.03      ( r2_hidden(k1_funct_1(sK11,sK8(sK9,sK11)),sK9) != iProver_top ),
% 3.44/1.03      inference(global_propositional_subsumption,
% 3.44/1.03                [status(thm)],
% 3.44/1.03                [c_5036,c_34,c_35,c_22,c_3908,c_4351]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(c_13125,plain,
% 3.44/1.03      ( r2_hidden(sK2(sK11,sK8(sK9,sK11)),sK9) != iProver_top ),
% 3.44/1.03      inference(demodulation,[status(thm)],[c_12526,c_5388]) ).
% 3.44/1.03  
% 3.44/1.03  cnf(contradiction,plain,
% 3.44/1.03      ( $false ),
% 3.44/1.03      inference(minisat,[status(thm)],[c_13669,c_13125]) ).
% 3.44/1.03  
% 3.44/1.03  
% 3.44/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.44/1.03  
% 3.44/1.03  ------                               Statistics
% 3.44/1.03  
% 3.44/1.03  ------ General
% 3.44/1.03  
% 3.44/1.03  abstr_ref_over_cycles:                  0
% 3.44/1.03  abstr_ref_under_cycles:                 0
% 3.44/1.03  gc_basic_clause_elim:                   0
% 3.44/1.03  forced_gc_time:                         0
% 3.44/1.03  parsing_time:                           0.013
% 3.44/1.03  unif_index_cands_time:                  0.
% 3.44/1.03  unif_index_add_time:                    0.
% 3.44/1.03  orderings_time:                         0.
% 3.44/1.03  out_proof_time:                         0.014
% 3.44/1.03  total_time:                             0.505
% 3.44/1.03  num_of_symbols:                         54
% 3.44/1.03  num_of_terms:                           20809
% 3.44/1.03  
% 3.44/1.03  ------ Preprocessing
% 3.44/1.03  
% 3.44/1.03  num_of_splits:                          0
% 3.44/1.03  num_of_split_atoms:                     0
% 3.44/1.03  num_of_reused_defs:                     0
% 3.44/1.03  num_eq_ax_congr_red:                    45
% 3.44/1.03  num_of_sem_filtered_clauses:            1
% 3.44/1.03  num_of_subtypes:                        0
% 3.44/1.03  monotx_restored_types:                  0
% 3.44/1.03  sat_num_of_epr_types:                   0
% 3.44/1.03  sat_num_of_non_cyclic_types:            0
% 3.44/1.03  sat_guarded_non_collapsed_types:        0
% 3.44/1.03  num_pure_diseq_elim:                    0
% 3.44/1.03  simp_replaced_by:                       0
% 3.44/1.03  res_preprocessed:                       148
% 3.44/1.03  prep_upred:                             0
% 3.44/1.03  prep_unflattend:                        12
% 3.44/1.03  smt_new_axioms:                         0
% 3.44/1.03  pred_elim_cands:                        4
% 3.44/1.03  pred_elim:                              1
% 3.44/1.03  pred_elim_cl:                           1
% 3.44/1.03  pred_elim_cycles:                       3
% 3.44/1.03  merged_defs:                            0
% 3.44/1.03  merged_defs_ncl:                        0
% 3.44/1.03  bin_hyper_res:                          0
% 3.44/1.03  prep_cycles:                            4
% 3.44/1.03  pred_elim_time:                         0.007
% 3.44/1.03  splitting_time:                         0.
% 3.44/1.03  sem_filter_time:                        0.
% 3.44/1.03  monotx_time:                            0.
% 3.44/1.03  subtype_inf_time:                       0.
% 3.44/1.03  
% 3.44/1.03  ------ Problem properties
% 3.44/1.03  
% 3.44/1.03  clauses:                                30
% 3.44/1.03  conjectures:                            9
% 3.44/1.03  epr:                                    5
% 3.44/1.03  horn:                                   24
% 3.44/1.03  ground:                                 9
% 3.44/1.03  unary:                                  9
% 3.44/1.03  binary:                                 5
% 3.44/1.03  lits:                                   83
% 3.44/1.03  lits_eq:                                19
% 3.44/1.03  fd_pure:                                0
% 3.44/1.03  fd_pseudo:                              0
% 3.44/1.03  fd_cond:                                0
% 3.44/1.03  fd_pseudo_cond:                         6
% 3.44/1.03  ac_symbols:                             0
% 3.44/1.03  
% 3.44/1.03  ------ Propositional Solver
% 3.44/1.03  
% 3.44/1.03  prop_solver_calls:                      33
% 3.44/1.03  prop_fast_solver_calls:                 1455
% 3.44/1.03  smt_solver_calls:                       0
% 3.44/1.03  smt_fast_solver_calls:                  0
% 3.44/1.03  prop_num_of_clauses:                    7626
% 3.44/1.03  prop_preprocess_simplified:             8802
% 3.44/1.03  prop_fo_subsumed:                       73
% 3.44/1.03  prop_solver_time:                       0.
% 3.44/1.03  smt_solver_time:                        0.
% 3.44/1.03  smt_fast_solver_time:                   0.
% 3.44/1.03  prop_fast_solver_time:                  0.
% 3.44/1.03  prop_unsat_core_time:                   0.
% 3.44/1.03  
% 3.44/1.03  ------ QBF
% 3.44/1.03  
% 3.44/1.03  qbf_q_res:                              0
% 3.44/1.03  qbf_num_tautologies:                    0
% 3.44/1.03  qbf_prep_cycles:                        0
% 3.44/1.03  
% 3.44/1.03  ------ BMC1
% 3.44/1.03  
% 3.44/1.03  bmc1_current_bound:                     -1
% 3.44/1.03  bmc1_last_solved_bound:                 -1
% 3.44/1.03  bmc1_unsat_core_size:                   -1
% 3.44/1.03  bmc1_unsat_core_parents_size:           -1
% 3.44/1.03  bmc1_merge_next_fun:                    0
% 3.44/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.44/1.03  
% 3.44/1.03  ------ Instantiation
% 3.44/1.03  
% 3.44/1.03  inst_num_of_clauses:                    1257
% 3.44/1.03  inst_num_in_passive:                    246
% 3.44/1.03  inst_num_in_active:                     637
% 3.44/1.03  inst_num_in_unprocessed:                374
% 3.44/1.03  inst_num_of_loops:                      810
% 3.44/1.03  inst_num_of_learning_restarts:          0
% 3.44/1.03  inst_num_moves_active_passive:          168
% 3.44/1.03  inst_lit_activity:                      0
% 3.44/1.03  inst_lit_activity_moves:                0
% 3.44/1.03  inst_num_tautologies:                   0
% 3.44/1.03  inst_num_prop_implied:                  0
% 3.44/1.03  inst_num_existing_simplified:           0
% 3.44/1.03  inst_num_eq_res_simplified:             0
% 3.44/1.03  inst_num_child_elim:                    0
% 3.44/1.03  inst_num_of_dismatching_blockings:      1432
% 3.44/1.03  inst_num_of_non_proper_insts:           1988
% 3.44/1.03  inst_num_of_duplicates:                 0
% 3.44/1.03  inst_inst_num_from_inst_to_res:         0
% 3.44/1.03  inst_dismatching_checking_time:         0.
% 3.44/1.03  
% 3.44/1.03  ------ Resolution
% 3.44/1.03  
% 3.44/1.03  res_num_of_clauses:                     0
% 3.44/1.03  res_num_in_passive:                     0
% 3.44/1.03  res_num_in_active:                      0
% 3.44/1.03  res_num_of_loops:                       152
% 3.44/1.03  res_forward_subset_subsumed:            84
% 3.44/1.03  res_backward_subset_subsumed:           0
% 3.44/1.03  res_forward_subsumed:                   0
% 3.44/1.03  res_backward_subsumed:                  0
% 3.44/1.03  res_forward_subsumption_resolution:     0
% 3.44/1.03  res_backward_subsumption_resolution:    0
% 3.44/1.03  res_clause_to_clause_subsumption:       2080
% 3.44/1.03  res_orphan_elimination:                 0
% 3.44/1.03  res_tautology_del:                      132
% 3.44/1.03  res_num_eq_res_simplified:              0
% 3.44/1.03  res_num_sel_changes:                    0
% 3.44/1.03  res_moves_from_active_to_pass:          0
% 3.44/1.03  
% 3.44/1.03  ------ Superposition
% 3.44/1.03  
% 3.44/1.03  sup_time_total:                         0.
% 3.44/1.03  sup_time_generating:                    0.
% 3.44/1.03  sup_time_sim_full:                      0.
% 3.44/1.03  sup_time_sim_immed:                     0.
% 3.44/1.03  
% 3.44/1.03  sup_num_of_clauses:                     1149
% 3.44/1.03  sup_num_in_active:                      153
% 3.44/1.03  sup_num_in_passive:                     996
% 3.44/1.03  sup_num_of_loops:                       160
% 3.44/1.03  sup_fw_superposition:                   705
% 3.44/1.03  sup_bw_superposition:                   530
% 3.44/1.03  sup_immediate_simplified:               57
% 3.44/1.03  sup_given_eliminated:                   0
% 3.44/1.03  comparisons_done:                       0
% 3.44/1.03  comparisons_avoided:                    3
% 3.44/1.03  
% 3.44/1.03  ------ Simplifications
% 3.44/1.03  
% 3.44/1.03  
% 3.44/1.03  sim_fw_subset_subsumed:                 14
% 3.44/1.03  sim_bw_subset_subsumed:                 3
% 3.44/1.03  sim_fw_subsumed:                        1
% 3.44/1.03  sim_bw_subsumed:                        6
% 3.44/1.03  sim_fw_subsumption_res:                 0
% 3.44/1.03  sim_bw_subsumption_res:                 0
% 3.44/1.03  sim_tautology_del:                      9
% 3.44/1.03  sim_eq_tautology_del:                   59
% 3.44/1.03  sim_eq_res_simp:                        1
% 3.44/1.03  sim_fw_demodulated:                     2
% 3.44/1.03  sim_bw_demodulated:                     5
% 3.44/1.03  sim_light_normalised:                   34
% 3.44/1.03  sim_joinable_taut:                      0
% 3.44/1.03  sim_joinable_simp:                      0
% 3.44/1.03  sim_ac_normalised:                      0
% 3.44/1.03  sim_smt_subsumption:                    0
% 3.44/1.03  
%------------------------------------------------------------------------------
