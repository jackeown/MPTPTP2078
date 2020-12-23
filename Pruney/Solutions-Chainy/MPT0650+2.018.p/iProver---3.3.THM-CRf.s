%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:25 EST 2020

% Result     : Theorem 11.62s
% Output     : CNFRefutation 11.62s
% Verified   : 
% Statistics : Number of formulae       :  171 (1510 expanded)
%              Number of clauses        :  104 ( 496 expanded)
%              Number of leaves         :   18 ( 305 expanded)
%              Depth                    :   28
%              Number of atoms          :  513 (6309 expanded)
%              Number of equality atoms :  241 (2205 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
          | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
        & r2_hidden(X0,k2_relat_1(X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
        | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 )
      & r2_hidden(sK3,k2_relat_1(sK4))
      & v2_funct_1(sK4)
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
      | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 )
    & r2_hidden(sK3,k2_relat_1(sK4))
    & v2_funct_1(sK4)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f44])).

fof(f74,plain,(
    r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f40,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f40,f39,f38])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f33])).

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
    inference(flattening,[],[f42])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f60,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f70])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_808,plain,
    ( r2_hidden(sK3,k2_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_826,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_23,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_809,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3861,plain,
    ( k1_funct_1(X0,sK2(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_826,c_809])).

cnf(c_37854,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK3)) = sK3
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_808,c_3861])).

cnf(c_29,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1066,plain,
    ( r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4)
    | ~ r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1118,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK2(sK4,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_40311,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_37854,c_29,c_28,c_26,c_1066,c_1118])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_822,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4046,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_826,c_822])).

cnf(c_805,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_819,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2337,plain,
    ( k5_relat_1(sK4,k6_relat_1(k2_relat_1(sK4))) = sK4 ),
    inference(superposition,[status(thm)],[c_805,c_819])).

cnf(c_18,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_814,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_823,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4061,plain,
    ( k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X0,k6_relat_1(X1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_823])).

cnf(c_12,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4069,plain,
    ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4061,c_12])).

cnf(c_4288,plain,
    ( k1_relat_1(k5_relat_1(sK4,k6_relat_1(X0))) = k10_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_805,c_4069])).

cnf(c_4312,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2337,c_4288])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_811,plain,
    ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X1)) = X1
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4313,plain,
    ( k1_funct_1(k2_funct_1(k5_relat_1(sK4,k6_relat_1(X0))),k1_funct_1(k5_relat_1(sK4,k6_relat_1(X0)),X1)) = X1
    | r2_hidden(X1,k10_relat_1(sK4,X0)) != iProver_top
    | v1_funct_1(k5_relat_1(sK4,k6_relat_1(X0))) != iProver_top
    | v2_funct_1(k5_relat_1(sK4,k6_relat_1(X0))) != iProver_top
    | v1_relat_1(k5_relat_1(sK4,k6_relat_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4288,c_811])).

cnf(c_8653,plain,
    ( k1_funct_1(k2_funct_1(k5_relat_1(sK4,k6_relat_1(k2_relat_1(sK4)))),k1_funct_1(k5_relat_1(sK4,k6_relat_1(k2_relat_1(sK4))),X0)) = X0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(k5_relat_1(sK4,k6_relat_1(k2_relat_1(sK4)))) != iProver_top
    | v2_funct_1(k5_relat_1(sK4,k6_relat_1(k2_relat_1(sK4)))) != iProver_top
    | v1_relat_1(k5_relat_1(sK4,k6_relat_1(k2_relat_1(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4312,c_4313])).

cnf(c_806,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_818,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5311,plain,
    ( k2_funct_1(sK4) = k4_relat_1(sK4)
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_806,c_818])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_65,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_funct_1(sK4) = k4_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_5951,plain,
    ( k2_funct_1(sK4) = k4_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5311,c_29,c_28,c_27,c_65])).

cnf(c_8659,plain,
    ( k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,X0)) = X0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8653,c_2337,c_5951])).

cnf(c_30,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_31,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_32,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_9269,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8659,c_30,c_31,c_32])).

cnf(c_9270,plain,
    ( k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,X0)) = X0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9269])).

cnf(c_30314,plain,
    ( k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,sK2(sK4,X0))) = sK2(sK4,X0)
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4046,c_9270])).

cnf(c_34553,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,sK2(sK4,X0))) = sK2(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30314,c_30])).

cnf(c_34554,plain,
    ( k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,sK2(sK4,X0))) = sK2(sK4,X0)
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_34553])).

cnf(c_34565,plain,
    ( k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,sK2(sK4,sK3))) = sK2(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_808,c_34554])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_810,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_34750,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2(sK4,sK3)),k1_relat_1(k4_relat_1(sK4))) != iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(sK4,sK2(sK4,sK3)),sK2(sK4,sK3)),k4_relat_1(sK4)) = iProver_top
    | v1_funct_1(k4_relat_1(sK4)) != iProver_top
    | v1_relat_1(k4_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_34565,c_810])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_820,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1531,plain,
    ( k1_relat_1(k4_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_805,c_820])).

cnf(c_34760,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2(sK4,sK3)),k2_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(sK4,sK2(sK4,sK3)),sK2(sK4,sK3)),k4_relat_1(sK4)) = iProver_top
    | v1_funct_1(k4_relat_1(sK4)) != iProver_top
    | v1_relat_1(k4_relat_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34750,c_1531])).

cnf(c_33,plain,
    ( r2_hidden(sK3,k2_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_90,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_92,plain,
    ( v1_relat_1(k4_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_1067,plain,
    ( r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4) = iProver_top
    | r2_hidden(sK3,k2_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1066])).

cnf(c_1115,plain,
    ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1116,plain,
    ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1115])).

cnf(c_1171,plain,
    ( ~ r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4))
    | r2_hidden(k4_tarski(sK2(sK4,sK3),k1_funct_1(sK4,sK2(sK4,sK3))),sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1172,plain,
    ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK4,sK3),k1_funct_1(sK4,sK2(sK4,sK3))),sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1171])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1503,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2(sK4,sK3)),k2_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(sK2(sK4,sK3),k1_funct_1(sK4,sK2(sK4,sK3))),sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1504,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2(sK4,sK3)),k2_relat_1(sK4)) = iProver_top
    | r2_hidden(k4_tarski(sK2(sK4,sK3),k1_funct_1(sK4,sK2(sK4,sK3))),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1503])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_817,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5960,plain,
    ( v1_funct_1(k4_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5951,c_817])).

cnf(c_34955,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK4,sK2(sK4,sK3)),sK2(sK4,sK3)),k4_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34760,c_30,c_31,c_33,c_92,c_1067,c_1116,c_1172,c_1504,c_5960])).

cnf(c_34961,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2(sK4,sK3)),k1_relat_1(k4_relat_1(sK4))) = iProver_top
    | v1_relat_1(k4_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_34955,c_822])).

cnf(c_34978,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2(sK4,sK3)),k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(k4_relat_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34961,c_1531])).

cnf(c_36558,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2(sK4,sK3)),k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34978,c_30,c_31,c_33,c_1067,c_1116,c_1172,c_1504])).

cnf(c_825,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2335,plain,
    ( k5_relat_1(k4_relat_1(X0),k6_relat_1(k2_relat_1(k4_relat_1(X0)))) = k4_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_825,c_819])).

cnf(c_2986,plain,
    ( k5_relat_1(k4_relat_1(sK4),k6_relat_1(k2_relat_1(k4_relat_1(sK4)))) = k4_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_805,c_2335])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_821,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1818,plain,
    ( k2_relat_1(k4_relat_1(sK4)) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_805,c_821])).

cnf(c_2988,plain,
    ( k5_relat_1(k4_relat_1(sK4),k6_relat_1(k1_relat_1(sK4))) = k4_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_2986,c_1818])).

cnf(c_4285,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k4_relat_1(X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_825,c_4069])).

cnf(c_12702,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(sK4),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK4),X0) ),
    inference(superposition,[status(thm)],[c_805,c_4285])).

cnf(c_12726,plain,
    ( k10_relat_1(k4_relat_1(sK4),k1_relat_1(sK4)) = k1_relat_1(k4_relat_1(sK4)) ),
    inference(superposition,[status(thm)],[c_2988,c_12702])).

cnf(c_4062,plain,
    ( k10_relat_1(X0,k1_relat_1(sK4)) = k1_relat_1(k5_relat_1(X0,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_823])).

cnf(c_4428,plain,
    ( k10_relat_1(k4_relat_1(X0),k1_relat_1(sK4)) = k1_relat_1(k5_relat_1(k4_relat_1(X0),sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_825,c_4062])).

cnf(c_4714,plain,
    ( k10_relat_1(k4_relat_1(sK4),k1_relat_1(sK4)) = k1_relat_1(k5_relat_1(k4_relat_1(sK4),sK4)) ),
    inference(superposition,[status(thm)],[c_805,c_4428])).

cnf(c_12763,plain,
    ( k10_relat_1(k4_relat_1(sK4),k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_12726,c_1531,c_4714])).

cnf(c_12896,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(sK4),sK4)) = k2_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_12763,c_4714])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_813,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13247,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),X0) = k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),X0))
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | v1_funct_1(k4_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_12896,c_813])).

cnf(c_28545,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),X0) = k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),X0))
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13247,c_30,c_31,c_92,c_5960])).

cnf(c_36568,plain,
    ( k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,sK2(sK4,sK3)))) = k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),k1_funct_1(sK4,sK2(sK4,sK3))) ),
    inference(superposition,[status(thm)],[c_36558,c_28545])).

cnf(c_36620,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),k1_funct_1(sK4,sK2(sK4,sK3))) = k1_funct_1(sK4,sK2(sK4,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_36568,c_34565])).

cnf(c_40314,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_40311,c_36620])).

cnf(c_28557,plain,
    ( k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),sK3)) = k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),sK3) ),
    inference(superposition,[status(thm)],[c_808,c_28545])).

cnf(c_40343,plain,
    ( k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_40314,c_28557])).

cnf(c_25,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_5955,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),sK3) != sK3
    | k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),sK3)) != sK3 ),
    inference(demodulation,[status(thm)],[c_5951,c_25])).

cnf(c_28653,plain,
    ( k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),sK3)) != sK3 ),
    inference(demodulation,[status(thm)],[c_28557,c_5955])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_40343,c_28653])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:49:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.62/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.62/2.00  
% 11.62/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.62/2.00  
% 11.62/2.00  ------  iProver source info
% 11.62/2.00  
% 11.62/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.62/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.62/2.00  git: non_committed_changes: false
% 11.62/2.00  git: last_make_outside_of_git: false
% 11.62/2.00  
% 11.62/2.00  ------ 
% 11.62/2.00  ------ Parsing...
% 11.62/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.62/2.00  
% 11.62/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.62/2.00  
% 11.62/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.62/2.00  
% 11.62/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/2.00  ------ Proving...
% 11.62/2.00  ------ Problem Properties 
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  clauses                                 28
% 11.62/2.00  conjectures                             5
% 11.62/2.00  EPR                                     3
% 11.62/2.00  Horn                                    27
% 11.62/2.00  unary                                   8
% 11.62/2.00  binary                                  8
% 11.62/2.00  lits                                    70
% 11.62/2.00  lits eq                                 16
% 11.62/2.00  fd_pure                                 0
% 11.62/2.00  fd_pseudo                               0
% 11.62/2.00  fd_cond                                 0
% 11.62/2.00  fd_pseudo_cond                          3
% 11.62/2.00  AC symbols                              0
% 11.62/2.00  
% 11.62/2.00  ------ Input Options Time Limit: Unbounded
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  ------ 
% 11.62/2.00  Current options:
% 11.62/2.00  ------ 
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  ------ Proving...
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  % SZS status Theorem for theBenchmark.p
% 11.62/2.00  
% 11.62/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.62/2.00  
% 11.62/2.00  fof(f15,conjecture,(
% 11.62/2.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f16,negated_conjecture,(
% 11.62/2.00    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 11.62/2.00    inference(negated_conjecture,[],[f15])).
% 11.62/2.00  
% 11.62/2.00  fof(f34,plain,(
% 11.62/2.00    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 11.62/2.00    inference(ennf_transformation,[],[f16])).
% 11.62/2.00  
% 11.62/2.00  fof(f35,plain,(
% 11.62/2.00    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 11.62/2.00    inference(flattening,[],[f34])).
% 11.62/2.00  
% 11.62/2.00  fof(f44,plain,(
% 11.62/2.00    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3 | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3) & r2_hidden(sK3,k2_relat_1(sK4)) & v2_funct_1(sK4) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 11.62/2.00    introduced(choice_axiom,[])).
% 11.62/2.00  
% 11.62/2.00  fof(f45,plain,(
% 11.62/2.00    (k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3 | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3) & r2_hidden(sK3,k2_relat_1(sK4)) & v2_funct_1(sK4) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 11.62/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f44])).
% 11.62/2.00  
% 11.62/2.00  fof(f74,plain,(
% 11.62/2.00    r2_hidden(sK3,k2_relat_1(sK4))),
% 11.62/2.00    inference(cnf_transformation,[],[f45])).
% 11.62/2.00  
% 11.62/2.00  fof(f1,axiom,(
% 11.62/2.00    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f36,plain,(
% 11.62/2.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 11.62/2.00    inference(nnf_transformation,[],[f1])).
% 11.62/2.00  
% 11.62/2.00  fof(f37,plain,(
% 11.62/2.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 11.62/2.00    inference(rectify,[],[f36])).
% 11.62/2.00  
% 11.62/2.00  fof(f40,plain,(
% 11.62/2.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0))),
% 11.62/2.00    introduced(choice_axiom,[])).
% 11.62/2.00  
% 11.62/2.00  fof(f39,plain,(
% 11.62/2.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0))) )),
% 11.62/2.00    introduced(choice_axiom,[])).
% 11.62/2.00  
% 11.62/2.00  fof(f38,plain,(
% 11.62/2.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 11.62/2.00    introduced(choice_axiom,[])).
% 11.62/2.00  
% 11.62/2.00  fof(f41,plain,(
% 11.62/2.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 11.62/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f40,f39,f38])).
% 11.62/2.00  
% 11.62/2.00  fof(f46,plain,(
% 11.62/2.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 11.62/2.00    inference(cnf_transformation,[],[f41])).
% 11.62/2.00  
% 11.62/2.00  fof(f77,plain,(
% 11.62/2.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 11.62/2.00    inference(equality_resolution,[],[f46])).
% 11.62/2.00  
% 11.62/2.00  fof(f14,axiom,(
% 11.62/2.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f32,plain,(
% 11.62/2.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 11.62/2.00    inference(ennf_transformation,[],[f14])).
% 11.62/2.00  
% 11.62/2.00  fof(f33,plain,(
% 11.62/2.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.62/2.00    inference(flattening,[],[f32])).
% 11.62/2.00  
% 11.62/2.00  fof(f42,plain,(
% 11.62/2.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.62/2.00    inference(nnf_transformation,[],[f33])).
% 11.62/2.00  
% 11.62/2.00  fof(f43,plain,(
% 11.62/2.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.62/2.00    inference(flattening,[],[f42])).
% 11.62/2.00  
% 11.62/2.00  fof(f69,plain,(
% 11.62/2.00    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f43])).
% 11.62/2.00  
% 11.62/2.00  fof(f71,plain,(
% 11.62/2.00    v1_relat_1(sK4)),
% 11.62/2.00    inference(cnf_transformation,[],[f45])).
% 11.62/2.00  
% 11.62/2.00  fof(f72,plain,(
% 11.62/2.00    v1_funct_1(sK4)),
% 11.62/2.00    inference(cnf_transformation,[],[f45])).
% 11.62/2.00  
% 11.62/2.00  fof(f5,axiom,(
% 11.62/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f20,plain,(
% 11.62/2.00    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 11.62/2.00    inference(ennf_transformation,[],[f5])).
% 11.62/2.00  
% 11.62/2.00  fof(f21,plain,(
% 11.62/2.00    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 11.62/2.00    inference(flattening,[],[f20])).
% 11.62/2.00  
% 11.62/2.00  fof(f53,plain,(
% 11.62/2.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f21])).
% 11.62/2.00  
% 11.62/2.00  fof(f8,axiom,(
% 11.62/2.00    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f23,plain,(
% 11.62/2.00    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 11.62/2.00    inference(ennf_transformation,[],[f8])).
% 11.62/2.00  
% 11.62/2.00  fof(f59,plain,(
% 11.62/2.00    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f23])).
% 11.62/2.00  
% 11.62/2.00  fof(f11,axiom,(
% 11.62/2.00    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f63,plain,(
% 11.62/2.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 11.62/2.00    inference(cnf_transformation,[],[f11])).
% 11.62/2.00  
% 11.62/2.00  fof(f4,axiom,(
% 11.62/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f19,plain,(
% 11.62/2.00    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.62/2.00    inference(ennf_transformation,[],[f4])).
% 11.62/2.00  
% 11.62/2.00  fof(f52,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f19])).
% 11.62/2.00  
% 11.62/2.00  fof(f7,axiom,(
% 11.62/2.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f57,plain,(
% 11.62/2.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 11.62/2.00    inference(cnf_transformation,[],[f7])).
% 11.62/2.00  
% 11.62/2.00  fof(f13,axiom,(
% 11.62/2.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f30,plain,(
% 11.62/2.00    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.62/2.00    inference(ennf_transformation,[],[f13])).
% 11.62/2.00  
% 11.62/2.00  fof(f31,plain,(
% 11.62/2.00    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.62/2.00    inference(flattening,[],[f30])).
% 11.62/2.00  
% 11.62/2.00  fof(f66,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f31])).
% 11.62/2.00  
% 11.62/2.00  fof(f9,axiom,(
% 11.62/2.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f24,plain,(
% 11.62/2.00    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.62/2.00    inference(ennf_transformation,[],[f9])).
% 11.62/2.00  
% 11.62/2.00  fof(f25,plain,(
% 11.62/2.00    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.62/2.00    inference(flattening,[],[f24])).
% 11.62/2.00  
% 11.62/2.00  fof(f60,plain,(
% 11.62/2.00    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f25])).
% 11.62/2.00  
% 11.62/2.00  fof(f73,plain,(
% 11.62/2.00    v2_funct_1(sK4)),
% 11.62/2.00    inference(cnf_transformation,[],[f45])).
% 11.62/2.00  
% 11.62/2.00  fof(f70,plain,(
% 11.62/2.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f43])).
% 11.62/2.00  
% 11.62/2.00  fof(f78,plain,(
% 11.62/2.00    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.62/2.00    inference(equality_resolution,[],[f70])).
% 11.62/2.00  
% 11.62/2.00  fof(f6,axiom,(
% 11.62/2.00    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f22,plain,(
% 11.62/2.00    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 11.62/2.00    inference(ennf_transformation,[],[f6])).
% 11.62/2.00  
% 11.62/2.00  fof(f55,plain,(
% 11.62/2.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f22])).
% 11.62/2.00  
% 11.62/2.00  fof(f2,axiom,(
% 11.62/2.00    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f17,plain,(
% 11.62/2.00    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 11.62/2.00    inference(ennf_transformation,[],[f2])).
% 11.62/2.00  
% 11.62/2.00  fof(f50,plain,(
% 11.62/2.00    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f17])).
% 11.62/2.00  
% 11.62/2.00  fof(f47,plain,(
% 11.62/2.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 11.62/2.00    inference(cnf_transformation,[],[f41])).
% 11.62/2.00  
% 11.62/2.00  fof(f76,plain,(
% 11.62/2.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 11.62/2.00    inference(equality_resolution,[],[f47])).
% 11.62/2.00  
% 11.62/2.00  fof(f10,axiom,(
% 11.62/2.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f26,plain,(
% 11.62/2.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.62/2.00    inference(ennf_transformation,[],[f10])).
% 11.62/2.00  
% 11.62/2.00  fof(f27,plain,(
% 11.62/2.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.62/2.00    inference(flattening,[],[f26])).
% 11.62/2.00  
% 11.62/2.00  fof(f62,plain,(
% 11.62/2.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f27])).
% 11.62/2.00  
% 11.62/2.00  fof(f56,plain,(
% 11.62/2.00    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f22])).
% 11.62/2.00  
% 11.62/2.00  fof(f12,axiom,(
% 11.62/2.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0))))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f28,plain,(
% 11.62/2.00    ! [X0,X1] : (! [X2] : ((k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.62/2.00    inference(ennf_transformation,[],[f12])).
% 11.62/2.00  
% 11.62/2.00  fof(f29,plain,(
% 11.62/2.00    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.62/2.00    inference(flattening,[],[f28])).
% 11.62/2.00  
% 11.62/2.00  fof(f65,plain,(
% 11.62/2.00    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f29])).
% 11.62/2.00  
% 11.62/2.00  fof(f75,plain,(
% 11.62/2.00    k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3 | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3),
% 11.62/2.00    inference(cnf_transformation,[],[f45])).
% 11.62/2.00  
% 11.62/2.00  cnf(c_26,negated_conjecture,
% 11.62/2.00      ( r2_hidden(sK3,k2_relat_1(sK4)) ),
% 11.62/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_808,plain,
% 11.62/2.00      ( r2_hidden(sK3,k2_relat_1(sK4)) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3,plain,
% 11.62/2.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 11.62/2.00      | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_826,plain,
% 11.62/2.00      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 11.62/2.00      | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_23,plain,
% 11.62/2.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 11.62/2.00      | ~ v1_funct_1(X2)
% 11.62/2.00      | ~ v1_relat_1(X2)
% 11.62/2.00      | k1_funct_1(X2,X0) = X1 ),
% 11.62/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_809,plain,
% 11.62/2.00      ( k1_funct_1(X0,X1) = X2
% 11.62/2.00      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 11.62/2.00      | v1_funct_1(X0) != iProver_top
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3861,plain,
% 11.62/2.00      ( k1_funct_1(X0,sK2(X0,X1)) = X1
% 11.62/2.00      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 11.62/2.00      | v1_funct_1(X0) != iProver_top
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_826,c_809]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_37854,plain,
% 11.62/2.00      ( k1_funct_1(sK4,sK2(sK4,sK3)) = sK3
% 11.62/2.00      | v1_funct_1(sK4) != iProver_top
% 11.62/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_808,c_3861]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_29,negated_conjecture,
% 11.62/2.00      ( v1_relat_1(sK4) ),
% 11.62/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_28,negated_conjecture,
% 11.62/2.00      ( v1_funct_1(sK4) ),
% 11.62/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1066,plain,
% 11.62/2.00      ( r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4)
% 11.62/2.00      | ~ r2_hidden(sK3,k2_relat_1(sK4)) ),
% 11.62/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1118,plain,
% 11.62/2.00      ( ~ r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4)
% 11.62/2.00      | ~ v1_funct_1(sK4)
% 11.62/2.00      | ~ v1_relat_1(sK4)
% 11.62/2.00      | k1_funct_1(sK4,sK2(sK4,sK3)) = sK3 ),
% 11.62/2.00      inference(instantiation,[status(thm)],[c_23]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_40311,plain,
% 11.62/2.00      ( k1_funct_1(sK4,sK2(sK4,sK3)) = sK3 ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_37854,c_29,c_28,c_26,c_1066,c_1118]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_8,plain,
% 11.62/2.00      ( r2_hidden(X0,k1_relat_1(X1))
% 11.62/2.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 11.62/2.00      | ~ v1_relat_1(X1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_822,plain,
% 11.62/2.00      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 11.62/2.00      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 11.62/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4046,plain,
% 11.62/2.00      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 11.62/2.00      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 11.62/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_826,c_822]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_805,plain,
% 11.62/2.00      ( v1_relat_1(sK4) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_13,plain,
% 11.62/2.00      ( ~ v1_relat_1(X0)
% 11.62/2.00      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_819,plain,
% 11.62/2.00      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2337,plain,
% 11.62/2.00      ( k5_relat_1(sK4,k6_relat_1(k2_relat_1(sK4))) = sK4 ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_805,c_819]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_18,plain,
% 11.62/2.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 11.62/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_814,plain,
% 11.62/2.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6,plain,
% 11.62/2.00      ( ~ v1_relat_1(X0)
% 11.62/2.00      | ~ v1_relat_1(X1)
% 11.62/2.00      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 11.62/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_823,plain,
% 11.62/2.00      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 11.62/2.00      | v1_relat_1(X1) != iProver_top
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4061,plain,
% 11.62/2.00      ( k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X0,k6_relat_1(X1)))
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_814,c_823]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_12,plain,
% 11.62/2.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4069,plain,
% 11.62/2.00      ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,X1)
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_4061,c_12]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4288,plain,
% 11.62/2.00      ( k1_relat_1(k5_relat_1(sK4,k6_relat_1(X0))) = k10_relat_1(sK4,X0) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_805,c_4069]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4312,plain,
% 11.62/2.00      ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2337,c_4288]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_21,plain,
% 11.62/2.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.62/2.00      | ~ v1_funct_1(X1)
% 11.62/2.00      | ~ v2_funct_1(X1)
% 11.62/2.00      | ~ v1_relat_1(X1)
% 11.62/2.00      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_811,plain,
% 11.62/2.00      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X1)) = X1
% 11.62/2.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 11.62/2.00      | v1_funct_1(X0) != iProver_top
% 11.62/2.00      | v2_funct_1(X0) != iProver_top
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4313,plain,
% 11.62/2.00      ( k1_funct_1(k2_funct_1(k5_relat_1(sK4,k6_relat_1(X0))),k1_funct_1(k5_relat_1(sK4,k6_relat_1(X0)),X1)) = X1
% 11.62/2.00      | r2_hidden(X1,k10_relat_1(sK4,X0)) != iProver_top
% 11.62/2.00      | v1_funct_1(k5_relat_1(sK4,k6_relat_1(X0))) != iProver_top
% 11.62/2.00      | v2_funct_1(k5_relat_1(sK4,k6_relat_1(X0))) != iProver_top
% 11.62/2.00      | v1_relat_1(k5_relat_1(sK4,k6_relat_1(X0))) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_4288,c_811]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_8653,plain,
% 11.62/2.00      ( k1_funct_1(k2_funct_1(k5_relat_1(sK4,k6_relat_1(k2_relat_1(sK4)))),k1_funct_1(k5_relat_1(sK4,k6_relat_1(k2_relat_1(sK4))),X0)) = X0
% 11.62/2.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 11.62/2.00      | v1_funct_1(k5_relat_1(sK4,k6_relat_1(k2_relat_1(sK4)))) != iProver_top
% 11.62/2.00      | v2_funct_1(k5_relat_1(sK4,k6_relat_1(k2_relat_1(sK4)))) != iProver_top
% 11.62/2.00      | v1_relat_1(k5_relat_1(sK4,k6_relat_1(k2_relat_1(sK4)))) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_4312,c_4313]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_806,plain,
% 11.62/2.00      ( v1_funct_1(sK4) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_14,plain,
% 11.62/2.00      ( ~ v1_funct_1(X0)
% 11.62/2.00      | ~ v2_funct_1(X0)
% 11.62/2.00      | ~ v1_relat_1(X0)
% 11.62/2.00      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_818,plain,
% 11.62/2.00      ( k2_funct_1(X0) = k4_relat_1(X0)
% 11.62/2.00      | v1_funct_1(X0) != iProver_top
% 11.62/2.00      | v2_funct_1(X0) != iProver_top
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_5311,plain,
% 11.62/2.00      ( k2_funct_1(sK4) = k4_relat_1(sK4)
% 11.62/2.00      | v2_funct_1(sK4) != iProver_top
% 11.62/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_806,c_818]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_27,negated_conjecture,
% 11.62/2.00      ( v2_funct_1(sK4) ),
% 11.62/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_65,plain,
% 11.62/2.00      ( ~ v1_funct_1(sK4)
% 11.62/2.00      | ~ v2_funct_1(sK4)
% 11.62/2.00      | ~ v1_relat_1(sK4)
% 11.62/2.00      | k2_funct_1(sK4) = k4_relat_1(sK4) ),
% 11.62/2.00      inference(instantiation,[status(thm)],[c_14]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_5951,plain,
% 11.62/2.00      ( k2_funct_1(sK4) = k4_relat_1(sK4) ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_5311,c_29,c_28,c_27,c_65]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_8659,plain,
% 11.62/2.00      ( k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,X0)) = X0
% 11.62/2.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 11.62/2.00      | v1_funct_1(sK4) != iProver_top
% 11.62/2.00      | v2_funct_1(sK4) != iProver_top
% 11.62/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.62/2.00      inference(light_normalisation,[status(thm)],[c_8653,c_2337,c_5951]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_30,plain,
% 11.62/2.00      ( v1_relat_1(sK4) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_31,plain,
% 11.62/2.00      ( v1_funct_1(sK4) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_32,plain,
% 11.62/2.00      ( v2_funct_1(sK4) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_9269,plain,
% 11.62/2.00      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 11.62/2.00      | k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_8659,c_30,c_31,c_32]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_9270,plain,
% 11.62/2.00      ( k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,X0)) = X0
% 11.62/2.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 11.62/2.00      inference(renaming,[status(thm)],[c_9269]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_30314,plain,
% 11.62/2.00      ( k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,sK2(sK4,X0))) = sK2(sK4,X0)
% 11.62/2.00      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 11.62/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_4046,c_9270]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_34553,plain,
% 11.62/2.00      ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 11.62/2.00      | k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,sK2(sK4,X0))) = sK2(sK4,X0) ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_30314,c_30]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_34554,plain,
% 11.62/2.00      ( k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,sK2(sK4,X0))) = sK2(sK4,X0)
% 11.62/2.00      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 11.62/2.00      inference(renaming,[status(thm)],[c_34553]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_34565,plain,
% 11.62/2.00      ( k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,sK2(sK4,sK3))) = sK2(sK4,sK3) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_808,c_34554]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_22,plain,
% 11.62/2.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.62/2.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 11.62/2.00      | ~ v1_funct_1(X1)
% 11.62/2.00      | ~ v1_relat_1(X1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f78]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_810,plain,
% 11.62/2.00      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 11.62/2.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
% 11.62/2.00      | v1_funct_1(X1) != iProver_top
% 11.62/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_34750,plain,
% 11.62/2.00      ( r2_hidden(k1_funct_1(sK4,sK2(sK4,sK3)),k1_relat_1(k4_relat_1(sK4))) != iProver_top
% 11.62/2.00      | r2_hidden(k4_tarski(k1_funct_1(sK4,sK2(sK4,sK3)),sK2(sK4,sK3)),k4_relat_1(sK4)) = iProver_top
% 11.62/2.00      | v1_funct_1(k4_relat_1(sK4)) != iProver_top
% 11.62/2.00      | v1_relat_1(k4_relat_1(sK4)) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_34565,c_810]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_10,plain,
% 11.62/2.00      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_820,plain,
% 11.62/2.00      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1531,plain,
% 11.62/2.00      ( k1_relat_1(k4_relat_1(sK4)) = k2_relat_1(sK4) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_805,c_820]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_34760,plain,
% 11.62/2.00      ( r2_hidden(k1_funct_1(sK4,sK2(sK4,sK3)),k2_relat_1(sK4)) != iProver_top
% 11.62/2.00      | r2_hidden(k4_tarski(k1_funct_1(sK4,sK2(sK4,sK3)),sK2(sK4,sK3)),k4_relat_1(sK4)) = iProver_top
% 11.62/2.00      | v1_funct_1(k4_relat_1(sK4)) != iProver_top
% 11.62/2.00      | v1_relat_1(k4_relat_1(sK4)) != iProver_top ),
% 11.62/2.00      inference(light_normalisation,[status(thm)],[c_34750,c_1531]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_33,plain,
% 11.62/2.00      ( r2_hidden(sK3,k2_relat_1(sK4)) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4,plain,
% 11.62/2.00      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 11.62/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_90,plain,
% 11.62/2.00      ( v1_relat_1(X0) != iProver_top
% 11.62/2.00      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_92,plain,
% 11.62/2.00      ( v1_relat_1(k4_relat_1(sK4)) = iProver_top
% 11.62/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.62/2.00      inference(instantiation,[status(thm)],[c_90]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1067,plain,
% 11.62/2.00      ( r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4) = iProver_top
% 11.62/2.00      | r2_hidden(sK3,k2_relat_1(sK4)) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_1066]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1115,plain,
% 11.62/2.00      ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4))
% 11.62/2.00      | ~ r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4)
% 11.62/2.00      | ~ v1_relat_1(sK4) ),
% 11.62/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1116,plain,
% 11.62/2.00      ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4)) = iProver_top
% 11.62/2.00      | r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4) != iProver_top
% 11.62/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_1115]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1171,plain,
% 11.62/2.00      ( ~ r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4))
% 11.62/2.00      | r2_hidden(k4_tarski(sK2(sK4,sK3),k1_funct_1(sK4,sK2(sK4,sK3))),sK4)
% 11.62/2.00      | ~ v1_funct_1(sK4)
% 11.62/2.00      | ~ v1_relat_1(sK4) ),
% 11.62/2.00      inference(instantiation,[status(thm)],[c_22]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1172,plain,
% 11.62/2.00      ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4)) != iProver_top
% 11.62/2.00      | r2_hidden(k4_tarski(sK2(sK4,sK3),k1_funct_1(sK4,sK2(sK4,sK3))),sK4) = iProver_top
% 11.62/2.00      | v1_funct_1(sK4) != iProver_top
% 11.62/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_1171]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2,plain,
% 11.62/2.00      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1503,plain,
% 11.62/2.00      ( r2_hidden(k1_funct_1(sK4,sK2(sK4,sK3)),k2_relat_1(sK4))
% 11.62/2.00      | ~ r2_hidden(k4_tarski(sK2(sK4,sK3),k1_funct_1(sK4,sK2(sK4,sK3))),sK4) ),
% 11.62/2.00      inference(instantiation,[status(thm)],[c_2]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1504,plain,
% 11.62/2.00      ( r2_hidden(k1_funct_1(sK4,sK2(sK4,sK3)),k2_relat_1(sK4)) = iProver_top
% 11.62/2.00      | r2_hidden(k4_tarski(sK2(sK4,sK3),k1_funct_1(sK4,sK2(sK4,sK3))),sK4) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_1503]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_15,plain,
% 11.62/2.00      ( ~ v1_funct_1(X0)
% 11.62/2.00      | v1_funct_1(k2_funct_1(X0))
% 11.62/2.00      | ~ v1_relat_1(X0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_817,plain,
% 11.62/2.00      ( v1_funct_1(X0) != iProver_top
% 11.62/2.00      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_5960,plain,
% 11.62/2.00      ( v1_funct_1(k4_relat_1(sK4)) = iProver_top
% 11.62/2.00      | v1_funct_1(sK4) != iProver_top
% 11.62/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_5951,c_817]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_34955,plain,
% 11.62/2.00      ( r2_hidden(k4_tarski(k1_funct_1(sK4,sK2(sK4,sK3)),sK2(sK4,sK3)),k4_relat_1(sK4)) = iProver_top ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_34760,c_30,c_31,c_33,c_92,c_1067,c_1116,c_1172,c_1504,
% 11.62/2.00                 c_5960]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_34961,plain,
% 11.62/2.00      ( r2_hidden(k1_funct_1(sK4,sK2(sK4,sK3)),k1_relat_1(k4_relat_1(sK4))) = iProver_top
% 11.62/2.00      | v1_relat_1(k4_relat_1(sK4)) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_34955,c_822]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_34978,plain,
% 11.62/2.00      ( r2_hidden(k1_funct_1(sK4,sK2(sK4,sK3)),k2_relat_1(sK4)) = iProver_top
% 11.62/2.00      | v1_relat_1(k4_relat_1(sK4)) != iProver_top ),
% 11.62/2.00      inference(light_normalisation,[status(thm)],[c_34961,c_1531]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_36558,plain,
% 11.62/2.00      ( r2_hidden(k1_funct_1(sK4,sK2(sK4,sK3)),k2_relat_1(sK4)) = iProver_top ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_34978,c_30,c_31,c_33,c_1067,c_1116,c_1172,c_1504]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_825,plain,
% 11.62/2.00      ( v1_relat_1(X0) != iProver_top
% 11.62/2.00      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2335,plain,
% 11.62/2.00      ( k5_relat_1(k4_relat_1(X0),k6_relat_1(k2_relat_1(k4_relat_1(X0)))) = k4_relat_1(X0)
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_825,c_819]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2986,plain,
% 11.62/2.00      ( k5_relat_1(k4_relat_1(sK4),k6_relat_1(k2_relat_1(k4_relat_1(sK4)))) = k4_relat_1(sK4) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_805,c_2335]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_9,plain,
% 11.62/2.00      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_821,plain,
% 11.62/2.00      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1818,plain,
% 11.62/2.00      ( k2_relat_1(k4_relat_1(sK4)) = k1_relat_1(sK4) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_805,c_821]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2988,plain,
% 11.62/2.00      ( k5_relat_1(k4_relat_1(sK4),k6_relat_1(k1_relat_1(sK4))) = k4_relat_1(sK4) ),
% 11.62/2.00      inference(light_normalisation,[status(thm)],[c_2986,c_1818]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4285,plain,
% 11.62/2.00      ( k1_relat_1(k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k4_relat_1(X0),X1)
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_825,c_4069]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_12702,plain,
% 11.62/2.00      ( k1_relat_1(k5_relat_1(k4_relat_1(sK4),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK4),X0) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_805,c_4285]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_12726,plain,
% 11.62/2.00      ( k10_relat_1(k4_relat_1(sK4),k1_relat_1(sK4)) = k1_relat_1(k4_relat_1(sK4)) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2988,c_12702]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4062,plain,
% 11.62/2.00      ( k10_relat_1(X0,k1_relat_1(sK4)) = k1_relat_1(k5_relat_1(X0,sK4))
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_805,c_823]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4428,plain,
% 11.62/2.00      ( k10_relat_1(k4_relat_1(X0),k1_relat_1(sK4)) = k1_relat_1(k5_relat_1(k4_relat_1(X0),sK4))
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_825,c_4062]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4714,plain,
% 11.62/2.00      ( k10_relat_1(k4_relat_1(sK4),k1_relat_1(sK4)) = k1_relat_1(k5_relat_1(k4_relat_1(sK4),sK4)) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_805,c_4428]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_12763,plain,
% 11.62/2.00      ( k10_relat_1(k4_relat_1(sK4),k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 11.62/2.00      inference(light_normalisation,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_12726,c_1531,c_4714]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_12896,plain,
% 11.62/2.00      ( k1_relat_1(k5_relat_1(k4_relat_1(sK4),sK4)) = k2_relat_1(sK4) ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_12763,c_4714]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_19,plain,
% 11.62/2.00      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 11.62/2.00      | ~ v1_funct_1(X1)
% 11.62/2.00      | ~ v1_funct_1(X2)
% 11.62/2.00      | ~ v1_relat_1(X2)
% 11.62/2.00      | ~ v1_relat_1(X1)
% 11.62/2.00      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 11.62/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_813,plain,
% 11.62/2.00      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 11.62/2.00      | r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
% 11.62/2.00      | v1_funct_1(X0) != iProver_top
% 11.62/2.00      | v1_funct_1(X1) != iProver_top
% 11.62/2.00      | v1_relat_1(X0) != iProver_top
% 11.62/2.00      | v1_relat_1(X1) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_13247,plain,
% 11.62/2.00      ( k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),X0) = k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),X0))
% 11.62/2.00      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 11.62/2.00      | v1_funct_1(k4_relat_1(sK4)) != iProver_top
% 11.62/2.00      | v1_funct_1(sK4) != iProver_top
% 11.62/2.00      | v1_relat_1(k4_relat_1(sK4)) != iProver_top
% 11.62/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_12896,c_813]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_28545,plain,
% 11.62/2.00      ( k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),X0) = k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),X0))
% 11.62/2.00      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_13247,c_30,c_31,c_92,c_5960]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_36568,plain,
% 11.62/2.00      ( k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,sK2(sK4,sK3)))) = k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),k1_funct_1(sK4,sK2(sK4,sK3))) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_36558,c_28545]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_36620,plain,
% 11.62/2.00      ( k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),k1_funct_1(sK4,sK2(sK4,sK3))) = k1_funct_1(sK4,sK2(sK4,sK3)) ),
% 11.62/2.00      inference(light_normalisation,[status(thm)],[c_36568,c_34565]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_40314,plain,
% 11.62/2.00      ( k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),sK3) = sK3 ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_40311,c_36620]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_28557,plain,
% 11.62/2.00      ( k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),sK3)) = k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),sK3) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_808,c_28545]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_40343,plain,
% 11.62/2.00      ( k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),sK3)) = sK3 ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_40314,c_28557]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_25,negated_conjecture,
% 11.62/2.00      ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
% 11.62/2.00      | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
% 11.62/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_5955,plain,
% 11.62/2.00      ( k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),sK3) != sK3
% 11.62/2.00      | k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),sK3)) != sK3 ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_5951,c_25]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_28653,plain,
% 11.62/2.00      ( k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),sK3)) != sK3 ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_28557,c_5955]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(contradiction,plain,
% 11.62/2.00      ( $false ),
% 11.62/2.00      inference(minisat,[status(thm)],[c_40343,c_28653]) ).
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.62/2.00  
% 11.62/2.00  ------                               Statistics
% 11.62/2.00  
% 11.62/2.00  ------ Selected
% 11.62/2.00  
% 11.62/2.00  total_time:                             1.112
% 11.62/2.00  
%------------------------------------------------------------------------------
