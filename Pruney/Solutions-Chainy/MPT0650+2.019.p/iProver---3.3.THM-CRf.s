%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:25 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 682 expanded)
%              Number of clauses        :   86 ( 192 expanded)
%              Number of leaves         :   18 ( 147 expanded)
%              Depth                    :   19
%              Number of atoms          :  463 (3128 expanded)
%              Number of equality atoms :  192 ( 982 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f42,plain,
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

fof(f43,plain,
    ( ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
      | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 )
    & r2_hidden(sK3,k2_relat_1(sK4))
    & v2_funct_1(sK4)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f33,f42])).

fof(f71,plain,(
    r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38,f37,f36])).

fof(f44,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f67])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1021,plain,
    ( r2_hidden(sK3,k2_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1034,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_22,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1022,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2336,plain,
    ( k1_funct_1(X0,sK2(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_1022])).

cnf(c_12293,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK3)) = sK3
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1021,c_2336])).

cnf(c_28,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1244,plain,
    ( r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4)
    | ~ r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1269,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK2(sK4,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_12953,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12293,c_28,c_27,c_25,c_1244,c_1269])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1023,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_12956,plain,
    ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_12953,c_1023])).

cnf(c_32,plain,
    ( r2_hidden(sK3,k2_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1245,plain,
    ( r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4) = iProver_top
    | r2_hidden(sK3,k2_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1244])).

cnf(c_13362,plain,
    ( r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12956,c_32,c_1245])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1031,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13368,plain,
    ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_13362,c_1031])).

cnf(c_29,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1266,plain,
    ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1267,plain,
    ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1266])).

cnf(c_13891,plain,
    ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13368,c_29,c_32,c_1245,c_1267])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_370,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_371,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_375,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_371,c_28,c_27])).

cnf(c_1015,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_322,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_323,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_funct_1(sK4) = k4_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_64,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_funct_1(sK4) = k4_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_325,plain,
    ( k2_funct_1(sK4) = k4_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_323,c_28,c_27,c_26,c_64])).

cnf(c_1081,plain,
    ( k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,X0)) = X0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1015,c_325])).

cnf(c_13898,plain,
    ( k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,sK2(sK4,sK3))) = sK2(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_13891,c_1081])).

cnf(c_13923,plain,
    ( k1_funct_1(k4_relat_1(sK4),sK3) = sK2(sK4,sK3) ),
    inference(light_normalisation,[status(thm)],[c_13898,c_12953])).

cnf(c_1019,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1033,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1028,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1908,plain,
    ( k5_relat_1(k4_relat_1(X0),k6_relat_1(k2_relat_1(k4_relat_1(X0)))) = k4_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1033,c_1028])).

cnf(c_7382,plain,
    ( k5_relat_1(k4_relat_1(sK4),k6_relat_1(k2_relat_1(k4_relat_1(sK4)))) = k4_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1019,c_1908])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1030,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1803,plain,
    ( k2_relat_1(k4_relat_1(sK4)) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1019,c_1030])).

cnf(c_7384,plain,
    ( k5_relat_1(k4_relat_1(sK4),k6_relat_1(k1_relat_1(sK4))) = k4_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_7382,c_1803])).

cnf(c_17,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1025,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1032,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3256,plain,
    ( k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X0,k6_relat_1(X1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_1032])).

cnf(c_11,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3264,plain,
    ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3256,c_11])).

cnf(c_3294,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k4_relat_1(X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1033,c_3264])).

cnf(c_8403,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(sK4),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK4),X0) ),
    inference(superposition,[status(thm)],[c_1019,c_3294])).

cnf(c_8551,plain,
    ( k10_relat_1(k4_relat_1(sK4),k1_relat_1(sK4)) = k1_relat_1(k4_relat_1(sK4)) ),
    inference(superposition,[status(thm)],[c_7384,c_8403])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1029,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1635,plain,
    ( k1_relat_1(k4_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1019,c_1029])).

cnf(c_3257,plain,
    ( k10_relat_1(X0,k1_relat_1(sK4)) = k1_relat_1(k5_relat_1(X0,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1019,c_1032])).

cnf(c_3659,plain,
    ( k10_relat_1(k4_relat_1(X0),k1_relat_1(sK4)) = k1_relat_1(k5_relat_1(k4_relat_1(X0),sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1033,c_3257])).

cnf(c_3774,plain,
    ( k10_relat_1(k4_relat_1(sK4),k1_relat_1(sK4)) = k1_relat_1(k5_relat_1(k4_relat_1(sK4),sK4)) ),
    inference(superposition,[status(thm)],[c_1019,c_3659])).

cnf(c_8566,plain,
    ( k10_relat_1(k4_relat_1(sK4),k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_8551,c_1635,c_3774])).

cnf(c_8781,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(sK4),sK4)) = k2_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_8566,c_3774])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1024,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9004,plain,
    ( k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),X0)) = k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),X0)
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | v1_funct_1(k4_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k4_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8781,c_1024])).

cnf(c_30,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_86,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_88,plain,
    ( v1_relat_1(k4_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1027,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2330,plain,
    ( v1_funct_1(k4_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_325,c_1027])).

cnf(c_10473,plain,
    ( k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),X0)) = k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),X0)
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9004,c_29,c_30,c_88,c_2330])).

cnf(c_10484,plain,
    ( k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),sK3)) = k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),sK3) ),
    inference(superposition,[status(thm)],[c_1021,c_10473])).

cnf(c_24,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1102,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),sK3) != sK3
    | k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),sK3)) != sK3 ),
    inference(light_normalisation,[status(thm)],[c_24,c_325])).

cnf(c_10600,plain,
    ( k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),sK3)) != sK3 ),
    inference(demodulation,[status(thm)],[c_10484,c_1102])).

cnf(c_14214,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK3)) != sK3 ),
    inference(demodulation,[status(thm)],[c_13923,c_10600])).

cnf(c_14225,plain,
    ( sK3 != sK3 ),
    inference(light_normalisation,[status(thm)],[c_14214,c_12953])).

cnf(c_14226,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_14225])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:16:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.89/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/0.98  
% 3.89/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.89/0.98  
% 3.89/0.98  ------  iProver source info
% 3.89/0.98  
% 3.89/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.89/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.89/0.98  git: non_committed_changes: false
% 3.89/0.98  git: last_make_outside_of_git: false
% 3.89/0.98  
% 3.89/0.98  ------ 
% 3.89/0.98  
% 3.89/0.98  ------ Input Options
% 3.89/0.98  
% 3.89/0.98  --out_options                           all
% 3.89/0.98  --tptp_safe_out                         true
% 3.89/0.98  --problem_path                          ""
% 3.89/0.98  --include_path                          ""
% 3.89/0.98  --clausifier                            res/vclausify_rel
% 3.89/0.98  --clausifier_options                    --mode clausify
% 3.89/0.98  --stdin                                 false
% 3.89/0.98  --stats_out                             all
% 3.89/0.98  
% 3.89/0.98  ------ General Options
% 3.89/0.98  
% 3.89/0.98  --fof                                   false
% 3.89/0.98  --time_out_real                         305.
% 3.89/0.98  --time_out_virtual                      -1.
% 3.89/0.98  --symbol_type_check                     false
% 3.89/0.98  --clausify_out                          false
% 3.89/0.98  --sig_cnt_out                           false
% 3.89/0.98  --trig_cnt_out                          false
% 3.89/0.98  --trig_cnt_out_tolerance                1.
% 3.89/0.98  --trig_cnt_out_sk_spl                   false
% 3.89/0.98  --abstr_cl_out                          false
% 3.89/0.98  
% 3.89/0.98  ------ Global Options
% 3.89/0.98  
% 3.89/0.98  --schedule                              default
% 3.89/0.98  --add_important_lit                     false
% 3.89/0.98  --prop_solver_per_cl                    1000
% 3.89/0.98  --min_unsat_core                        false
% 3.89/0.98  --soft_assumptions                      false
% 3.89/0.98  --soft_lemma_size                       3
% 3.89/0.98  --prop_impl_unit_size                   0
% 3.89/0.98  --prop_impl_unit                        []
% 3.89/0.98  --share_sel_clauses                     true
% 3.89/0.98  --reset_solvers                         false
% 3.89/0.98  --bc_imp_inh                            [conj_cone]
% 3.89/0.98  --conj_cone_tolerance                   3.
% 3.89/0.98  --extra_neg_conj                        none
% 3.89/0.98  --large_theory_mode                     true
% 3.89/0.98  --prolific_symb_bound                   200
% 3.89/0.98  --lt_threshold                          2000
% 3.89/0.98  --clause_weak_htbl                      true
% 3.89/0.98  --gc_record_bc_elim                     false
% 3.89/0.98  
% 3.89/0.98  ------ Preprocessing Options
% 3.89/0.98  
% 3.89/0.98  --preprocessing_flag                    true
% 3.89/0.98  --time_out_prep_mult                    0.1
% 3.89/0.98  --splitting_mode                        input
% 3.89/0.98  --splitting_grd                         true
% 3.89/0.98  --splitting_cvd                         false
% 3.89/0.98  --splitting_cvd_svl                     false
% 3.89/0.98  --splitting_nvd                         32
% 3.89/0.98  --sub_typing                            true
% 3.89/0.98  --prep_gs_sim                           true
% 3.89/0.98  --prep_unflatten                        true
% 3.89/0.98  --prep_res_sim                          true
% 3.89/0.98  --prep_upred                            true
% 3.89/0.98  --prep_sem_filter                       exhaustive
% 3.89/0.98  --prep_sem_filter_out                   false
% 3.89/0.98  --pred_elim                             true
% 3.89/0.98  --res_sim_input                         true
% 3.89/0.98  --eq_ax_congr_red                       true
% 3.89/0.98  --pure_diseq_elim                       true
% 3.89/0.98  --brand_transform                       false
% 3.89/0.98  --non_eq_to_eq                          false
% 3.89/0.98  --prep_def_merge                        true
% 3.89/0.98  --prep_def_merge_prop_impl              false
% 3.89/0.98  --prep_def_merge_mbd                    true
% 3.89/0.98  --prep_def_merge_tr_red                 false
% 3.89/0.98  --prep_def_merge_tr_cl                  false
% 3.89/0.98  --smt_preprocessing                     true
% 3.89/0.98  --smt_ac_axioms                         fast
% 3.89/0.98  --preprocessed_out                      false
% 3.89/0.98  --preprocessed_stats                    false
% 3.89/0.98  
% 3.89/0.98  ------ Abstraction refinement Options
% 3.89/0.98  
% 3.89/0.98  --abstr_ref                             []
% 3.89/0.98  --abstr_ref_prep                        false
% 3.89/0.98  --abstr_ref_until_sat                   false
% 3.89/0.98  --abstr_ref_sig_restrict                funpre
% 3.89/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.89/0.98  --abstr_ref_under                       []
% 3.89/0.98  
% 3.89/0.98  ------ SAT Options
% 3.89/0.98  
% 3.89/0.98  --sat_mode                              false
% 3.89/0.98  --sat_fm_restart_options                ""
% 3.89/0.98  --sat_gr_def                            false
% 3.89/0.98  --sat_epr_types                         true
% 3.89/0.98  --sat_non_cyclic_types                  false
% 3.89/0.98  --sat_finite_models                     false
% 3.89/0.98  --sat_fm_lemmas                         false
% 3.89/0.98  --sat_fm_prep                           false
% 3.89/0.98  --sat_fm_uc_incr                        true
% 3.89/0.98  --sat_out_model                         small
% 3.89/0.98  --sat_out_clauses                       false
% 3.89/0.98  
% 3.89/0.98  ------ QBF Options
% 3.89/0.98  
% 3.89/0.98  --qbf_mode                              false
% 3.89/0.98  --qbf_elim_univ                         false
% 3.89/0.98  --qbf_dom_inst                          none
% 3.89/0.98  --qbf_dom_pre_inst                      false
% 3.89/0.98  --qbf_sk_in                             false
% 3.89/0.98  --qbf_pred_elim                         true
% 3.89/0.98  --qbf_split                             512
% 3.89/0.98  
% 3.89/0.98  ------ BMC1 Options
% 3.89/0.98  
% 3.89/0.98  --bmc1_incremental                      false
% 3.89/0.98  --bmc1_axioms                           reachable_all
% 3.89/0.98  --bmc1_min_bound                        0
% 3.89/0.98  --bmc1_max_bound                        -1
% 3.89/0.98  --bmc1_max_bound_default                -1
% 3.89/0.98  --bmc1_symbol_reachability              true
% 3.89/0.98  --bmc1_property_lemmas                  false
% 3.89/0.98  --bmc1_k_induction                      false
% 3.89/0.98  --bmc1_non_equiv_states                 false
% 3.89/0.98  --bmc1_deadlock                         false
% 3.89/0.98  --bmc1_ucm                              false
% 3.89/0.98  --bmc1_add_unsat_core                   none
% 3.89/0.98  --bmc1_unsat_core_children              false
% 3.89/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.89/0.98  --bmc1_out_stat                         full
% 3.89/0.98  --bmc1_ground_init                      false
% 3.89/0.98  --bmc1_pre_inst_next_state              false
% 3.89/0.98  --bmc1_pre_inst_state                   false
% 3.89/0.98  --bmc1_pre_inst_reach_state             false
% 3.89/0.98  --bmc1_out_unsat_core                   false
% 3.89/0.98  --bmc1_aig_witness_out                  false
% 3.89/0.98  --bmc1_verbose                          false
% 3.89/0.98  --bmc1_dump_clauses_tptp                false
% 3.89/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.89/0.98  --bmc1_dump_file                        -
% 3.89/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.89/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.89/0.98  --bmc1_ucm_extend_mode                  1
% 3.89/0.98  --bmc1_ucm_init_mode                    2
% 3.89/0.98  --bmc1_ucm_cone_mode                    none
% 3.89/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.89/0.98  --bmc1_ucm_relax_model                  4
% 3.89/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.89/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.89/0.98  --bmc1_ucm_layered_model                none
% 3.89/0.98  --bmc1_ucm_max_lemma_size               10
% 3.89/0.98  
% 3.89/0.98  ------ AIG Options
% 3.89/0.98  
% 3.89/0.98  --aig_mode                              false
% 3.89/0.98  
% 3.89/0.98  ------ Instantiation Options
% 3.89/0.98  
% 3.89/0.98  --instantiation_flag                    true
% 3.89/0.98  --inst_sos_flag                         false
% 3.89/0.98  --inst_sos_phase                        true
% 3.89/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.89/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.89/0.98  --inst_lit_sel_side                     num_symb
% 3.89/0.98  --inst_solver_per_active                1400
% 3.89/0.98  --inst_solver_calls_frac                1.
% 3.89/0.98  --inst_passive_queue_type               priority_queues
% 3.89/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.89/0.98  --inst_passive_queues_freq              [25;2]
% 3.89/0.98  --inst_dismatching                      true
% 3.89/0.98  --inst_eager_unprocessed_to_passive     true
% 3.89/0.98  --inst_prop_sim_given                   true
% 3.89/0.98  --inst_prop_sim_new                     false
% 3.89/0.98  --inst_subs_new                         false
% 3.89/0.98  --inst_eq_res_simp                      false
% 3.89/0.98  --inst_subs_given                       false
% 3.89/0.98  --inst_orphan_elimination               true
% 3.89/0.98  --inst_learning_loop_flag               true
% 3.89/0.98  --inst_learning_start                   3000
% 3.89/0.98  --inst_learning_factor                  2
% 3.89/0.98  --inst_start_prop_sim_after_learn       3
% 3.89/0.98  --inst_sel_renew                        solver
% 3.89/0.98  --inst_lit_activity_flag                true
% 3.89/0.98  --inst_restr_to_given                   false
% 3.89/0.98  --inst_activity_threshold               500
% 3.89/0.98  --inst_out_proof                        true
% 3.89/0.98  
% 3.89/0.98  ------ Resolution Options
% 3.89/0.98  
% 3.89/0.98  --resolution_flag                       true
% 3.89/0.98  --res_lit_sel                           adaptive
% 3.89/0.98  --res_lit_sel_side                      none
% 3.89/0.98  --res_ordering                          kbo
% 3.89/0.98  --res_to_prop_solver                    active
% 3.89/0.98  --res_prop_simpl_new                    false
% 3.89/0.98  --res_prop_simpl_given                  true
% 3.89/0.98  --res_passive_queue_type                priority_queues
% 3.89/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.89/0.98  --res_passive_queues_freq               [15;5]
% 3.89/0.98  --res_forward_subs                      full
% 3.89/0.98  --res_backward_subs                     full
% 3.89/0.98  --res_forward_subs_resolution           true
% 3.89/0.98  --res_backward_subs_resolution          true
% 3.89/0.98  --res_orphan_elimination                true
% 3.89/0.98  --res_time_limit                        2.
% 3.89/0.98  --res_out_proof                         true
% 3.89/0.98  
% 3.89/0.98  ------ Superposition Options
% 3.89/0.98  
% 3.89/0.98  --superposition_flag                    true
% 3.89/0.98  --sup_passive_queue_type                priority_queues
% 3.89/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.89/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.89/0.98  --demod_completeness_check              fast
% 3.89/0.98  --demod_use_ground                      true
% 3.89/0.98  --sup_to_prop_solver                    passive
% 3.89/0.98  --sup_prop_simpl_new                    true
% 3.89/0.98  --sup_prop_simpl_given                  true
% 3.89/0.98  --sup_fun_splitting                     false
% 3.89/0.98  --sup_smt_interval                      50000
% 3.89/0.98  
% 3.89/0.98  ------ Superposition Simplification Setup
% 3.89/0.98  
% 3.89/0.98  --sup_indices_passive                   []
% 3.89/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.89/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.98  --sup_full_bw                           [BwDemod]
% 3.89/0.98  --sup_immed_triv                        [TrivRules]
% 3.89/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.98  --sup_immed_bw_main                     []
% 3.89/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.89/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.89/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.89/0.98  
% 3.89/0.98  ------ Combination Options
% 3.89/0.98  
% 3.89/0.98  --comb_res_mult                         3
% 3.89/0.98  --comb_sup_mult                         2
% 3.89/0.98  --comb_inst_mult                        10
% 3.89/0.98  
% 3.89/0.98  ------ Debug Options
% 3.89/0.98  
% 3.89/0.98  --dbg_backtrace                         false
% 3.89/0.98  --dbg_dump_prop_clauses                 false
% 3.89/0.98  --dbg_dump_prop_clauses_file            -
% 3.89/0.98  --dbg_out_stat                          false
% 3.89/0.98  ------ Parsing...
% 3.89/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.89/0.98  
% 3.89/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.89/0.98  
% 3.89/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.89/0.98  
% 3.89/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/0.98  ------ Proving...
% 3.89/0.98  ------ Problem Properties 
% 3.89/0.98  
% 3.89/0.98  
% 3.89/0.98  clauses                                 28
% 3.89/0.98  conjectures                             4
% 3.89/0.98  EPR                                     2
% 3.89/0.98  Horn                                    27
% 3.89/0.98  unary                                   7
% 3.89/0.98  binary                                  10
% 3.89/0.98  lits                                    65
% 3.89/0.98  lits eq                                 18
% 3.89/0.98  fd_pure                                 0
% 3.89/0.98  fd_pseudo                               0
% 3.89/0.98  fd_cond                                 0
% 3.89/0.98  fd_pseudo_cond                          3
% 3.89/0.98  AC symbols                              0
% 3.89/0.98  
% 3.89/0.98  ------ Schedule dynamic 5 is on 
% 3.89/0.98  
% 3.89/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.89/0.98  
% 3.89/0.98  
% 3.89/0.98  ------ 
% 3.89/0.98  Current options:
% 3.89/0.98  ------ 
% 3.89/0.98  
% 3.89/0.98  ------ Input Options
% 3.89/0.98  
% 3.89/0.98  --out_options                           all
% 3.89/0.98  --tptp_safe_out                         true
% 3.89/0.98  --problem_path                          ""
% 3.89/0.98  --include_path                          ""
% 3.89/0.98  --clausifier                            res/vclausify_rel
% 3.89/0.98  --clausifier_options                    --mode clausify
% 3.89/0.98  --stdin                                 false
% 3.89/0.98  --stats_out                             all
% 3.89/0.98  
% 3.89/0.98  ------ General Options
% 3.89/0.98  
% 3.89/0.98  --fof                                   false
% 3.89/0.98  --time_out_real                         305.
% 3.89/0.98  --time_out_virtual                      -1.
% 3.89/0.98  --symbol_type_check                     false
% 3.89/0.98  --clausify_out                          false
% 3.89/0.98  --sig_cnt_out                           false
% 3.89/0.98  --trig_cnt_out                          false
% 3.89/0.98  --trig_cnt_out_tolerance                1.
% 3.89/0.98  --trig_cnt_out_sk_spl                   false
% 3.89/0.98  --abstr_cl_out                          false
% 3.89/0.98  
% 3.89/0.98  ------ Global Options
% 3.89/0.98  
% 3.89/0.98  --schedule                              default
% 3.89/0.98  --add_important_lit                     false
% 3.89/0.98  --prop_solver_per_cl                    1000
% 3.89/0.98  --min_unsat_core                        false
% 3.89/0.98  --soft_assumptions                      false
% 3.89/0.98  --soft_lemma_size                       3
% 3.89/0.98  --prop_impl_unit_size                   0
% 3.89/0.98  --prop_impl_unit                        []
% 3.89/0.98  --share_sel_clauses                     true
% 3.89/0.98  --reset_solvers                         false
% 3.89/0.98  --bc_imp_inh                            [conj_cone]
% 3.89/0.98  --conj_cone_tolerance                   3.
% 3.89/0.98  --extra_neg_conj                        none
% 3.89/0.98  --large_theory_mode                     true
% 3.89/0.98  --prolific_symb_bound                   200
% 3.89/0.98  --lt_threshold                          2000
% 3.89/0.98  --clause_weak_htbl                      true
% 3.89/0.98  --gc_record_bc_elim                     false
% 3.89/0.98  
% 3.89/0.98  ------ Preprocessing Options
% 3.89/0.98  
% 3.89/0.98  --preprocessing_flag                    true
% 3.89/0.98  --time_out_prep_mult                    0.1
% 3.89/0.98  --splitting_mode                        input
% 3.89/0.98  --splitting_grd                         true
% 3.89/0.98  --splitting_cvd                         false
% 3.89/0.98  --splitting_cvd_svl                     false
% 3.89/0.98  --splitting_nvd                         32
% 3.89/0.98  --sub_typing                            true
% 3.89/0.98  --prep_gs_sim                           true
% 3.89/0.98  --prep_unflatten                        true
% 3.89/0.98  --prep_res_sim                          true
% 3.89/0.98  --prep_upred                            true
% 3.89/0.98  --prep_sem_filter                       exhaustive
% 3.89/0.98  --prep_sem_filter_out                   false
% 3.89/0.98  --pred_elim                             true
% 3.89/0.98  --res_sim_input                         true
% 3.89/0.98  --eq_ax_congr_red                       true
% 3.89/0.98  --pure_diseq_elim                       true
% 3.89/0.98  --brand_transform                       false
% 3.89/0.98  --non_eq_to_eq                          false
% 3.89/0.98  --prep_def_merge                        true
% 3.89/0.98  --prep_def_merge_prop_impl              false
% 3.89/0.98  --prep_def_merge_mbd                    true
% 3.89/0.98  --prep_def_merge_tr_red                 false
% 3.89/0.98  --prep_def_merge_tr_cl                  false
% 3.89/0.98  --smt_preprocessing                     true
% 3.89/0.98  --smt_ac_axioms                         fast
% 3.89/0.98  --preprocessed_out                      false
% 3.89/0.98  --preprocessed_stats                    false
% 3.89/0.98  
% 3.89/0.98  ------ Abstraction refinement Options
% 3.89/0.98  
% 3.89/0.98  --abstr_ref                             []
% 3.89/0.98  --abstr_ref_prep                        false
% 3.89/0.98  --abstr_ref_until_sat                   false
% 3.89/0.98  --abstr_ref_sig_restrict                funpre
% 3.89/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.89/0.98  --abstr_ref_under                       []
% 3.89/0.98  
% 3.89/0.98  ------ SAT Options
% 3.89/0.98  
% 3.89/0.98  --sat_mode                              false
% 3.89/0.98  --sat_fm_restart_options                ""
% 3.89/0.98  --sat_gr_def                            false
% 3.89/0.98  --sat_epr_types                         true
% 3.89/0.98  --sat_non_cyclic_types                  false
% 3.89/0.98  --sat_finite_models                     false
% 3.89/0.98  --sat_fm_lemmas                         false
% 3.89/0.98  --sat_fm_prep                           false
% 3.89/0.98  --sat_fm_uc_incr                        true
% 3.89/0.98  --sat_out_model                         small
% 3.89/0.98  --sat_out_clauses                       false
% 3.89/0.98  
% 3.89/0.98  ------ QBF Options
% 3.89/0.98  
% 3.89/0.98  --qbf_mode                              false
% 3.89/0.98  --qbf_elim_univ                         false
% 3.89/0.98  --qbf_dom_inst                          none
% 3.89/0.98  --qbf_dom_pre_inst                      false
% 3.89/0.98  --qbf_sk_in                             false
% 3.89/0.98  --qbf_pred_elim                         true
% 3.89/0.98  --qbf_split                             512
% 3.89/0.98  
% 3.89/0.98  ------ BMC1 Options
% 3.89/0.98  
% 3.89/0.98  --bmc1_incremental                      false
% 3.89/0.98  --bmc1_axioms                           reachable_all
% 3.89/0.98  --bmc1_min_bound                        0
% 3.89/0.98  --bmc1_max_bound                        -1
% 3.89/0.98  --bmc1_max_bound_default                -1
% 3.89/0.98  --bmc1_symbol_reachability              true
% 3.89/0.98  --bmc1_property_lemmas                  false
% 3.89/0.98  --bmc1_k_induction                      false
% 3.89/0.98  --bmc1_non_equiv_states                 false
% 3.89/0.98  --bmc1_deadlock                         false
% 3.89/0.98  --bmc1_ucm                              false
% 3.89/0.98  --bmc1_add_unsat_core                   none
% 3.89/0.98  --bmc1_unsat_core_children              false
% 3.89/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.89/0.98  --bmc1_out_stat                         full
% 3.89/0.98  --bmc1_ground_init                      false
% 3.89/0.98  --bmc1_pre_inst_next_state              false
% 3.89/0.98  --bmc1_pre_inst_state                   false
% 3.89/0.98  --bmc1_pre_inst_reach_state             false
% 3.89/0.98  --bmc1_out_unsat_core                   false
% 3.89/0.98  --bmc1_aig_witness_out                  false
% 3.89/0.98  --bmc1_verbose                          false
% 3.89/0.98  --bmc1_dump_clauses_tptp                false
% 3.89/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.89/0.98  --bmc1_dump_file                        -
% 3.89/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.89/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.89/0.98  --bmc1_ucm_extend_mode                  1
% 3.89/0.98  --bmc1_ucm_init_mode                    2
% 3.89/0.98  --bmc1_ucm_cone_mode                    none
% 3.89/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.89/0.98  --bmc1_ucm_relax_model                  4
% 3.89/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.89/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.89/0.98  --bmc1_ucm_layered_model                none
% 3.89/0.98  --bmc1_ucm_max_lemma_size               10
% 3.89/0.98  
% 3.89/0.98  ------ AIG Options
% 3.89/0.98  
% 3.89/0.98  --aig_mode                              false
% 3.89/0.98  
% 3.89/0.98  ------ Instantiation Options
% 3.89/0.98  
% 3.89/0.98  --instantiation_flag                    true
% 3.89/0.98  --inst_sos_flag                         false
% 3.89/0.98  --inst_sos_phase                        true
% 3.89/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.89/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.89/0.98  --inst_lit_sel_side                     none
% 3.89/0.98  --inst_solver_per_active                1400
% 3.89/0.98  --inst_solver_calls_frac                1.
% 3.89/0.98  --inst_passive_queue_type               priority_queues
% 3.89/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.89/0.98  --inst_passive_queues_freq              [25;2]
% 3.89/0.98  --inst_dismatching                      true
% 3.89/0.98  --inst_eager_unprocessed_to_passive     true
% 3.89/0.98  --inst_prop_sim_given                   true
% 3.89/0.98  --inst_prop_sim_new                     false
% 3.89/0.98  --inst_subs_new                         false
% 3.89/0.98  --inst_eq_res_simp                      false
% 3.89/0.98  --inst_subs_given                       false
% 3.89/0.98  --inst_orphan_elimination               true
% 3.89/0.98  --inst_learning_loop_flag               true
% 3.89/0.98  --inst_learning_start                   3000
% 3.89/0.98  --inst_learning_factor                  2
% 3.89/0.98  --inst_start_prop_sim_after_learn       3
% 3.89/0.98  --inst_sel_renew                        solver
% 3.89/0.98  --inst_lit_activity_flag                true
% 3.89/0.98  --inst_restr_to_given                   false
% 3.89/0.98  --inst_activity_threshold               500
% 3.89/0.98  --inst_out_proof                        true
% 3.89/0.98  
% 3.89/0.98  ------ Resolution Options
% 3.89/0.98  
% 3.89/0.98  --resolution_flag                       false
% 3.89/0.98  --res_lit_sel                           adaptive
% 3.89/0.98  --res_lit_sel_side                      none
% 3.89/0.98  --res_ordering                          kbo
% 3.89/0.98  --res_to_prop_solver                    active
% 3.89/0.98  --res_prop_simpl_new                    false
% 3.89/0.98  --res_prop_simpl_given                  true
% 3.89/0.98  --res_passive_queue_type                priority_queues
% 3.89/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.89/0.98  --res_passive_queues_freq               [15;5]
% 3.89/0.98  --res_forward_subs                      full
% 3.89/0.98  --res_backward_subs                     full
% 3.89/0.98  --res_forward_subs_resolution           true
% 3.89/0.98  --res_backward_subs_resolution          true
% 3.89/0.98  --res_orphan_elimination                true
% 3.89/0.98  --res_time_limit                        2.
% 3.89/0.98  --res_out_proof                         true
% 3.89/0.98  
% 3.89/0.98  ------ Superposition Options
% 3.89/0.98  
% 3.89/0.98  --superposition_flag                    true
% 3.89/0.98  --sup_passive_queue_type                priority_queues
% 3.89/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.89/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.89/0.98  --demod_completeness_check              fast
% 3.89/0.98  --demod_use_ground                      true
% 3.89/0.98  --sup_to_prop_solver                    passive
% 3.89/0.98  --sup_prop_simpl_new                    true
% 3.89/0.98  --sup_prop_simpl_given                  true
% 3.89/0.98  --sup_fun_splitting                     false
% 3.89/0.98  --sup_smt_interval                      50000
% 3.89/0.98  
% 3.89/0.98  ------ Superposition Simplification Setup
% 3.89/0.98  
% 3.89/0.98  --sup_indices_passive                   []
% 3.89/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.89/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.98  --sup_full_bw                           [BwDemod]
% 3.89/0.98  --sup_immed_triv                        [TrivRules]
% 3.89/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.98  --sup_immed_bw_main                     []
% 3.89/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.89/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.89/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.89/0.98  
% 3.89/0.98  ------ Combination Options
% 3.89/0.98  
% 3.89/0.98  --comb_res_mult                         3
% 3.89/0.98  --comb_sup_mult                         2
% 3.89/0.98  --comb_inst_mult                        10
% 3.89/0.98  
% 3.89/0.98  ------ Debug Options
% 3.89/0.98  
% 3.89/0.98  --dbg_backtrace                         false
% 3.89/0.98  --dbg_dump_prop_clauses                 false
% 3.89/0.98  --dbg_dump_prop_clauses_file            -
% 3.89/0.98  --dbg_out_stat                          false
% 3.89/0.98  
% 3.89/0.98  
% 3.89/0.98  
% 3.89/0.98  
% 3.89/0.98  ------ Proving...
% 3.89/0.98  
% 3.89/0.98  
% 3.89/0.98  % SZS status Theorem for theBenchmark.p
% 3.89/0.98  
% 3.89/0.98   Resolution empty clause
% 3.89/0.98  
% 3.89/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.89/0.98  
% 3.89/0.98  fof(f14,conjecture,(
% 3.89/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 3.89/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f15,negated_conjecture,(
% 3.89/0.98    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 3.89/0.98    inference(negated_conjecture,[],[f14])).
% 3.89/0.98  
% 3.89/0.98  fof(f32,plain,(
% 3.89/0.98    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.89/0.98    inference(ennf_transformation,[],[f15])).
% 3.89/0.98  
% 3.89/0.98  fof(f33,plain,(
% 3.89/0.98    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.89/0.98    inference(flattening,[],[f32])).
% 3.89/0.98  
% 3.89/0.98  fof(f42,plain,(
% 3.89/0.98    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3 | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3) & r2_hidden(sK3,k2_relat_1(sK4)) & v2_funct_1(sK4) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 3.89/0.98    introduced(choice_axiom,[])).
% 3.89/0.98  
% 3.89/0.98  fof(f43,plain,(
% 3.89/0.98    (k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3 | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3) & r2_hidden(sK3,k2_relat_1(sK4)) & v2_funct_1(sK4) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 3.89/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f33,f42])).
% 3.89/0.98  
% 3.89/0.98  fof(f71,plain,(
% 3.89/0.98    r2_hidden(sK3,k2_relat_1(sK4))),
% 3.89/0.98    inference(cnf_transformation,[],[f43])).
% 3.89/0.98  
% 3.89/0.98  fof(f1,axiom,(
% 3.89/0.98    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 3.89/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f34,plain,(
% 3.89/0.98    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 3.89/0.98    inference(nnf_transformation,[],[f1])).
% 3.89/0.98  
% 3.89/0.98  fof(f35,plain,(
% 3.89/0.98    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.89/0.98    inference(rectify,[],[f34])).
% 3.89/0.98  
% 3.89/0.98  fof(f38,plain,(
% 3.89/0.98    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0))),
% 3.89/0.98    introduced(choice_axiom,[])).
% 3.89/0.98  
% 3.89/0.98  fof(f37,plain,(
% 3.89/0.98    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0))) )),
% 3.89/0.98    introduced(choice_axiom,[])).
% 3.89/0.98  
% 3.89/0.98  fof(f36,plain,(
% 3.89/0.98    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.89/0.98    introduced(choice_axiom,[])).
% 3.89/0.98  
% 3.89/0.98  fof(f39,plain,(
% 3.89/0.98    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 3.89/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38,f37,f36])).
% 3.89/0.98  
% 3.89/0.98  fof(f44,plain,(
% 3.89/0.98    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 3.89/0.98    inference(cnf_transformation,[],[f39])).
% 3.89/0.98  
% 3.89/0.98  fof(f74,plain,(
% 3.89/0.98    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 3.89/0.98    inference(equality_resolution,[],[f44])).
% 3.89/0.98  
% 3.89/0.98  fof(f13,axiom,(
% 3.89/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.89/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f30,plain,(
% 3.89/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.89/0.98    inference(ennf_transformation,[],[f13])).
% 3.89/0.98  
% 3.89/0.98  fof(f31,plain,(
% 3.89/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.89/0.98    inference(flattening,[],[f30])).
% 3.89/0.98  
% 3.89/0.98  fof(f40,plain,(
% 3.89/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.89/0.98    inference(nnf_transformation,[],[f31])).
% 3.89/0.98  
% 3.89/0.98  fof(f41,plain,(
% 3.89/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.89/0.98    inference(flattening,[],[f40])).
% 3.89/0.98  
% 3.89/0.98  fof(f66,plain,(
% 3.89/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f41])).
% 3.89/0.98  
% 3.89/0.98  fof(f68,plain,(
% 3.89/0.98    v1_relat_1(sK4)),
% 3.89/0.98    inference(cnf_transformation,[],[f43])).
% 3.89/0.98  
% 3.89/0.98  fof(f69,plain,(
% 3.89/0.98    v1_funct_1(sK4)),
% 3.89/0.98    inference(cnf_transformation,[],[f43])).
% 3.89/0.98  
% 3.89/0.98  fof(f67,plain,(
% 3.89/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f41])).
% 3.89/0.98  
% 3.89/0.98  fof(f75,plain,(
% 3.89/0.98    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.89/0.98    inference(equality_resolution,[],[f67])).
% 3.89/0.98  
% 3.89/0.98  fof(f4,axiom,(
% 3.89/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.89/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f18,plain,(
% 3.89/0.98    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 3.89/0.98    inference(ennf_transformation,[],[f4])).
% 3.89/0.98  
% 3.89/0.98  fof(f19,plain,(
% 3.89/0.98    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 3.89/0.98    inference(flattening,[],[f18])).
% 3.89/0.98  
% 3.89/0.98  fof(f50,plain,(
% 3.89/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f19])).
% 3.89/0.98  
% 3.89/0.98  fof(f12,axiom,(
% 3.89/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 3.89/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f28,plain,(
% 3.89/0.98    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.89/0.98    inference(ennf_transformation,[],[f12])).
% 3.89/0.98  
% 3.89/0.98  fof(f29,plain,(
% 3.89/0.98    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.89/0.98    inference(flattening,[],[f28])).
% 3.89/0.98  
% 3.89/0.98  fof(f63,plain,(
% 3.89/0.98    ( ! [X0,X1] : (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f29])).
% 3.89/0.98  
% 3.89/0.98  fof(f70,plain,(
% 3.89/0.98    v2_funct_1(sK4)),
% 3.89/0.98    inference(cnf_transformation,[],[f43])).
% 3.89/0.98  
% 3.89/0.98  fof(f8,axiom,(
% 3.89/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.89/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f22,plain,(
% 3.89/0.98    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.89/0.98    inference(ennf_transformation,[],[f8])).
% 3.89/0.98  
% 3.89/0.98  fof(f23,plain,(
% 3.89/0.98    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.89/0.98    inference(flattening,[],[f22])).
% 3.89/0.98  
% 3.89/0.98  fof(f57,plain,(
% 3.89/0.98    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f23])).
% 3.89/0.98  
% 3.89/0.98  fof(f2,axiom,(
% 3.89/0.98    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 3.89/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f16,plain,(
% 3.89/0.98    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.89/0.98    inference(ennf_transformation,[],[f2])).
% 3.89/0.98  
% 3.89/0.98  fof(f48,plain,(
% 3.89/0.98    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f16])).
% 3.89/0.98  
% 3.89/0.98  fof(f7,axiom,(
% 3.89/0.98    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.89/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f21,plain,(
% 3.89/0.98    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.89/0.98    inference(ennf_transformation,[],[f7])).
% 3.89/0.98  
% 3.89/0.98  fof(f56,plain,(
% 3.89/0.98    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f21])).
% 3.89/0.98  
% 3.89/0.98  fof(f5,axiom,(
% 3.89/0.98    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 3.89/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f20,plain,(
% 3.89/0.98    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.89/0.98    inference(ennf_transformation,[],[f5])).
% 3.89/0.98  
% 3.89/0.98  fof(f53,plain,(
% 3.89/0.98    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f20])).
% 3.89/0.98  
% 3.89/0.98  fof(f10,axiom,(
% 3.89/0.98    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.89/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f60,plain,(
% 3.89/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.89/0.98    inference(cnf_transformation,[],[f10])).
% 3.89/0.98  
% 3.89/0.98  fof(f3,axiom,(
% 3.89/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.89/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f17,plain,(
% 3.89/0.98    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.89/0.98    inference(ennf_transformation,[],[f3])).
% 3.89/0.98  
% 3.89/0.98  fof(f49,plain,(
% 3.89/0.98    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f17])).
% 3.89/0.98  
% 3.89/0.98  fof(f6,axiom,(
% 3.89/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.89/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f54,plain,(
% 3.89/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.89/0.98    inference(cnf_transformation,[],[f6])).
% 3.89/0.98  
% 3.89/0.98  fof(f52,plain,(
% 3.89/0.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f20])).
% 3.89/0.98  
% 3.89/0.98  fof(f11,axiom,(
% 3.89/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0))))),
% 3.89/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f26,plain,(
% 3.89/0.98    ! [X0,X1] : (! [X2] : ((k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.89/0.98    inference(ennf_transformation,[],[f11])).
% 3.89/0.98  
% 3.89/0.98  fof(f27,plain,(
% 3.89/0.98    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.89/0.98    inference(flattening,[],[f26])).
% 3.89/0.98  
% 3.89/0.98  fof(f62,plain,(
% 3.89/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f27])).
% 3.89/0.98  
% 3.89/0.98  fof(f9,axiom,(
% 3.89/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.89/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.98  
% 3.89/0.98  fof(f24,plain,(
% 3.89/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.89/0.98    inference(ennf_transformation,[],[f9])).
% 3.89/0.98  
% 3.89/0.98  fof(f25,plain,(
% 3.89/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.89/0.98    inference(flattening,[],[f24])).
% 3.89/0.98  
% 3.89/0.98  fof(f59,plain,(
% 3.89/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.89/0.98    inference(cnf_transformation,[],[f25])).
% 3.89/0.98  
% 3.89/0.98  fof(f72,plain,(
% 3.89/0.98    k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3 | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3),
% 3.89/0.98    inference(cnf_transformation,[],[f43])).
% 3.89/0.98  
% 3.89/0.98  cnf(c_25,negated_conjecture,
% 3.89/0.98      ( r2_hidden(sK3,k2_relat_1(sK4)) ),
% 3.89/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1021,plain,
% 3.89/0.98      ( r2_hidden(sK3,k2_relat_1(sK4)) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_3,plain,
% 3.89/0.98      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.89/0.98      | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) ),
% 3.89/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1034,plain,
% 3.89/0.98      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.89/0.98      | r2_hidden(k4_tarski(sK2(X1,X0),X0),X1) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_22,plain,
% 3.89/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.89/0.98      | ~ v1_funct_1(X2)
% 3.89/0.98      | ~ v1_relat_1(X2)
% 3.89/0.98      | k1_funct_1(X2,X0) = X1 ),
% 3.89/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1022,plain,
% 3.89/0.98      ( k1_funct_1(X0,X1) = X2
% 3.89/0.98      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 3.89/0.98      | v1_funct_1(X0) != iProver_top
% 3.89/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_2336,plain,
% 3.89/0.98      ( k1_funct_1(X0,sK2(X0,X1)) = X1
% 3.89/0.98      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.89/0.98      | v1_funct_1(X0) != iProver_top
% 3.89/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_1034,c_1022]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_12293,plain,
% 3.89/0.98      ( k1_funct_1(sK4,sK2(sK4,sK3)) = sK3
% 3.89/0.98      | v1_funct_1(sK4) != iProver_top
% 3.89/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_1021,c_2336]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_28,negated_conjecture,
% 3.89/0.98      ( v1_relat_1(sK4) ),
% 3.89/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_27,negated_conjecture,
% 3.89/0.98      ( v1_funct_1(sK4) ),
% 3.89/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1244,plain,
% 3.89/0.98      ( r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4)
% 3.89/0.98      | ~ r2_hidden(sK3,k2_relat_1(sK4)) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1269,plain,
% 3.89/0.98      ( ~ r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4)
% 3.89/0.98      | ~ v1_funct_1(sK4)
% 3.89/0.98      | ~ v1_relat_1(sK4)
% 3.89/0.98      | k1_funct_1(sK4,sK2(sK4,sK3)) = sK3 ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_22]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_12953,plain,
% 3.89/0.98      ( k1_funct_1(sK4,sK2(sK4,sK3)) = sK3 ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_12293,c_28,c_27,c_25,c_1244,c_1269]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_21,plain,
% 3.89/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.89/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.89/0.98      | ~ v1_funct_1(X1)
% 3.89/0.98      | ~ v1_relat_1(X1) ),
% 3.89/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1023,plain,
% 3.89/0.98      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.89/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
% 3.89/0.98      | v1_funct_1(X1) != iProver_top
% 3.89/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_12956,plain,
% 3.89/0.98      ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4)) != iProver_top
% 3.89/0.98      | r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4) = iProver_top
% 3.89/0.98      | v1_funct_1(sK4) != iProver_top
% 3.89/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_12953,c_1023]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_32,plain,
% 3.89/0.98      ( r2_hidden(sK3,k2_relat_1(sK4)) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1245,plain,
% 3.89/0.98      ( r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4) = iProver_top
% 3.89/0.98      | r2_hidden(sK3,k2_relat_1(sK4)) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_1244]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_13362,plain,
% 3.89/0.98      ( r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4) = iProver_top ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_12956,c_32,c_1245]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_7,plain,
% 3.89/0.98      ( r2_hidden(X0,k1_relat_1(X1))
% 3.89/0.98      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.89/0.98      | ~ v1_relat_1(X1) ),
% 3.89/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1031,plain,
% 3.89/0.98      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 3.89/0.98      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 3.89/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_13368,plain,
% 3.89/0.98      ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4)) = iProver_top
% 3.89/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_13362,c_1031]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_29,plain,
% 3.89/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1266,plain,
% 3.89/0.98      ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4))
% 3.89/0.98      | ~ r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4)
% 3.89/0.98      | ~ v1_relat_1(sK4) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1267,plain,
% 3.89/0.98      ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4)) = iProver_top
% 3.89/0.98      | r2_hidden(k4_tarski(sK2(sK4,sK3),sK3),sK4) != iProver_top
% 3.89/0.98      | v1_relat_1(sK4) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_1266]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_13891,plain,
% 3.89/0.98      ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4)) = iProver_top ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_13368,c_29,c_32,c_1245,c_1267]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_20,plain,
% 3.89/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.89/0.98      | ~ v1_funct_1(X1)
% 3.89/0.98      | ~ v2_funct_1(X1)
% 3.89/0.98      | ~ v1_relat_1(X1)
% 3.89/0.98      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
% 3.89/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_26,negated_conjecture,
% 3.89/0.98      ( v2_funct_1(sK4) ),
% 3.89/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_370,plain,
% 3.89/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.89/0.98      | ~ v1_funct_1(X1)
% 3.89/0.98      | ~ v1_relat_1(X1)
% 3.89/0.98      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
% 3.89/0.98      | sK4 != X1 ),
% 3.89/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_371,plain,
% 3.89/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.89/0.98      | ~ v1_funct_1(sK4)
% 3.89/0.98      | ~ v1_relat_1(sK4)
% 3.89/0.98      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
% 3.89/0.98      inference(unflattening,[status(thm)],[c_370]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_375,plain,
% 3.89/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.89/0.98      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_371,c_28,c_27]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1015,plain,
% 3.89/0.98      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
% 3.89/0.98      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_13,plain,
% 3.89/0.98      ( ~ v1_funct_1(X0)
% 3.89/0.98      | ~ v2_funct_1(X0)
% 3.89/0.98      | ~ v1_relat_1(X0)
% 3.89/0.98      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.89/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_322,plain,
% 3.89/0.98      ( ~ v1_funct_1(X0)
% 3.89/0.98      | ~ v1_relat_1(X0)
% 3.89/0.98      | k2_funct_1(X0) = k4_relat_1(X0)
% 3.89/0.98      | sK4 != X0 ),
% 3.89/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_323,plain,
% 3.89/0.98      ( ~ v1_funct_1(sK4)
% 3.89/0.98      | ~ v1_relat_1(sK4)
% 3.89/0.98      | k2_funct_1(sK4) = k4_relat_1(sK4) ),
% 3.89/0.98      inference(unflattening,[status(thm)],[c_322]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_64,plain,
% 3.89/0.98      ( ~ v1_funct_1(sK4)
% 3.89/0.98      | ~ v2_funct_1(sK4)
% 3.89/0.98      | ~ v1_relat_1(sK4)
% 3.89/0.98      | k2_funct_1(sK4) = k4_relat_1(sK4) ),
% 3.89/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_325,plain,
% 3.89/0.98      ( k2_funct_1(sK4) = k4_relat_1(sK4) ),
% 3.89/0.98      inference(global_propositional_subsumption,
% 3.89/0.98                [status(thm)],
% 3.89/0.98                [c_323,c_28,c_27,c_26,c_64]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1081,plain,
% 3.89/0.98      ( k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,X0)) = X0
% 3.89/0.98      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.89/0.98      inference(light_normalisation,[status(thm)],[c_1015,c_325]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_13898,plain,
% 3.89/0.98      ( k1_funct_1(k4_relat_1(sK4),k1_funct_1(sK4,sK2(sK4,sK3))) = sK2(sK4,sK3) ),
% 3.89/0.98      inference(superposition,[status(thm)],[c_13891,c_1081]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_13923,plain,
% 3.89/0.98      ( k1_funct_1(k4_relat_1(sK4),sK3) = sK2(sK4,sK3) ),
% 3.89/0.98      inference(light_normalisation,[status(thm)],[c_13898,c_12953]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1019,plain,
% 3.89/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_4,plain,
% 3.89/0.98      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 3.89/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_1033,plain,
% 3.89/0.98      ( v1_relat_1(X0) != iProver_top
% 3.89/0.98      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 3.89/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.89/0.98  
% 3.89/0.98  cnf(c_12,plain,
% 3.89/0.98      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ),
% 3.89/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1028,plain,
% 3.89/0.99      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 3.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1908,plain,
% 3.89/0.99      ( k5_relat_1(k4_relat_1(X0),k6_relat_1(k2_relat_1(k4_relat_1(X0)))) = k4_relat_1(X0)
% 3.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1033,c_1028]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_7382,plain,
% 3.89/0.99      ( k5_relat_1(k4_relat_1(sK4),k6_relat_1(k2_relat_1(k4_relat_1(sK4)))) = k4_relat_1(sK4) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1019,c_1908]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_8,plain,
% 3.89/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 3.89/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1030,plain,
% 3.89/0.99      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 3.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1803,plain,
% 3.89/0.99      ( k2_relat_1(k4_relat_1(sK4)) = k1_relat_1(sK4) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1019,c_1030]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_7384,plain,
% 3.89/0.99      ( k5_relat_1(k4_relat_1(sK4),k6_relat_1(k1_relat_1(sK4))) = k4_relat_1(sK4) ),
% 3.89/0.99      inference(light_normalisation,[status(thm)],[c_7382,c_1803]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_17,plain,
% 3.89/0.99      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.89/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1025,plain,
% 3.89/0.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_5,plain,
% 3.89/0.99      ( ~ v1_relat_1(X0)
% 3.89/0.99      | ~ v1_relat_1(X1)
% 3.89/0.99      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 3.89/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1032,plain,
% 3.89/0.99      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 3.89/0.99      | v1_relat_1(X1) != iProver_top
% 3.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3256,plain,
% 3.89/0.99      ( k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k5_relat_1(X0,k6_relat_1(X1)))
% 3.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1025,c_1032]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_11,plain,
% 3.89/0.99      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.89/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3264,plain,
% 3.89/0.99      ( k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,X1)
% 3.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.99      inference(demodulation,[status(thm)],[c_3256,c_11]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3294,plain,
% 3.89/0.99      ( k1_relat_1(k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k4_relat_1(X0),X1)
% 3.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1033,c_3264]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_8403,plain,
% 3.89/0.99      ( k1_relat_1(k5_relat_1(k4_relat_1(sK4),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK4),X0) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1019,c_3294]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_8551,plain,
% 3.89/0.99      ( k10_relat_1(k4_relat_1(sK4),k1_relat_1(sK4)) = k1_relat_1(k4_relat_1(sK4)) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_7384,c_8403]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_9,plain,
% 3.89/0.99      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 3.89/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1029,plain,
% 3.89/0.99      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 3.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1635,plain,
% 3.89/0.99      ( k1_relat_1(k4_relat_1(sK4)) = k2_relat_1(sK4) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1019,c_1029]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3257,plain,
% 3.89/0.99      ( k10_relat_1(X0,k1_relat_1(sK4)) = k1_relat_1(k5_relat_1(X0,sK4))
% 3.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1019,c_1032]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3659,plain,
% 3.89/0.99      ( k10_relat_1(k4_relat_1(X0),k1_relat_1(sK4)) = k1_relat_1(k5_relat_1(k4_relat_1(X0),sK4))
% 3.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1033,c_3257]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3774,plain,
% 3.89/0.99      ( k10_relat_1(k4_relat_1(sK4),k1_relat_1(sK4)) = k1_relat_1(k5_relat_1(k4_relat_1(sK4),sK4)) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1019,c_3659]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_8566,plain,
% 3.89/0.99      ( k10_relat_1(k4_relat_1(sK4),k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 3.89/0.99      inference(light_normalisation,[status(thm)],[c_8551,c_1635,c_3774]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_8781,plain,
% 3.89/0.99      ( k1_relat_1(k5_relat_1(k4_relat_1(sK4),sK4)) = k2_relat_1(sK4) ),
% 3.89/0.99      inference(demodulation,[status(thm)],[c_8566,c_3774]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_18,plain,
% 3.89/0.99      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 3.89/0.99      | ~ v1_funct_1(X1)
% 3.89/0.99      | ~ v1_funct_1(X2)
% 3.89/0.99      | ~ v1_relat_1(X2)
% 3.89/0.99      | ~ v1_relat_1(X1)
% 3.89/0.99      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 3.89/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1024,plain,
% 3.89/0.99      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 3.89/0.99      | r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
% 3.89/0.99      | v1_funct_1(X0) != iProver_top
% 3.89/0.99      | v1_funct_1(X1) != iProver_top
% 3.89/0.99      | v1_relat_1(X0) != iProver_top
% 3.89/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_9004,plain,
% 3.89/0.99      ( k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),X0)) = k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),X0)
% 3.89/0.99      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 3.89/0.99      | v1_funct_1(k4_relat_1(sK4)) != iProver_top
% 3.89/0.99      | v1_funct_1(sK4) != iProver_top
% 3.89/0.99      | v1_relat_1(k4_relat_1(sK4)) != iProver_top
% 3.89/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_8781,c_1024]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_30,plain,
% 3.89/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_86,plain,
% 3.89/0.99      ( v1_relat_1(X0) != iProver_top
% 3.89/0.99      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_88,plain,
% 3.89/0.99      ( v1_relat_1(k4_relat_1(sK4)) = iProver_top
% 3.89/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.89/0.99      inference(instantiation,[status(thm)],[c_86]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_14,plain,
% 3.89/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.89/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1027,plain,
% 3.89/0.99      ( v1_funct_1(X0) != iProver_top
% 3.89/0.99      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.89/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_2330,plain,
% 3.89/0.99      ( v1_funct_1(k4_relat_1(sK4)) = iProver_top
% 3.89/0.99      | v1_funct_1(sK4) != iProver_top
% 3.89/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_325,c_1027]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_10473,plain,
% 3.89/0.99      ( k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),X0)) = k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),X0)
% 3.89/0.99      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 3.89/0.99      inference(global_propositional_subsumption,
% 3.89/0.99                [status(thm)],
% 3.89/0.99                [c_9004,c_29,c_30,c_88,c_2330]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_10484,plain,
% 3.89/0.99      ( k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),sK3)) = k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),sK3) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1021,c_10473]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_24,negated_conjecture,
% 3.89/0.99      ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
% 3.89/0.99      | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
% 3.89/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1102,plain,
% 3.89/0.99      ( k1_funct_1(k5_relat_1(k4_relat_1(sK4),sK4),sK3) != sK3
% 3.89/0.99      | k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),sK3)) != sK3 ),
% 3.89/0.99      inference(light_normalisation,[status(thm)],[c_24,c_325]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_10600,plain,
% 3.89/0.99      ( k1_funct_1(sK4,k1_funct_1(k4_relat_1(sK4),sK3)) != sK3 ),
% 3.89/0.99      inference(demodulation,[status(thm)],[c_10484,c_1102]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_14214,plain,
% 3.89/0.99      ( k1_funct_1(sK4,sK2(sK4,sK3)) != sK3 ),
% 3.89/0.99      inference(demodulation,[status(thm)],[c_13923,c_10600]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_14225,plain,
% 3.89/0.99      ( sK3 != sK3 ),
% 3.89/0.99      inference(light_normalisation,[status(thm)],[c_14214,c_12953]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_14226,plain,
% 3.89/0.99      ( $false ),
% 3.89/0.99      inference(equality_resolution_simp,[status(thm)],[c_14225]) ).
% 3.89/0.99  
% 3.89/0.99  
% 3.89/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.89/0.99  
% 3.89/0.99  ------                               Statistics
% 3.89/0.99  
% 3.89/0.99  ------ General
% 3.89/0.99  
% 3.89/0.99  abstr_ref_over_cycles:                  0
% 3.89/0.99  abstr_ref_under_cycles:                 0
% 3.89/0.99  gc_basic_clause_elim:                   0
% 3.89/0.99  forced_gc_time:                         0
% 3.89/0.99  parsing_time:                           0.012
% 3.89/0.99  unif_index_cands_time:                  0.
% 3.89/0.99  unif_index_add_time:                    0.
% 3.89/0.99  orderings_time:                         0.
% 3.89/0.99  out_proof_time:                         0.012
% 3.89/0.99  total_time:                             0.442
% 3.89/0.99  num_of_symbols:                         49
% 3.89/0.99  num_of_terms:                           16008
% 3.89/0.99  
% 3.89/0.99  ------ Preprocessing
% 3.89/0.99  
% 3.89/0.99  num_of_splits:                          0
% 3.89/0.99  num_of_split_atoms:                     0
% 3.89/0.99  num_of_reused_defs:                     0
% 3.89/0.99  num_eq_ax_congr_red:                    22
% 3.89/0.99  num_of_sem_filtered_clauses:            1
% 3.89/0.99  num_of_subtypes:                        0
% 3.89/0.99  monotx_restored_types:                  0
% 3.89/0.99  sat_num_of_epr_types:                   0
% 3.89/0.99  sat_num_of_non_cyclic_types:            0
% 3.89/0.99  sat_guarded_non_collapsed_types:        0
% 3.89/0.99  num_pure_diseq_elim:                    0
% 3.89/0.99  simp_replaced_by:                       0
% 3.89/0.99  res_preprocessed:                       140
% 3.89/0.99  prep_upred:                             0
% 3.89/0.99  prep_unflattend:                        6
% 3.89/0.99  smt_new_axioms:                         0
% 3.89/0.99  pred_elim_cands:                        3
% 3.89/0.99  pred_elim:                              1
% 3.89/0.99  pred_elim_cl:                           -1
% 3.89/0.99  pred_elim_cycles:                       3
% 3.89/0.99  merged_defs:                            0
% 3.89/0.99  merged_defs_ncl:                        0
% 3.89/0.99  bin_hyper_res:                          0
% 3.89/0.99  prep_cycles:                            4
% 3.89/0.99  pred_elim_time:                         0.003
% 3.89/0.99  splitting_time:                         0.
% 3.89/0.99  sem_filter_time:                        0.
% 3.89/0.99  monotx_time:                            0.
% 3.89/0.99  subtype_inf_time:                       0.
% 3.89/0.99  
% 3.89/0.99  ------ Problem properties
% 3.89/0.99  
% 3.89/0.99  clauses:                                28
% 3.89/0.99  conjectures:                            4
% 3.89/0.99  epr:                                    2
% 3.89/0.99  horn:                                   27
% 3.89/0.99  ground:                                 5
% 3.89/0.99  unary:                                  7
% 3.89/0.99  binary:                                 10
% 3.89/0.99  lits:                                   65
% 3.89/0.99  lits_eq:                                18
% 3.89/0.99  fd_pure:                                0
% 3.89/0.99  fd_pseudo:                              0
% 3.89/0.99  fd_cond:                                0
% 3.89/0.99  fd_pseudo_cond:                         3
% 3.89/0.99  ac_symbols:                             0
% 3.89/0.99  
% 3.89/0.99  ------ Propositional Solver
% 3.89/0.99  
% 3.89/0.99  prop_solver_calls:                      28
% 3.89/0.99  prop_fast_solver_calls:                 1114
% 3.89/0.99  smt_solver_calls:                       0
% 3.89/0.99  smt_fast_solver_calls:                  0
% 3.89/0.99  prop_num_of_clauses:                    5830
% 3.89/0.99  prop_preprocess_simplified:             13488
% 3.89/0.99  prop_fo_subsumed:                       48
% 3.89/0.99  prop_solver_time:                       0.
% 3.89/0.99  smt_solver_time:                        0.
% 3.89/0.99  smt_fast_solver_time:                   0.
% 3.89/0.99  prop_fast_solver_time:                  0.
% 3.89/0.99  prop_unsat_core_time:                   0.
% 3.89/0.99  
% 3.89/0.99  ------ QBF
% 3.89/0.99  
% 3.89/0.99  qbf_q_res:                              0
% 3.89/0.99  qbf_num_tautologies:                    0
% 3.89/0.99  qbf_prep_cycles:                        0
% 3.89/0.99  
% 3.89/0.99  ------ BMC1
% 3.89/0.99  
% 3.89/0.99  bmc1_current_bound:                     -1
% 3.89/0.99  bmc1_last_solved_bound:                 -1
% 3.89/0.99  bmc1_unsat_core_size:                   -1
% 3.89/0.99  bmc1_unsat_core_parents_size:           -1
% 3.89/0.99  bmc1_merge_next_fun:                    0
% 3.89/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.89/0.99  
% 3.89/0.99  ------ Instantiation
% 3.89/0.99  
% 3.89/0.99  inst_num_of_clauses:                    1810
% 3.89/0.99  inst_num_in_passive:                    857
% 3.89/0.99  inst_num_in_active:                     645
% 3.89/0.99  inst_num_in_unprocessed:                308
% 3.89/0.99  inst_num_of_loops:                      720
% 3.89/0.99  inst_num_of_learning_restarts:          0
% 3.89/0.99  inst_num_moves_active_passive:          72
% 3.89/0.99  inst_lit_activity:                      0
% 3.89/0.99  inst_lit_activity_moves:                0
% 3.89/0.99  inst_num_tautologies:                   0
% 3.89/0.99  inst_num_prop_implied:                  0
% 3.89/0.99  inst_num_existing_simplified:           0
% 3.89/0.99  inst_num_eq_res_simplified:             0
% 3.89/0.99  inst_num_child_elim:                    0
% 3.89/0.99  inst_num_of_dismatching_blockings:      646
% 3.89/0.99  inst_num_of_non_proper_insts:           1543
% 3.89/0.99  inst_num_of_duplicates:                 0
% 3.89/0.99  inst_inst_num_from_inst_to_res:         0
% 3.89/0.99  inst_dismatching_checking_time:         0.
% 3.89/0.99  
% 3.89/0.99  ------ Resolution
% 3.89/0.99  
% 3.89/0.99  res_num_of_clauses:                     0
% 3.89/0.99  res_num_in_passive:                     0
% 3.89/0.99  res_num_in_active:                      0
% 3.89/0.99  res_num_of_loops:                       144
% 3.89/0.99  res_forward_subset_subsumed:            90
% 3.89/0.99  res_backward_subset_subsumed:           0
% 3.89/0.99  res_forward_subsumed:                   0
% 3.89/0.99  res_backward_subsumed:                  0
% 3.89/0.99  res_forward_subsumption_resolution:     2
% 3.89/0.99  res_backward_subsumption_resolution:    0
% 3.89/0.99  res_clause_to_clause_subsumption:       1118
% 3.89/0.99  res_orphan_elimination:                 0
% 3.89/0.99  res_tautology_del:                      84
% 3.89/0.99  res_num_eq_res_simplified:              0
% 3.89/0.99  res_num_sel_changes:                    0
% 3.89/0.99  res_moves_from_active_to_pass:          0
% 3.89/0.99  
% 3.89/0.99  ------ Superposition
% 3.89/0.99  
% 3.89/0.99  sup_time_total:                         0.
% 3.89/0.99  sup_time_generating:                    0.
% 3.89/0.99  sup_time_sim_full:                      0.
% 3.89/0.99  sup_time_sim_immed:                     0.
% 3.89/0.99  
% 3.89/0.99  sup_num_of_clauses:                     358
% 3.89/0.99  sup_num_in_active:                      137
% 3.89/0.99  sup_num_in_passive:                     221
% 3.89/0.99  sup_num_of_loops:                       143
% 3.89/0.99  sup_fw_superposition:                   247
% 3.89/0.99  sup_bw_superposition:                   120
% 3.89/0.99  sup_immediate_simplified:               61
% 3.89/0.99  sup_given_eliminated:                   0
% 3.89/0.99  comparisons_done:                       0
% 3.89/0.99  comparisons_avoided:                    34
% 3.89/0.99  
% 3.89/0.99  ------ Simplifications
% 3.89/0.99  
% 3.89/0.99  
% 3.89/0.99  sim_fw_subset_subsumed:                 3
% 3.89/0.99  sim_bw_subset_subsumed:                 0
% 3.89/0.99  sim_fw_subsumed:                        2
% 3.89/0.99  sim_bw_subsumed:                        0
% 3.89/0.99  sim_fw_subsumption_res:                 3
% 3.89/0.99  sim_bw_subsumption_res:                 0
% 3.89/0.99  sim_tautology_del:                      5
% 3.89/0.99  sim_eq_tautology_del:                   11
% 3.89/0.99  sim_eq_res_simp:                        0
% 3.89/0.99  sim_fw_demodulated:                     1
% 3.89/0.99  sim_bw_demodulated:                     6
% 3.89/0.99  sim_light_normalised:                   63
% 3.89/0.99  sim_joinable_taut:                      0
% 3.89/0.99  sim_joinable_simp:                      0
% 3.89/0.99  sim_ac_normalised:                      0
% 3.89/0.99  sim_smt_subsumption:                    0
% 3.89/0.99  
%------------------------------------------------------------------------------
