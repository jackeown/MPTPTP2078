%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:18 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 431 expanded)
%              Number of clauses        :   58 ( 101 expanded)
%              Number of leaves         :   11 ( 114 expanded)
%              Depth                    :   25
%              Number of atoms          :  483 (3548 expanded)
%              Number of equality atoms :  248 (1578 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f32,plain,(
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
     => ( k6_relat_1(X0) != sK5
        & k5_relat_1(sK5,X1) = X1
        & v2_funct_1(X1)
        & r1_tarski(k2_relat_1(sK5),X0)
        & k1_relat_1(sK5) = X0
        & k1_relat_1(X1) = X0
        & v1_funct_1(sK5)
        & v1_relat_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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
          ( k6_relat_1(sK3) != X2
          & k5_relat_1(X2,sK4) = sK4
          & v2_funct_1(sK4)
          & r1_tarski(k2_relat_1(X2),sK3)
          & k1_relat_1(X2) = sK3
          & k1_relat_1(sK4) = sK3
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k6_relat_1(sK3) != sK5
    & k5_relat_1(sK5,sK4) = sK4
    & v2_funct_1(sK4)
    & r1_tarski(k2_relat_1(sK5),sK3)
    & k1_relat_1(sK5) = sK3
    & k1_relat_1(sK4) = sK3
    & v1_funct_1(sK5)
    & v1_relat_1(sK5)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f32,f31])).

fof(f54,plain,(
    r1_tarski(k2_relat_1(sK5),sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    k1_relat_1(sK5) = sK3 ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK2(X0,X1)) != sK2(X0,X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK2(X0,X1)) != sK2(X0,X1)
            & r2_hidden(sK2(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f43])).

fof(f57,plain,(
    k6_relat_1(sK3) != sK5 ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    k5_relat_1(sK5,sK4) = sK4 ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK0(X0) != sK1(X0)
        & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0))
        & r2_hidden(sK0(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK0(X0) != sK1(X0)
            & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0))
            & r2_hidden(sK0(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f35,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    k1_relat_1(sK4) = sK3 ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | k1_funct_1(X1,sK2(X0,X1)) != sK2(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k1_funct_1(X1,sK2(k1_relat_1(X1),X1)) != sK2(k1_relat_1(X1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f44])).

cnf(c_0,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK5),sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_218,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0
    | k2_relat_1(X0) != k2_relat_1(sK5)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_219,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(sK3)) = X0
    | k2_relat_1(X0) != k2_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_1023,plain,
    ( k5_relat_1(X0,k6_relat_1(sK3)) = X0
    | k2_relat_1(X0) != k2_relat_1(sK5)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_1327,plain,
    ( k5_relat_1(sK5,k6_relat_1(sK3)) = sK5
    | v1_relat_1(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1023])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_681,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1224,plain,
    ( k2_relat_1(sK5) = k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_1225,plain,
    ( ~ v1_relat_1(sK5)
    | k5_relat_1(sK5,k6_relat_1(sK3)) = sK5
    | k2_relat_1(sK5) != k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_219])).

cnf(c_1545,plain,
    ( k5_relat_1(sK5,k6_relat_1(sK3)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1327,c_21,c_1224,c_1225])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1030,plain,
    ( r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1733,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_1030])).

cnf(c_18,negated_conjecture,
    ( k1_relat_1(sK5) = sK3 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1738,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1733,c_18])).

cnf(c_26,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_27,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1762,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1738,c_26,c_27])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1025,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8,plain,
    ( r2_hidden(sK2(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1034,plain,
    ( k6_relat_1(k1_relat_1(X0)) = X0
    | r2_hidden(sK2(k1_relat_1(X0),X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2131,plain,
    ( k6_relat_1(k1_relat_1(sK5)) = sK5
    | r2_hidden(sK2(sK3,sK5),sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_1034])).

cnf(c_2185,plain,
    ( k6_relat_1(sK3) = sK5
    | r2_hidden(sK2(sK3,sK5),sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2131,c_18])).

cnf(c_14,negated_conjecture,
    ( k6_relat_1(sK3) != sK5 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2294,plain,
    ( r2_hidden(sK2(sK3,sK5),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2185,c_26,c_27,c_14])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1036,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2859,plain,
    ( k1_funct_1(X0,k1_funct_1(sK5,X1)) = k1_funct_1(k5_relat_1(sK5,X0),X1)
    | r2_hidden(X1,sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_1036])).

cnf(c_3004,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,k1_funct_1(sK5,X1)) = k1_funct_1(k5_relat_1(sK5,X0),X1)
    | r2_hidden(X1,sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2859,c_26,c_27])).

cnf(c_3005,plain,
    ( k1_funct_1(X0,k1_funct_1(sK5,X1)) = k1_funct_1(k5_relat_1(sK5,X0),X1)
    | r2_hidden(X1,sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3004])).

cnf(c_3017,plain,
    ( k1_funct_1(k5_relat_1(sK5,X0),sK2(sK3,sK5)) = k1_funct_1(X0,k1_funct_1(sK5,sK2(sK3,sK5)))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2294,c_3005])).

cnf(c_3199,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK5,sK2(sK3,sK5))) = k1_funct_1(k5_relat_1(sK5,sK4),sK2(sK3,sK5))
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_3017])).

cnf(c_15,negated_conjecture,
    ( k5_relat_1(sK5,sK4) = sK4 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3202,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK5,sK2(sK3,sK5))) = k1_funct_1(sK4,sK2(sK3,sK5))
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3199,c_15])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3212,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK5,sK2(sK3,sK5))) = k1_funct_1(sK4,sK2(sK3,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3202,c_24])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1037,plain,
    ( X0 = X1
    | k1_funct_1(X2,X0) != k1_funct_1(X2,X1)
    | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
    | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3475,plain,
    ( k1_funct_1(sK4,sK2(sK3,sK5)) != k1_funct_1(sK4,X0)
    | k1_funct_1(sK5,sK2(sK3,sK5)) = X0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,sK2(sK3,sK5)),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3212,c_1037])).

cnf(c_19,negated_conjecture,
    ( k1_relat_1(sK4) = sK3 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3529,plain,
    ( k1_funct_1(sK4,sK2(sK3,sK5)) != k1_funct_1(sK4,X0)
    | k1_funct_1(sK5,sK2(sK3,sK5)) = X0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,sK2(sK3,sK5)),sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3475,c_19])).

cnf(c_25,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_29,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3611,plain,
    ( r2_hidden(k1_funct_1(sK5,sK2(sK3,sK5)),sK3) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | k1_funct_1(sK5,sK2(sK3,sK5)) = X0
    | k1_funct_1(sK4,sK2(sK3,sK5)) != k1_funct_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3529,c_24,c_25,c_29])).

cnf(c_3612,plain,
    ( k1_funct_1(sK4,sK2(sK3,sK5)) != k1_funct_1(sK4,X0)
    | k1_funct_1(sK5,sK2(sK3,sK5)) = X0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,sK2(sK3,sK5)),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3611])).

cnf(c_3622,plain,
    ( k1_funct_1(sK5,sK2(sK3,sK5)) = sK2(sK3,sK5)
    | r2_hidden(sK2(sK3,sK5),sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,sK2(sK3,sK5)),sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3612])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK2(k1_relat_1(X0),X0)) != sK2(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1035,plain,
    ( k1_funct_1(X0,sK2(k1_relat_1(X0),X0)) != sK2(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2770,plain,
    ( k1_funct_1(sK5,sK2(sK3,sK5)) != sK2(k1_relat_1(sK5),sK5)
    | k6_relat_1(k1_relat_1(sK5)) = sK5
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_1035])).

cnf(c_2785,plain,
    ( k1_funct_1(sK5,sK2(sK3,sK5)) != sK2(sK3,sK5)
    | k6_relat_1(sK3) = sK5
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2770,c_18])).

cnf(c_3754,plain,
    ( r2_hidden(k1_funct_1(sK5,sK2(sK3,sK5)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3622,c_26,c_27,c_14,c_2185,c_2785])).

cnf(c_3759,plain,
    ( r2_hidden(sK2(sK3,sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_3754])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3759,c_2185,c_14,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 18:03:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.45/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/0.98  
% 2.45/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.45/0.98  
% 2.45/0.98  ------  iProver source info
% 2.45/0.98  
% 2.45/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.45/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.45/0.98  git: non_committed_changes: false
% 2.45/0.98  git: last_make_outside_of_git: false
% 2.45/0.98  
% 2.45/0.98  ------ 
% 2.45/0.98  
% 2.45/0.98  ------ Input Options
% 2.45/0.98  
% 2.45/0.98  --out_options                           all
% 2.45/0.98  --tptp_safe_out                         true
% 2.45/0.98  --problem_path                          ""
% 2.45/0.98  --include_path                          ""
% 2.45/0.98  --clausifier                            res/vclausify_rel
% 2.45/0.98  --clausifier_options                    --mode clausify
% 2.45/0.98  --stdin                                 false
% 2.45/0.98  --stats_out                             all
% 2.45/0.98  
% 2.45/0.98  ------ General Options
% 2.45/0.98  
% 2.45/0.98  --fof                                   false
% 2.45/0.98  --time_out_real                         305.
% 2.45/0.98  --time_out_virtual                      -1.
% 2.45/0.98  --symbol_type_check                     false
% 2.45/0.98  --clausify_out                          false
% 2.45/0.98  --sig_cnt_out                           false
% 2.45/0.98  --trig_cnt_out                          false
% 2.45/0.98  --trig_cnt_out_tolerance                1.
% 2.45/0.98  --trig_cnt_out_sk_spl                   false
% 2.45/0.98  --abstr_cl_out                          false
% 2.45/0.98  
% 2.45/0.98  ------ Global Options
% 2.45/0.98  
% 2.45/0.98  --schedule                              default
% 2.45/0.98  --add_important_lit                     false
% 2.45/0.98  --prop_solver_per_cl                    1000
% 2.45/0.98  --min_unsat_core                        false
% 2.45/0.98  --soft_assumptions                      false
% 2.45/0.98  --soft_lemma_size                       3
% 2.45/0.98  --prop_impl_unit_size                   0
% 2.45/0.98  --prop_impl_unit                        []
% 2.45/0.98  --share_sel_clauses                     true
% 2.45/0.98  --reset_solvers                         false
% 2.45/0.98  --bc_imp_inh                            [conj_cone]
% 2.45/0.98  --conj_cone_tolerance                   3.
% 2.45/0.98  --extra_neg_conj                        none
% 2.45/0.98  --large_theory_mode                     true
% 2.45/0.98  --prolific_symb_bound                   200
% 2.45/0.98  --lt_threshold                          2000
% 2.45/0.98  --clause_weak_htbl                      true
% 2.45/0.98  --gc_record_bc_elim                     false
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing Options
% 2.45/0.98  
% 2.45/0.98  --preprocessing_flag                    true
% 2.45/0.98  --time_out_prep_mult                    0.1
% 2.45/0.98  --splitting_mode                        input
% 2.45/0.98  --splitting_grd                         true
% 2.45/0.98  --splitting_cvd                         false
% 2.45/0.98  --splitting_cvd_svl                     false
% 2.45/0.98  --splitting_nvd                         32
% 2.45/0.98  --sub_typing                            true
% 2.45/0.98  --prep_gs_sim                           true
% 2.45/0.98  --prep_unflatten                        true
% 2.45/0.98  --prep_res_sim                          true
% 2.45/0.98  --prep_upred                            true
% 2.45/0.98  --prep_sem_filter                       exhaustive
% 2.45/0.98  --prep_sem_filter_out                   false
% 2.45/0.98  --pred_elim                             true
% 2.45/0.98  --res_sim_input                         true
% 2.45/0.98  --eq_ax_congr_red                       true
% 2.45/0.98  --pure_diseq_elim                       true
% 2.45/0.98  --brand_transform                       false
% 2.45/0.98  --non_eq_to_eq                          false
% 2.45/0.98  --prep_def_merge                        true
% 2.45/0.98  --prep_def_merge_prop_impl              false
% 2.45/0.98  --prep_def_merge_mbd                    true
% 2.45/0.98  --prep_def_merge_tr_red                 false
% 2.45/0.98  --prep_def_merge_tr_cl                  false
% 2.45/0.98  --smt_preprocessing                     true
% 2.45/0.98  --smt_ac_axioms                         fast
% 2.45/0.98  --preprocessed_out                      false
% 2.45/0.98  --preprocessed_stats                    false
% 2.45/0.98  
% 2.45/0.98  ------ Abstraction refinement Options
% 2.45/0.98  
% 2.45/0.98  --abstr_ref                             []
% 2.45/0.98  --abstr_ref_prep                        false
% 2.45/0.98  --abstr_ref_until_sat                   false
% 2.45/0.98  --abstr_ref_sig_restrict                funpre
% 2.45/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/0.98  --abstr_ref_under                       []
% 2.45/0.98  
% 2.45/0.98  ------ SAT Options
% 2.45/0.98  
% 2.45/0.98  --sat_mode                              false
% 2.45/0.98  --sat_fm_restart_options                ""
% 2.45/0.98  --sat_gr_def                            false
% 2.45/0.98  --sat_epr_types                         true
% 2.45/0.98  --sat_non_cyclic_types                  false
% 2.45/0.98  --sat_finite_models                     false
% 2.45/0.98  --sat_fm_lemmas                         false
% 2.45/0.98  --sat_fm_prep                           false
% 2.45/0.98  --sat_fm_uc_incr                        true
% 2.45/0.98  --sat_out_model                         small
% 2.45/0.98  --sat_out_clauses                       false
% 2.45/0.98  
% 2.45/0.98  ------ QBF Options
% 2.45/0.98  
% 2.45/0.98  --qbf_mode                              false
% 2.45/0.98  --qbf_elim_univ                         false
% 2.45/0.98  --qbf_dom_inst                          none
% 2.45/0.98  --qbf_dom_pre_inst                      false
% 2.45/0.98  --qbf_sk_in                             false
% 2.45/0.98  --qbf_pred_elim                         true
% 2.45/0.98  --qbf_split                             512
% 2.45/0.98  
% 2.45/0.98  ------ BMC1 Options
% 2.45/0.98  
% 2.45/0.98  --bmc1_incremental                      false
% 2.45/0.98  --bmc1_axioms                           reachable_all
% 2.45/0.98  --bmc1_min_bound                        0
% 2.45/0.98  --bmc1_max_bound                        -1
% 2.45/0.98  --bmc1_max_bound_default                -1
% 2.45/0.98  --bmc1_symbol_reachability              true
% 2.45/0.98  --bmc1_property_lemmas                  false
% 2.45/0.98  --bmc1_k_induction                      false
% 2.45/0.98  --bmc1_non_equiv_states                 false
% 2.45/0.98  --bmc1_deadlock                         false
% 2.45/0.98  --bmc1_ucm                              false
% 2.45/0.98  --bmc1_add_unsat_core                   none
% 2.45/0.98  --bmc1_unsat_core_children              false
% 2.45/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/0.98  --bmc1_out_stat                         full
% 2.45/0.98  --bmc1_ground_init                      false
% 2.45/0.98  --bmc1_pre_inst_next_state              false
% 2.45/0.98  --bmc1_pre_inst_state                   false
% 2.45/0.98  --bmc1_pre_inst_reach_state             false
% 2.45/0.98  --bmc1_out_unsat_core                   false
% 2.45/0.98  --bmc1_aig_witness_out                  false
% 2.45/0.98  --bmc1_verbose                          false
% 2.45/0.98  --bmc1_dump_clauses_tptp                false
% 2.45/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.45/0.98  --bmc1_dump_file                        -
% 2.45/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.45/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.45/0.98  --bmc1_ucm_extend_mode                  1
% 2.45/0.98  --bmc1_ucm_init_mode                    2
% 2.45/0.98  --bmc1_ucm_cone_mode                    none
% 2.45/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.45/0.98  --bmc1_ucm_relax_model                  4
% 2.45/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.45/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/0.98  --bmc1_ucm_layered_model                none
% 2.45/0.98  --bmc1_ucm_max_lemma_size               10
% 2.45/0.98  
% 2.45/0.98  ------ AIG Options
% 2.45/0.98  
% 2.45/0.98  --aig_mode                              false
% 2.45/0.98  
% 2.45/0.98  ------ Instantiation Options
% 2.45/0.98  
% 2.45/0.98  --instantiation_flag                    true
% 2.45/0.98  --inst_sos_flag                         false
% 2.45/0.98  --inst_sos_phase                        true
% 2.45/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/0.98  --inst_lit_sel_side                     num_symb
% 2.45/0.98  --inst_solver_per_active                1400
% 2.45/0.98  --inst_solver_calls_frac                1.
% 2.45/0.98  --inst_passive_queue_type               priority_queues
% 2.45/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/0.98  --inst_passive_queues_freq              [25;2]
% 2.45/0.98  --inst_dismatching                      true
% 2.45/0.98  --inst_eager_unprocessed_to_passive     true
% 2.45/0.98  --inst_prop_sim_given                   true
% 2.45/0.98  --inst_prop_sim_new                     false
% 2.45/0.98  --inst_subs_new                         false
% 2.45/0.98  --inst_eq_res_simp                      false
% 2.45/0.98  --inst_subs_given                       false
% 2.45/0.98  --inst_orphan_elimination               true
% 2.45/0.98  --inst_learning_loop_flag               true
% 2.45/0.98  --inst_learning_start                   3000
% 2.45/0.98  --inst_learning_factor                  2
% 2.45/0.98  --inst_start_prop_sim_after_learn       3
% 2.45/0.98  --inst_sel_renew                        solver
% 2.45/0.98  --inst_lit_activity_flag                true
% 2.45/0.98  --inst_restr_to_given                   false
% 2.45/0.98  --inst_activity_threshold               500
% 2.45/0.98  --inst_out_proof                        true
% 2.45/0.98  
% 2.45/0.98  ------ Resolution Options
% 2.45/0.98  
% 2.45/0.98  --resolution_flag                       true
% 2.45/0.98  --res_lit_sel                           adaptive
% 2.45/0.98  --res_lit_sel_side                      none
% 2.45/0.98  --res_ordering                          kbo
% 2.45/0.98  --res_to_prop_solver                    active
% 2.45/0.98  --res_prop_simpl_new                    false
% 2.45/0.98  --res_prop_simpl_given                  true
% 2.45/0.98  --res_passive_queue_type                priority_queues
% 2.45/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/0.98  --res_passive_queues_freq               [15;5]
% 2.45/0.98  --res_forward_subs                      full
% 2.45/0.98  --res_backward_subs                     full
% 2.45/0.98  --res_forward_subs_resolution           true
% 2.45/0.98  --res_backward_subs_resolution          true
% 2.45/0.98  --res_orphan_elimination                true
% 2.45/0.98  --res_time_limit                        2.
% 2.45/0.98  --res_out_proof                         true
% 2.45/0.98  
% 2.45/0.98  ------ Superposition Options
% 2.45/0.98  
% 2.45/0.98  --superposition_flag                    true
% 2.45/0.98  --sup_passive_queue_type                priority_queues
% 2.45/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.45/0.98  --demod_completeness_check              fast
% 2.45/0.98  --demod_use_ground                      true
% 2.45/0.98  --sup_to_prop_solver                    passive
% 2.45/0.98  --sup_prop_simpl_new                    true
% 2.45/0.98  --sup_prop_simpl_given                  true
% 2.45/0.98  --sup_fun_splitting                     false
% 2.45/0.98  --sup_smt_interval                      50000
% 2.45/0.98  
% 2.45/0.98  ------ Superposition Simplification Setup
% 2.45/0.98  
% 2.45/0.98  --sup_indices_passive                   []
% 2.45/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_full_bw                           [BwDemod]
% 2.45/0.98  --sup_immed_triv                        [TrivRules]
% 2.45/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_immed_bw_main                     []
% 2.45/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/0.98  
% 2.45/0.98  ------ Combination Options
% 2.45/0.98  
% 2.45/0.98  --comb_res_mult                         3
% 2.45/0.98  --comb_sup_mult                         2
% 2.45/0.98  --comb_inst_mult                        10
% 2.45/0.98  
% 2.45/0.98  ------ Debug Options
% 2.45/0.98  
% 2.45/0.98  --dbg_backtrace                         false
% 2.45/0.98  --dbg_dump_prop_clauses                 false
% 2.45/0.98  --dbg_dump_prop_clauses_file            -
% 2.45/0.98  --dbg_out_stat                          false
% 2.45/0.98  ------ Parsing...
% 2.45/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.45/0.98  ------ Proving...
% 2.45/0.98  ------ Problem Properties 
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  clauses                                 23
% 2.45/0.98  conjectures                             9
% 2.45/0.98  EPR                                     5
% 2.45/0.98  Horn                                    19
% 2.45/0.98  unary                                   9
% 2.45/0.98  binary                                  0
% 2.45/0.98  lits                                    69
% 2.45/0.98  lits eq                                 16
% 2.45/0.98  fd_pure                                 0
% 2.45/0.98  fd_pseudo                               0
% 2.45/0.98  fd_cond                                 0
% 2.45/0.98  fd_pseudo_cond                          1
% 2.45/0.98  AC symbols                              0
% 2.45/0.98  
% 2.45/0.98  ------ Schedule dynamic 5 is on 
% 2.45/0.98  
% 2.45/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  ------ 
% 2.45/0.98  Current options:
% 2.45/0.98  ------ 
% 2.45/0.98  
% 2.45/0.98  ------ Input Options
% 2.45/0.98  
% 2.45/0.98  --out_options                           all
% 2.45/0.98  --tptp_safe_out                         true
% 2.45/0.98  --problem_path                          ""
% 2.45/0.98  --include_path                          ""
% 2.45/0.98  --clausifier                            res/vclausify_rel
% 2.45/0.98  --clausifier_options                    --mode clausify
% 2.45/0.98  --stdin                                 false
% 2.45/0.98  --stats_out                             all
% 2.45/0.98  
% 2.45/0.98  ------ General Options
% 2.45/0.98  
% 2.45/0.98  --fof                                   false
% 2.45/0.98  --time_out_real                         305.
% 2.45/0.98  --time_out_virtual                      -1.
% 2.45/0.98  --symbol_type_check                     false
% 2.45/0.98  --clausify_out                          false
% 2.45/0.98  --sig_cnt_out                           false
% 2.45/0.98  --trig_cnt_out                          false
% 2.45/0.98  --trig_cnt_out_tolerance                1.
% 2.45/0.98  --trig_cnt_out_sk_spl                   false
% 2.45/0.98  --abstr_cl_out                          false
% 2.45/0.98  
% 2.45/0.98  ------ Global Options
% 2.45/0.98  
% 2.45/0.98  --schedule                              default
% 2.45/0.98  --add_important_lit                     false
% 2.45/0.98  --prop_solver_per_cl                    1000
% 2.45/0.98  --min_unsat_core                        false
% 2.45/0.98  --soft_assumptions                      false
% 2.45/0.98  --soft_lemma_size                       3
% 2.45/0.98  --prop_impl_unit_size                   0
% 2.45/0.98  --prop_impl_unit                        []
% 2.45/0.98  --share_sel_clauses                     true
% 2.45/0.98  --reset_solvers                         false
% 2.45/0.98  --bc_imp_inh                            [conj_cone]
% 2.45/0.98  --conj_cone_tolerance                   3.
% 2.45/0.98  --extra_neg_conj                        none
% 2.45/0.98  --large_theory_mode                     true
% 2.45/0.98  --prolific_symb_bound                   200
% 2.45/0.98  --lt_threshold                          2000
% 2.45/0.98  --clause_weak_htbl                      true
% 2.45/0.98  --gc_record_bc_elim                     false
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing Options
% 2.45/0.98  
% 2.45/0.98  --preprocessing_flag                    true
% 2.45/0.98  --time_out_prep_mult                    0.1
% 2.45/0.98  --splitting_mode                        input
% 2.45/0.98  --splitting_grd                         true
% 2.45/0.98  --splitting_cvd                         false
% 2.45/0.98  --splitting_cvd_svl                     false
% 2.45/0.98  --splitting_nvd                         32
% 2.45/0.98  --sub_typing                            true
% 2.45/0.98  --prep_gs_sim                           true
% 2.45/0.98  --prep_unflatten                        true
% 2.45/0.98  --prep_res_sim                          true
% 2.45/0.98  --prep_upred                            true
% 2.45/0.98  --prep_sem_filter                       exhaustive
% 2.45/0.98  --prep_sem_filter_out                   false
% 2.45/0.98  --pred_elim                             true
% 2.45/0.98  --res_sim_input                         true
% 2.45/0.98  --eq_ax_congr_red                       true
% 2.45/0.98  --pure_diseq_elim                       true
% 2.45/0.98  --brand_transform                       false
% 2.45/0.98  --non_eq_to_eq                          false
% 2.45/0.98  --prep_def_merge                        true
% 2.45/0.98  --prep_def_merge_prop_impl              false
% 2.45/0.98  --prep_def_merge_mbd                    true
% 2.45/0.98  --prep_def_merge_tr_red                 false
% 2.45/0.98  --prep_def_merge_tr_cl                  false
% 2.45/0.98  --smt_preprocessing                     true
% 2.45/0.98  --smt_ac_axioms                         fast
% 2.45/0.98  --preprocessed_out                      false
% 2.45/0.98  --preprocessed_stats                    false
% 2.45/0.98  
% 2.45/0.98  ------ Abstraction refinement Options
% 2.45/0.98  
% 2.45/0.98  --abstr_ref                             []
% 2.45/0.98  --abstr_ref_prep                        false
% 2.45/0.98  --abstr_ref_until_sat                   false
% 2.45/0.98  --abstr_ref_sig_restrict                funpre
% 2.45/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/0.98  --abstr_ref_under                       []
% 2.45/0.98  
% 2.45/0.98  ------ SAT Options
% 2.45/0.98  
% 2.45/0.98  --sat_mode                              false
% 2.45/0.98  --sat_fm_restart_options                ""
% 2.45/0.98  --sat_gr_def                            false
% 2.45/0.98  --sat_epr_types                         true
% 2.45/0.98  --sat_non_cyclic_types                  false
% 2.45/0.98  --sat_finite_models                     false
% 2.45/0.98  --sat_fm_lemmas                         false
% 2.45/0.98  --sat_fm_prep                           false
% 2.45/0.98  --sat_fm_uc_incr                        true
% 2.45/0.98  --sat_out_model                         small
% 2.45/0.98  --sat_out_clauses                       false
% 2.45/0.98  
% 2.45/0.98  ------ QBF Options
% 2.45/0.98  
% 2.45/0.98  --qbf_mode                              false
% 2.45/0.98  --qbf_elim_univ                         false
% 2.45/0.98  --qbf_dom_inst                          none
% 2.45/0.98  --qbf_dom_pre_inst                      false
% 2.45/0.98  --qbf_sk_in                             false
% 2.45/0.98  --qbf_pred_elim                         true
% 2.45/0.98  --qbf_split                             512
% 2.45/0.98  
% 2.45/0.98  ------ BMC1 Options
% 2.45/0.98  
% 2.45/0.98  --bmc1_incremental                      false
% 2.45/0.98  --bmc1_axioms                           reachable_all
% 2.45/0.98  --bmc1_min_bound                        0
% 2.45/0.98  --bmc1_max_bound                        -1
% 2.45/0.98  --bmc1_max_bound_default                -1
% 2.45/0.98  --bmc1_symbol_reachability              true
% 2.45/0.98  --bmc1_property_lemmas                  false
% 2.45/0.98  --bmc1_k_induction                      false
% 2.45/0.98  --bmc1_non_equiv_states                 false
% 2.45/0.98  --bmc1_deadlock                         false
% 2.45/0.98  --bmc1_ucm                              false
% 2.45/0.98  --bmc1_add_unsat_core                   none
% 2.45/0.98  --bmc1_unsat_core_children              false
% 2.45/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/0.98  --bmc1_out_stat                         full
% 2.45/0.98  --bmc1_ground_init                      false
% 2.45/0.98  --bmc1_pre_inst_next_state              false
% 2.45/0.98  --bmc1_pre_inst_state                   false
% 2.45/0.98  --bmc1_pre_inst_reach_state             false
% 2.45/0.98  --bmc1_out_unsat_core                   false
% 2.45/0.98  --bmc1_aig_witness_out                  false
% 2.45/0.98  --bmc1_verbose                          false
% 2.45/0.98  --bmc1_dump_clauses_tptp                false
% 2.45/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.45/0.98  --bmc1_dump_file                        -
% 2.45/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.45/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.45/0.98  --bmc1_ucm_extend_mode                  1
% 2.45/0.98  --bmc1_ucm_init_mode                    2
% 2.45/0.98  --bmc1_ucm_cone_mode                    none
% 2.45/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.45/0.98  --bmc1_ucm_relax_model                  4
% 2.45/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.45/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/0.98  --bmc1_ucm_layered_model                none
% 2.45/0.98  --bmc1_ucm_max_lemma_size               10
% 2.45/0.98  
% 2.45/0.98  ------ AIG Options
% 2.45/0.98  
% 2.45/0.98  --aig_mode                              false
% 2.45/0.98  
% 2.45/0.98  ------ Instantiation Options
% 2.45/0.98  
% 2.45/0.98  --instantiation_flag                    true
% 2.45/0.98  --inst_sos_flag                         false
% 2.45/0.98  --inst_sos_phase                        true
% 2.45/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/0.98  --inst_lit_sel_side                     none
% 2.45/0.98  --inst_solver_per_active                1400
% 2.45/0.98  --inst_solver_calls_frac                1.
% 2.45/0.98  --inst_passive_queue_type               priority_queues
% 2.45/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/0.98  --inst_passive_queues_freq              [25;2]
% 2.45/0.98  --inst_dismatching                      true
% 2.45/0.98  --inst_eager_unprocessed_to_passive     true
% 2.45/0.98  --inst_prop_sim_given                   true
% 2.45/0.98  --inst_prop_sim_new                     false
% 2.45/0.98  --inst_subs_new                         false
% 2.45/0.98  --inst_eq_res_simp                      false
% 2.45/0.98  --inst_subs_given                       false
% 2.45/0.98  --inst_orphan_elimination               true
% 2.45/0.98  --inst_learning_loop_flag               true
% 2.45/0.98  --inst_learning_start                   3000
% 2.45/0.98  --inst_learning_factor                  2
% 2.45/0.98  --inst_start_prop_sim_after_learn       3
% 2.45/0.98  --inst_sel_renew                        solver
% 2.45/0.98  --inst_lit_activity_flag                true
% 2.45/0.98  --inst_restr_to_given                   false
% 2.45/0.98  --inst_activity_threshold               500
% 2.45/0.98  --inst_out_proof                        true
% 2.45/0.98  
% 2.45/0.98  ------ Resolution Options
% 2.45/0.98  
% 2.45/0.98  --resolution_flag                       false
% 2.45/0.98  --res_lit_sel                           adaptive
% 2.45/0.98  --res_lit_sel_side                      none
% 2.45/0.98  --res_ordering                          kbo
% 2.45/0.98  --res_to_prop_solver                    active
% 2.45/0.98  --res_prop_simpl_new                    false
% 2.45/0.98  --res_prop_simpl_given                  true
% 2.45/0.98  --res_passive_queue_type                priority_queues
% 2.45/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/0.98  --res_passive_queues_freq               [15;5]
% 2.45/0.98  --res_forward_subs                      full
% 2.45/0.98  --res_backward_subs                     full
% 2.45/0.98  --res_forward_subs_resolution           true
% 2.45/0.98  --res_backward_subs_resolution          true
% 2.45/0.98  --res_orphan_elimination                true
% 2.45/0.98  --res_time_limit                        2.
% 2.45/0.98  --res_out_proof                         true
% 2.45/0.98  
% 2.45/0.98  ------ Superposition Options
% 2.45/0.98  
% 2.45/0.98  --superposition_flag                    true
% 2.45/0.98  --sup_passive_queue_type                priority_queues
% 2.45/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.45/0.98  --demod_completeness_check              fast
% 2.45/0.98  --demod_use_ground                      true
% 2.45/0.98  --sup_to_prop_solver                    passive
% 2.45/0.98  --sup_prop_simpl_new                    true
% 2.45/0.98  --sup_prop_simpl_given                  true
% 2.45/0.98  --sup_fun_splitting                     false
% 2.45/0.98  --sup_smt_interval                      50000
% 2.45/0.98  
% 2.45/0.98  ------ Superposition Simplification Setup
% 2.45/0.98  
% 2.45/0.98  --sup_indices_passive                   []
% 2.45/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_full_bw                           [BwDemod]
% 2.45/0.98  --sup_immed_triv                        [TrivRules]
% 2.45/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_immed_bw_main                     []
% 2.45/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/0.98  
% 2.45/0.98  ------ Combination Options
% 2.45/0.98  
% 2.45/0.98  --comb_res_mult                         3
% 2.45/0.98  --comb_sup_mult                         2
% 2.45/0.98  --comb_inst_mult                        10
% 2.45/0.98  
% 2.45/0.98  ------ Debug Options
% 2.45/0.98  
% 2.45/0.98  --dbg_backtrace                         false
% 2.45/0.98  --dbg_dump_prop_clauses                 false
% 2.45/0.98  --dbg_dump_prop_clauses_file            -
% 2.45/0.98  --dbg_out_stat                          false
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  ------ Proving...
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  % SZS status Theorem for theBenchmark.p
% 2.45/0.98  
% 2.45/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.45/0.98  
% 2.45/0.98  fof(f1,axiom,(
% 2.45/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f8,plain,(
% 2.45/0.98    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.45/0.98    inference(ennf_transformation,[],[f1])).
% 2.45/0.98  
% 2.45/0.98  fof(f9,plain,(
% 2.45/0.98    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.45/0.98    inference(flattening,[],[f8])).
% 2.45/0.98  
% 2.45/0.98  fof(f34,plain,(
% 2.45/0.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f9])).
% 2.45/0.98  
% 2.45/0.98  fof(f6,conjecture,(
% 2.45/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f7,negated_conjecture,(
% 2.45/0.98    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 2.45/0.98    inference(negated_conjecture,[],[f6])).
% 2.45/0.98  
% 2.45/0.98  fof(f18,plain,(
% 2.45/0.98    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.45/0.98    inference(ennf_transformation,[],[f7])).
% 2.45/0.98  
% 2.45/0.98  fof(f19,plain,(
% 2.45/0.98    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.45/0.98    inference(flattening,[],[f18])).
% 2.45/0.98  
% 2.45/0.98  fof(f32,plain,(
% 2.45/0.98    ( ! [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k6_relat_1(X0) != sK5 & k5_relat_1(sK5,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(sK5),X0) & k1_relat_1(sK5) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(sK5) & v1_relat_1(sK5))) )),
% 2.45/0.98    introduced(choice_axiom,[])).
% 2.45/0.98  
% 2.45/0.98  fof(f31,plain,(
% 2.45/0.98    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k6_relat_1(sK3) != X2 & k5_relat_1(X2,sK4) = sK4 & v2_funct_1(sK4) & r1_tarski(k2_relat_1(X2),sK3) & k1_relat_1(X2) = sK3 & k1_relat_1(sK4) = sK3 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 2.45/0.98    introduced(choice_axiom,[])).
% 2.45/0.98  
% 2.45/0.98  fof(f33,plain,(
% 2.45/0.98    (k6_relat_1(sK3) != sK5 & k5_relat_1(sK5,sK4) = sK4 & v2_funct_1(sK4) & r1_tarski(k2_relat_1(sK5),sK3) & k1_relat_1(sK5) = sK3 & k1_relat_1(sK4) = sK3 & v1_funct_1(sK5) & v1_relat_1(sK5)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 2.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f32,f31])).
% 2.45/0.98  
% 2.45/0.98  fof(f54,plain,(
% 2.45/0.98    r1_tarski(k2_relat_1(sK5),sK3)),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f50,plain,(
% 2.45/0.98    v1_relat_1(sK5)),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f5,axiom,(
% 2.45/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f16,plain,(
% 2.45/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.45/0.98    inference(ennf_transformation,[],[f5])).
% 2.45/0.98  
% 2.45/0.98  fof(f17,plain,(
% 2.45/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.45/0.98    inference(flattening,[],[f16])).
% 2.45/0.98  
% 2.45/0.98  fof(f29,plain,(
% 2.45/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.45/0.98    inference(nnf_transformation,[],[f17])).
% 2.45/0.98  
% 2.45/0.98  fof(f30,plain,(
% 2.45/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.45/0.98    inference(flattening,[],[f29])).
% 2.45/0.98  
% 2.45/0.98  fof(f46,plain,(
% 2.45/0.98    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f30])).
% 2.45/0.98  
% 2.45/0.98  fof(f53,plain,(
% 2.45/0.98    k1_relat_1(sK5) = sK3),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f51,plain,(
% 2.45/0.98    v1_funct_1(sK5)),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f49,plain,(
% 2.45/0.98    v1_funct_1(sK4)),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f4,axiom,(
% 2.45/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f14,plain,(
% 2.45/0.98    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.45/0.98    inference(ennf_transformation,[],[f4])).
% 2.45/0.98  
% 2.45/0.98  fof(f15,plain,(
% 2.45/0.98    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.45/0.98    inference(flattening,[],[f14])).
% 2.45/0.98  
% 2.45/0.98  fof(f24,plain,(
% 2.45/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.45/0.98    inference(nnf_transformation,[],[f15])).
% 2.45/0.98  
% 2.45/0.98  fof(f25,plain,(
% 2.45/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.45/0.98    inference(flattening,[],[f24])).
% 2.45/0.98  
% 2.45/0.98  fof(f26,plain,(
% 2.45/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.45/0.98    inference(rectify,[],[f25])).
% 2.45/0.98  
% 2.45/0.98  fof(f27,plain,(
% 2.45/0.98    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK2(X0,X1)) != sK2(X0,X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.45/0.98    introduced(choice_axiom,[])).
% 2.45/0.98  
% 2.45/0.98  fof(f28,plain,(
% 2.45/0.98    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK2(X0,X1)) != sK2(X0,X1) & r2_hidden(sK2(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 2.45/0.98  
% 2.45/0.98  fof(f43,plain,(
% 2.45/0.98    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f28])).
% 2.45/0.98  
% 2.45/0.98  fof(f59,plain,(
% 2.45/0.98    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.45/0.98    inference(equality_resolution,[],[f43])).
% 2.45/0.98  
% 2.45/0.98  fof(f57,plain,(
% 2.45/0.98    k6_relat_1(sK3) != sK5),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f3,axiom,(
% 2.45/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f12,plain,(
% 2.45/0.98    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.45/0.98    inference(ennf_transformation,[],[f3])).
% 2.45/0.98  
% 2.45/0.98  fof(f13,plain,(
% 2.45/0.98    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.45/0.98    inference(flattening,[],[f12])).
% 2.45/0.98  
% 2.45/0.98  fof(f40,plain,(
% 2.45/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f13])).
% 2.45/0.98  
% 2.45/0.98  fof(f56,plain,(
% 2.45/0.98    k5_relat_1(sK5,sK4) = sK4),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f48,plain,(
% 2.45/0.98    v1_relat_1(sK4)),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f2,axiom,(
% 2.45/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 2.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f10,plain,(
% 2.45/0.98    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.45/0.98    inference(ennf_transformation,[],[f2])).
% 2.45/0.98  
% 2.45/0.98  fof(f11,plain,(
% 2.45/0.98    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.45/0.98    inference(flattening,[],[f10])).
% 2.45/0.98  
% 2.45/0.98  fof(f20,plain,(
% 2.45/0.98    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.45/0.98    inference(nnf_transformation,[],[f11])).
% 2.45/0.98  
% 2.45/0.98  fof(f21,plain,(
% 2.45/0.98    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.45/0.98    inference(rectify,[],[f20])).
% 2.45/0.98  
% 2.45/0.98  fof(f22,plain,(
% 2.45/0.98    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 2.45/0.98    introduced(choice_axiom,[])).
% 2.45/0.98  
% 2.45/0.98  fof(f23,plain,(
% 2.45/0.98    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 2.45/0.98  
% 2.45/0.98  fof(f35,plain,(
% 2.45/0.98    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f23])).
% 2.45/0.98  
% 2.45/0.98  fof(f52,plain,(
% 2.45/0.98    k1_relat_1(sK4) = sK3),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f55,plain,(
% 2.45/0.98    v2_funct_1(sK4)),
% 2.45/0.98    inference(cnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f44,plain,(
% 2.45/0.98    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | k1_funct_1(X1,sK2(X0,X1)) != sK2(X0,X1) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f28])).
% 2.45/0.98  
% 2.45/0.98  fof(f58,plain,(
% 2.45/0.98    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k1_funct_1(X1,sK2(k1_relat_1(X1),X1)) != sK2(k1_relat_1(X1),X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.45/0.98    inference(equality_resolution,[],[f44])).
% 2.45/0.98  
% 2.45/0.98  cnf(c_0,plain,
% 2.45/0.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.45/0.98      | ~ v1_relat_1(X0)
% 2.45/0.98      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 2.45/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_17,negated_conjecture,
% 2.45/0.98      ( r1_tarski(k2_relat_1(sK5),sK3) ),
% 2.45/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_218,plain,
% 2.45/0.98      ( ~ v1_relat_1(X0)
% 2.45/0.98      | k5_relat_1(X0,k6_relat_1(X1)) = X0
% 2.45/0.98      | k2_relat_1(X0) != k2_relat_1(sK5)
% 2.45/0.98      | sK3 != X1 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_17]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_219,plain,
% 2.45/0.98      ( ~ v1_relat_1(X0)
% 2.45/0.98      | k5_relat_1(X0,k6_relat_1(sK3)) = X0
% 2.45/0.98      | k2_relat_1(X0) != k2_relat_1(sK5) ),
% 2.45/0.98      inference(unflattening,[status(thm)],[c_218]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1023,plain,
% 2.45/0.98      ( k5_relat_1(X0,k6_relat_1(sK3)) = X0
% 2.45/0.98      | k2_relat_1(X0) != k2_relat_1(sK5)
% 2.45/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1327,plain,
% 2.45/0.98      ( k5_relat_1(sK5,k6_relat_1(sK3)) = sK5
% 2.45/0.98      | v1_relat_1(sK5) != iProver_top ),
% 2.45/0.98      inference(equality_resolution,[status(thm)],[c_1023]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_21,negated_conjecture,
% 2.45/0.98      ( v1_relat_1(sK5) ),
% 2.45/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_681,plain,( X0 = X0 ),theory(equality) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1224,plain,
% 2.45/0.98      ( k2_relat_1(sK5) = k2_relat_1(sK5) ),
% 2.45/0.98      inference(instantiation,[status(thm)],[c_681]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1225,plain,
% 2.45/0.98      ( ~ v1_relat_1(sK5)
% 2.45/0.98      | k5_relat_1(sK5,k6_relat_1(sK3)) = sK5
% 2.45/0.98      | k2_relat_1(sK5) != k2_relat_1(sK5) ),
% 2.45/0.98      inference(instantiation,[status(thm)],[c_219]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1545,plain,
% 2.45/0.98      ( k5_relat_1(sK5,k6_relat_1(sK3)) = sK5 ),
% 2.45/0.98      inference(global_propositional_subsumption,
% 2.45/0.98                [status(thm)],
% 2.45/0.98                [c_1327,c_21,c_1224,c_1225]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_12,plain,
% 2.45/0.98      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
% 2.45/0.98      | r2_hidden(k1_funct_1(X1,X0),X2)
% 2.45/0.98      | ~ v1_funct_1(X1)
% 2.45/0.98      | ~ v1_relat_1(X1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1030,plain,
% 2.45/0.98      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))) != iProver_top
% 2.45/0.98      | r2_hidden(k1_funct_1(X1,X0),X2) = iProver_top
% 2.45/0.98      | v1_funct_1(X1) != iProver_top
% 2.45/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1733,plain,
% 2.45/0.98      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.45/0.98      | r2_hidden(k1_funct_1(sK5,X0),sK3) = iProver_top
% 2.45/0.98      | v1_funct_1(sK5) != iProver_top
% 2.45/0.98      | v1_relat_1(sK5) != iProver_top ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_1545,c_1030]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_18,negated_conjecture,
% 2.45/0.98      ( k1_relat_1(sK5) = sK3 ),
% 2.45/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1738,plain,
% 2.45/0.98      ( r2_hidden(X0,sK3) != iProver_top
% 2.45/0.98      | r2_hidden(k1_funct_1(sK5,X0),sK3) = iProver_top
% 2.45/0.98      | v1_funct_1(sK5) != iProver_top
% 2.45/0.98      | v1_relat_1(sK5) != iProver_top ),
% 2.45/0.98      inference(light_normalisation,[status(thm)],[c_1733,c_18]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_26,plain,
% 2.45/0.98      ( v1_relat_1(sK5) = iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_20,negated_conjecture,
% 2.45/0.98      ( v1_funct_1(sK5) ),
% 2.45/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_27,plain,
% 2.45/0.98      ( v1_funct_1(sK5) = iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1762,plain,
% 2.45/0.98      ( r2_hidden(X0,sK3) != iProver_top
% 2.45/0.98      | r2_hidden(k1_funct_1(sK5,X0),sK3) = iProver_top ),
% 2.45/0.98      inference(global_propositional_subsumption,
% 2.45/0.98                [status(thm)],
% 2.45/0.98                [c_1738,c_26,c_27]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_22,negated_conjecture,
% 2.45/0.98      ( v1_funct_1(sK4) ),
% 2.45/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1025,plain,
% 2.45/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_8,plain,
% 2.45/0.98      ( r2_hidden(sK2(k1_relat_1(X0),X0),k1_relat_1(X0))
% 2.45/0.98      | ~ v1_funct_1(X0)
% 2.45/0.98      | ~ v1_relat_1(X0)
% 2.45/0.98      | k6_relat_1(k1_relat_1(X0)) = X0 ),
% 2.45/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1034,plain,
% 2.45/0.98      ( k6_relat_1(k1_relat_1(X0)) = X0
% 2.45/0.98      | r2_hidden(sK2(k1_relat_1(X0),X0),k1_relat_1(X0)) = iProver_top
% 2.45/0.98      | v1_funct_1(X0) != iProver_top
% 2.45/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_2131,plain,
% 2.45/0.98      ( k6_relat_1(k1_relat_1(sK5)) = sK5
% 2.45/0.98      | r2_hidden(sK2(sK3,sK5),sK3) = iProver_top
% 2.45/0.98      | v1_funct_1(sK5) != iProver_top
% 2.45/0.98      | v1_relat_1(sK5) != iProver_top ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_18,c_1034]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_2185,plain,
% 2.45/0.98      ( k6_relat_1(sK3) = sK5
% 2.45/0.98      | r2_hidden(sK2(sK3,sK5),sK3) = iProver_top
% 2.45/0.98      | v1_funct_1(sK5) != iProver_top
% 2.45/0.98      | v1_relat_1(sK5) != iProver_top ),
% 2.45/0.98      inference(light_normalisation,[status(thm)],[c_2131,c_18]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_14,negated_conjecture,
% 2.45/0.98      ( k6_relat_1(sK3) != sK5 ),
% 2.45/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_2294,plain,
% 2.45/0.98      ( r2_hidden(sK2(sK3,sK5),sK3) = iProver_top ),
% 2.45/0.98      inference(global_propositional_subsumption,
% 2.45/0.98                [status(thm)],
% 2.45/0.98                [c_2185,c_26,c_27,c_14]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_6,plain,
% 2.45/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.45/0.98      | ~ v1_funct_1(X1)
% 2.45/0.98      | ~ v1_funct_1(X2)
% 2.45/0.98      | ~ v1_relat_1(X1)
% 2.45/0.98      | ~ v1_relat_1(X2)
% 2.45/0.98      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 2.45/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1036,plain,
% 2.45/0.98      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 2.45/0.98      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 2.45/0.98      | v1_funct_1(X0) != iProver_top
% 2.45/0.98      | v1_funct_1(X1) != iProver_top
% 2.45/0.98      | v1_relat_1(X0) != iProver_top
% 2.45/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_2859,plain,
% 2.45/0.98      ( k1_funct_1(X0,k1_funct_1(sK5,X1)) = k1_funct_1(k5_relat_1(sK5,X0),X1)
% 2.45/0.98      | r2_hidden(X1,sK3) != iProver_top
% 2.45/0.98      | v1_funct_1(X0) != iProver_top
% 2.45/0.98      | v1_funct_1(sK5) != iProver_top
% 2.45/0.98      | v1_relat_1(X0) != iProver_top
% 2.45/0.98      | v1_relat_1(sK5) != iProver_top ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_18,c_1036]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_3004,plain,
% 2.45/0.98      ( v1_relat_1(X0) != iProver_top
% 2.45/0.98      | k1_funct_1(X0,k1_funct_1(sK5,X1)) = k1_funct_1(k5_relat_1(sK5,X0),X1)
% 2.45/0.98      | r2_hidden(X1,sK3) != iProver_top
% 2.45/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.45/0.98      inference(global_propositional_subsumption,
% 2.45/0.98                [status(thm)],
% 2.45/0.98                [c_2859,c_26,c_27]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_3005,plain,
% 2.45/0.98      ( k1_funct_1(X0,k1_funct_1(sK5,X1)) = k1_funct_1(k5_relat_1(sK5,X0),X1)
% 2.45/0.98      | r2_hidden(X1,sK3) != iProver_top
% 2.45/0.98      | v1_funct_1(X0) != iProver_top
% 2.45/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.45/0.98      inference(renaming,[status(thm)],[c_3004]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_3017,plain,
% 2.45/0.98      ( k1_funct_1(k5_relat_1(sK5,X0),sK2(sK3,sK5)) = k1_funct_1(X0,k1_funct_1(sK5,sK2(sK3,sK5)))
% 2.45/0.98      | v1_funct_1(X0) != iProver_top
% 2.45/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_2294,c_3005]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_3199,plain,
% 2.45/0.98      ( k1_funct_1(sK4,k1_funct_1(sK5,sK2(sK3,sK5))) = k1_funct_1(k5_relat_1(sK5,sK4),sK2(sK3,sK5))
% 2.45/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_1025,c_3017]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_15,negated_conjecture,
% 2.45/0.98      ( k5_relat_1(sK5,sK4) = sK4 ),
% 2.45/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_3202,plain,
% 2.45/0.98      ( k1_funct_1(sK4,k1_funct_1(sK5,sK2(sK3,sK5))) = k1_funct_1(sK4,sK2(sK3,sK5))
% 2.45/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.45/0.98      inference(light_normalisation,[status(thm)],[c_3199,c_15]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_23,negated_conjecture,
% 2.45/0.98      ( v1_relat_1(sK4) ),
% 2.45/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_24,plain,
% 2.45/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_3212,plain,
% 2.45/0.98      ( k1_funct_1(sK4,k1_funct_1(sK5,sK2(sK3,sK5))) = k1_funct_1(sK4,sK2(sK3,sK5)) ),
% 2.45/0.98      inference(global_propositional_subsumption,
% 2.45/0.98                [status(thm)],
% 2.45/0.98                [c_3202,c_24]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_5,plain,
% 2.45/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.45/0.98      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.45/0.98      | ~ v1_funct_1(X1)
% 2.45/0.98      | ~ v2_funct_1(X1)
% 2.45/0.98      | ~ v1_relat_1(X1)
% 2.45/0.98      | X0 = X2
% 2.45/0.98      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 2.45/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1037,plain,
% 2.45/0.98      ( X0 = X1
% 2.45/0.98      | k1_funct_1(X2,X0) != k1_funct_1(X2,X1)
% 2.45/0.98      | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
% 2.45/0.98      | r2_hidden(X1,k1_relat_1(X2)) != iProver_top
% 2.45/0.98      | v1_funct_1(X2) != iProver_top
% 2.45/0.98      | v2_funct_1(X2) != iProver_top
% 2.45/0.98      | v1_relat_1(X2) != iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_3475,plain,
% 2.45/0.98      ( k1_funct_1(sK4,sK2(sK3,sK5)) != k1_funct_1(sK4,X0)
% 2.45/0.98      | k1_funct_1(sK5,sK2(sK3,sK5)) = X0
% 2.45/0.98      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.45/0.98      | r2_hidden(k1_funct_1(sK5,sK2(sK3,sK5)),k1_relat_1(sK4)) != iProver_top
% 2.45/0.98      | v1_funct_1(sK4) != iProver_top
% 2.45/0.98      | v2_funct_1(sK4) != iProver_top
% 2.45/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_3212,c_1037]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_19,negated_conjecture,
% 2.45/0.98      ( k1_relat_1(sK4) = sK3 ),
% 2.45/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_3529,plain,
% 2.45/0.98      ( k1_funct_1(sK4,sK2(sK3,sK5)) != k1_funct_1(sK4,X0)
% 2.45/0.98      | k1_funct_1(sK5,sK2(sK3,sK5)) = X0
% 2.45/0.98      | r2_hidden(X0,sK3) != iProver_top
% 2.45/0.98      | r2_hidden(k1_funct_1(sK5,sK2(sK3,sK5)),sK3) != iProver_top
% 2.45/0.98      | v1_funct_1(sK4) != iProver_top
% 2.45/0.98      | v2_funct_1(sK4) != iProver_top
% 2.45/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.45/0.98      inference(light_normalisation,[status(thm)],[c_3475,c_19]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_25,plain,
% 2.45/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_16,negated_conjecture,
% 2.45/0.98      ( v2_funct_1(sK4) ),
% 2.45/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_29,plain,
% 2.45/0.98      ( v2_funct_1(sK4) = iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_3611,plain,
% 2.45/0.98      ( r2_hidden(k1_funct_1(sK5,sK2(sK3,sK5)),sK3) != iProver_top
% 2.45/0.98      | r2_hidden(X0,sK3) != iProver_top
% 2.45/0.98      | k1_funct_1(sK5,sK2(sK3,sK5)) = X0
% 2.45/0.98      | k1_funct_1(sK4,sK2(sK3,sK5)) != k1_funct_1(sK4,X0) ),
% 2.45/0.98      inference(global_propositional_subsumption,
% 2.45/0.98                [status(thm)],
% 2.45/0.98                [c_3529,c_24,c_25,c_29]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_3612,plain,
% 2.45/0.98      ( k1_funct_1(sK4,sK2(sK3,sK5)) != k1_funct_1(sK4,X0)
% 2.45/0.98      | k1_funct_1(sK5,sK2(sK3,sK5)) = X0
% 2.45/0.98      | r2_hidden(X0,sK3) != iProver_top
% 2.45/0.98      | r2_hidden(k1_funct_1(sK5,sK2(sK3,sK5)),sK3) != iProver_top ),
% 2.45/0.98      inference(renaming,[status(thm)],[c_3611]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_3622,plain,
% 2.45/0.98      ( k1_funct_1(sK5,sK2(sK3,sK5)) = sK2(sK3,sK5)
% 2.45/0.99      | r2_hidden(sK2(sK3,sK5),sK3) != iProver_top
% 2.45/0.99      | r2_hidden(k1_funct_1(sK5,sK2(sK3,sK5)),sK3) != iProver_top ),
% 2.45/0.99      inference(equality_resolution,[status(thm)],[c_3612]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_7,plain,
% 2.45/0.99      ( ~ v1_funct_1(X0)
% 2.45/0.99      | ~ v1_relat_1(X0)
% 2.45/0.99      | k1_funct_1(X0,sK2(k1_relat_1(X0),X0)) != sK2(k1_relat_1(X0),X0)
% 2.45/0.99      | k6_relat_1(k1_relat_1(X0)) = X0 ),
% 2.45/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_1035,plain,
% 2.45/0.99      ( k1_funct_1(X0,sK2(k1_relat_1(X0),X0)) != sK2(k1_relat_1(X0),X0)
% 2.45/0.99      | k6_relat_1(k1_relat_1(X0)) = X0
% 2.45/0.99      | v1_funct_1(X0) != iProver_top
% 2.45/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.45/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_2770,plain,
% 2.45/0.99      ( k1_funct_1(sK5,sK2(sK3,sK5)) != sK2(k1_relat_1(sK5),sK5)
% 2.45/0.99      | k6_relat_1(k1_relat_1(sK5)) = sK5
% 2.45/0.99      | v1_funct_1(sK5) != iProver_top
% 2.45/0.99      | v1_relat_1(sK5) != iProver_top ),
% 2.45/0.99      inference(superposition,[status(thm)],[c_18,c_1035]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_2785,plain,
% 2.45/0.99      ( k1_funct_1(sK5,sK2(sK3,sK5)) != sK2(sK3,sK5)
% 2.45/0.99      | k6_relat_1(sK3) = sK5
% 2.45/0.99      | v1_funct_1(sK5) != iProver_top
% 2.45/0.99      | v1_relat_1(sK5) != iProver_top ),
% 2.45/0.99      inference(light_normalisation,[status(thm)],[c_2770,c_18]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_3754,plain,
% 2.45/0.99      ( r2_hidden(k1_funct_1(sK5,sK2(sK3,sK5)),sK3) != iProver_top ),
% 2.45/0.99      inference(global_propositional_subsumption,
% 2.45/0.99                [status(thm)],
% 2.45/0.99                [c_3622,c_26,c_27,c_14,c_2185,c_2785]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_3759,plain,
% 2.45/0.99      ( r2_hidden(sK2(sK3,sK5),sK3) != iProver_top ),
% 2.45/0.99      inference(superposition,[status(thm)],[c_1762,c_3754]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(contradiction,plain,
% 2.45/0.99      ( $false ),
% 2.45/0.99      inference(minisat,[status(thm)],[c_3759,c_2185,c_14,c_27,c_26]) ).
% 2.45/0.99  
% 2.45/0.99  
% 2.45/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.45/0.99  
% 2.45/0.99  ------                               Statistics
% 2.45/0.99  
% 2.45/0.99  ------ General
% 2.45/0.99  
% 2.45/0.99  abstr_ref_over_cycles:                  0
% 2.45/0.99  abstr_ref_under_cycles:                 0
% 2.45/0.99  gc_basic_clause_elim:                   0
% 2.45/0.99  forced_gc_time:                         0
% 2.45/0.99  parsing_time:                           0.009
% 2.45/0.99  unif_index_cands_time:                  0.
% 2.45/0.99  unif_index_add_time:                    0.
% 2.45/0.99  orderings_time:                         0.
% 2.45/0.99  out_proof_time:                         0.008
% 2.45/0.99  total_time:                             0.154
% 2.45/0.99  num_of_symbols:                         47
% 2.45/0.99  num_of_terms:                           3025
% 2.45/0.99  
% 2.45/0.99  ------ Preprocessing
% 2.45/0.99  
% 2.45/0.99  num_of_splits:                          0
% 2.45/0.99  num_of_split_atoms:                     0
% 2.45/0.99  num_of_reused_defs:                     0
% 2.45/0.99  num_eq_ax_congr_red:                    9
% 2.45/0.99  num_of_sem_filtered_clauses:            1
% 2.45/0.99  num_of_subtypes:                        0
% 2.45/0.99  monotx_restored_types:                  0
% 2.45/0.99  sat_num_of_epr_types:                   0
% 2.45/0.99  sat_num_of_non_cyclic_types:            0
% 2.45/0.99  sat_guarded_non_collapsed_types:        0
% 2.45/0.99  num_pure_diseq_elim:                    0
% 2.45/0.99  simp_replaced_by:                       0
% 2.45/0.99  res_preprocessed:                       118
% 2.45/0.99  prep_upred:                             0
% 2.45/0.99  prep_unflattend:                        11
% 2.45/0.99  smt_new_axioms:                         0
% 2.45/0.99  pred_elim_cands:                        4
% 2.45/0.99  pred_elim:                              1
% 2.45/0.99  pred_elim_cl:                           1
% 2.45/0.99  pred_elim_cycles:                       3
% 2.45/0.99  merged_defs:                            0
% 2.45/0.99  merged_defs_ncl:                        0
% 2.45/0.99  bin_hyper_res:                          0
% 2.45/0.99  prep_cycles:                            4
% 2.45/0.99  pred_elim_time:                         0.011
% 2.45/0.99  splitting_time:                         0.
% 2.45/0.99  sem_filter_time:                        0.
% 2.45/0.99  monotx_time:                            0.001
% 2.45/0.99  subtype_inf_time:                       0.
% 2.45/0.99  
% 2.45/0.99  ------ Problem properties
% 2.45/0.99  
% 2.45/0.99  clauses:                                23
% 2.45/0.99  conjectures:                            9
% 2.45/0.99  epr:                                    5
% 2.45/0.99  horn:                                   19
% 2.45/0.99  ground:                                 9
% 2.45/0.99  unary:                                  9
% 2.45/0.99  binary:                                 0
% 2.45/0.99  lits:                                   69
% 2.45/0.99  lits_eq:                                16
% 2.45/0.99  fd_pure:                                0
% 2.45/0.99  fd_pseudo:                              0
% 2.45/0.99  fd_cond:                                0
% 2.45/0.99  fd_pseudo_cond:                         1
% 2.45/0.99  ac_symbols:                             0
% 2.45/0.99  
% 2.45/0.99  ------ Propositional Solver
% 2.45/0.99  
% 2.45/0.99  prop_solver_calls:                      29
% 2.45/0.99  prop_fast_solver_calls:                 969
% 2.45/0.99  smt_solver_calls:                       0
% 2.45/0.99  smt_fast_solver_calls:                  0
% 2.45/0.99  prop_num_of_clauses:                    1024
% 2.45/0.99  prop_preprocess_simplified:             3820
% 2.45/0.99  prop_fo_subsumed:                       35
% 2.45/0.99  prop_solver_time:                       0.
% 2.45/0.99  smt_solver_time:                        0.
% 2.45/0.99  smt_fast_solver_time:                   0.
% 2.45/0.99  prop_fast_solver_time:                  0.
% 2.45/0.99  prop_unsat_core_time:                   0.
% 2.45/0.99  
% 2.45/0.99  ------ QBF
% 2.45/0.99  
% 2.45/0.99  qbf_q_res:                              0
% 2.45/0.99  qbf_num_tautologies:                    0
% 2.45/0.99  qbf_prep_cycles:                        0
% 2.45/0.99  
% 2.45/0.99  ------ BMC1
% 2.45/0.99  
% 2.45/0.99  bmc1_current_bound:                     -1
% 2.45/0.99  bmc1_last_solved_bound:                 -1
% 2.45/0.99  bmc1_unsat_core_size:                   -1
% 2.45/0.99  bmc1_unsat_core_parents_size:           -1
% 2.45/0.99  bmc1_merge_next_fun:                    0
% 2.45/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.45/0.99  
% 2.45/0.99  ------ Instantiation
% 2.45/0.99  
% 2.45/0.99  inst_num_of_clauses:                    341
% 2.45/0.99  inst_num_in_passive:                    75
% 2.45/0.99  inst_num_in_active:                     219
% 2.45/0.99  inst_num_in_unprocessed:                47
% 2.45/0.99  inst_num_of_loops:                      270
% 2.45/0.99  inst_num_of_learning_restarts:          0
% 2.45/0.99  inst_num_moves_active_passive:          46
% 2.45/0.99  inst_lit_activity:                      0
% 2.45/0.99  inst_lit_activity_moves:                0
% 2.45/0.99  inst_num_tautologies:                   0
% 2.45/0.99  inst_num_prop_implied:                  0
% 2.45/0.99  inst_num_existing_simplified:           0
% 2.45/0.99  inst_num_eq_res_simplified:             0
% 2.45/0.99  inst_num_child_elim:                    0
% 2.45/0.99  inst_num_of_dismatching_blockings:      249
% 2.45/0.99  inst_num_of_non_proper_insts:           538
% 2.45/0.99  inst_num_of_duplicates:                 0
% 2.45/0.99  inst_inst_num_from_inst_to_res:         0
% 2.45/0.99  inst_dismatching_checking_time:         0.
% 2.45/0.99  
% 2.45/0.99  ------ Resolution
% 2.45/0.99  
% 2.45/0.99  res_num_of_clauses:                     0
% 2.45/0.99  res_num_in_passive:                     0
% 2.45/0.99  res_num_in_active:                      0
% 2.45/0.99  res_num_of_loops:                       122
% 2.45/0.99  res_forward_subset_subsumed:            38
% 2.45/0.99  res_backward_subset_subsumed:           4
% 2.45/0.99  res_forward_subsumed:                   0
% 2.45/0.99  res_backward_subsumed:                  0
% 2.45/0.99  res_forward_subsumption_resolution:     0
% 2.45/0.99  res_backward_subsumption_resolution:    0
% 2.45/0.99  res_clause_to_clause_subsumption:       170
% 2.45/0.99  res_orphan_elimination:                 0
% 2.45/0.99  res_tautology_del:                      72
% 2.45/0.99  res_num_eq_res_simplified:              0
% 2.45/0.99  res_num_sel_changes:                    0
% 2.45/0.99  res_moves_from_active_to_pass:          0
% 2.45/0.99  
% 2.45/0.99  ------ Superposition
% 2.45/0.99  
% 2.45/0.99  sup_time_total:                         0.
% 2.45/0.99  sup_time_generating:                    0.
% 2.45/0.99  sup_time_sim_full:                      0.
% 2.45/0.99  sup_time_sim_immed:                     0.
% 2.45/0.99  
% 2.45/0.99  sup_num_of_clauses:                     93
% 2.45/0.99  sup_num_in_active:                      53
% 2.45/0.99  sup_num_in_passive:                     40
% 2.45/0.99  sup_num_of_loops:                       52
% 2.45/0.99  sup_fw_superposition:                   66
% 2.45/0.99  sup_bw_superposition:                   16
% 2.45/0.99  sup_immediate_simplified:               10
% 2.45/0.99  sup_given_eliminated:                   0
% 2.45/0.99  comparisons_done:                       0
% 2.45/0.99  comparisons_avoided:                    3
% 2.45/0.99  
% 2.45/0.99  ------ Simplifications
% 2.45/0.99  
% 2.45/0.99  
% 2.45/0.99  sim_fw_subset_subsumed:                 3
% 2.45/0.99  sim_bw_subset_subsumed:                 0
% 2.45/0.99  sim_fw_subsumed:                        0
% 2.45/0.99  sim_bw_subsumed:                        0
% 2.45/0.99  sim_fw_subsumption_res:                 0
% 2.45/0.99  sim_bw_subsumption_res:                 0
% 2.45/0.99  sim_tautology_del:                      4
% 2.45/0.99  sim_eq_tautology_del:                   2
% 2.45/0.99  sim_eq_res_simp:                        0
% 2.45/0.99  sim_fw_demodulated:                     0
% 2.45/0.99  sim_bw_demodulated:                     0
% 2.45/0.99  sim_light_normalised:                   7
% 2.45/0.99  sim_joinable_taut:                      0
% 2.45/0.99  sim_joinable_simp:                      0
% 2.45/0.99  sim_ac_normalised:                      0
% 2.45/0.99  sim_smt_subsumption:                    0
% 2.45/0.99  
%------------------------------------------------------------------------------
