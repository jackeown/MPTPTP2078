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
% DateTime   : Thu Dec  3 11:50:24 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 696 expanded)
%              Number of clauses        :   61 ( 171 expanded)
%              Number of leaves         :   13 ( 162 expanded)
%              Depth                    :   22
%              Number of atoms          :  478 (3960 expanded)
%              Number of equality atoms :  206 (1401 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f31,plain,
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

fof(f32,plain,
    ( ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
      | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 )
    & r2_hidden(sK3,k2_relat_1(sK4))
    & v2_funct_1(sK4)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f22,f31])).

fof(f52,plain,(
    r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X5)) = X5
        & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) = X2
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK0(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK0(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK0(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
                  & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X5)) = X5
                    & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).

fof(f33,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f34,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_706,plain,
    ( r2_hidden(sK3,k2_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_713,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_18,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_241,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_242,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_246,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_242,c_20,c_19])).

cnf(c_703,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_246])).

cnf(c_1317,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK2(sK4,X0))) = sK2(sK4,X0)
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_713,c_703])).

cnf(c_21,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1660,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK2(sK4,X0))) = sK2(sK4,X0)
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1317,c_21,c_22])).

cnf(c_1668,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK2(sK4,sK3))) = sK2(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_706,c_1660])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_714,plain,
    ( k1_funct_1(X0,sK2(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1222,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK3)) = sK3
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_714])).

cnf(c_905,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_funct_1(sK4,sK2(sK4,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1373,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1222,c_20,c_19,c_17,c_905])).

cnf(c_1675,plain,
    ( k1_funct_1(k2_funct_1(sK4),sK3) = sK2(sK4,sK3) ),
    inference(light_normalisation,[status(thm)],[c_1668,c_1373])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_710,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2))) = iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3735,plain,
    ( r2_hidden(sK2(sK4,sK3),k1_relat_1(X0)) != iProver_top
    | r2_hidden(sK3,k1_relat_1(k5_relat_1(k2_funct_1(sK4),X0))) = iProver_top
    | r2_hidden(sK3,k1_relat_1(k2_funct_1(sK4))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1675,c_710])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_225,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_226,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_32,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_228,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_226,c_20,c_19,c_18,c_32])).

cnf(c_3820,plain,
    ( r2_hidden(sK2(sK4,sK3),k1_relat_1(X0)) != iProver_top
    | r2_hidden(sK3,k1_relat_1(k5_relat_1(k2_funct_1(sK4),X0))) = iProver_top
    | r2_hidden(sK3,k2_relat_1(sK4)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3735,c_228])).

cnf(c_24,plain,
    ( r2_hidden(sK3,k2_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_49,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_51,plain,
    ( v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_52,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_54,plain,
    ( v1_relat_1(sK4) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_4619,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_hidden(sK3,k1_relat_1(k5_relat_1(k2_funct_1(sK4),X0))) = iProver_top
    | r2_hidden(sK2(sK4,sK3),k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3820,c_21,c_22,c_24,c_51,c_54])).

cnf(c_4620,plain,
    ( r2_hidden(sK2(sK4,sK3),k1_relat_1(X0)) != iProver_top
    | r2_hidden(sK3,k1_relat_1(k5_relat_1(k2_funct_1(sK4),X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4619])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_707,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4632,plain,
    ( k1_funct_1(X0,k1_funct_1(k2_funct_1(sK4),sK3)) = k1_funct_1(k5_relat_1(k2_funct_1(sK4),X0),sK3)
    | r2_hidden(sK2(sK4,sK3),k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4620,c_707])).

cnf(c_4639,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),X0),sK3) = k1_funct_1(X0,sK2(sK4,sK3))
    | r2_hidden(sK2(sK4,sK3),k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4632,c_1675])).

cnf(c_4676,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = k1_funct_1(sK4,sK2(sK4,sK3))
    | r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4639])).

cnf(c_16,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
    | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1681,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
    | k1_funct_1(sK4,sK2(sK4,sK3)) != sK3 ),
    inference(demodulation,[status(thm)],[c_1675,c_16])).

cnf(c_1682,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
    | sK3 != sK3 ),
    inference(light_normalisation,[status(thm)],[c_1681,c_1373])).

cnf(c_1683,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_1682])).

cnf(c_402,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_900,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != X0
    | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_402])).

cnf(c_1560,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != k1_funct_1(sK4,sK2(sK4,sK3))
    | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = sK3
    | sK3 != k1_funct_1(sK4,sK2(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_900])).

cnf(c_939,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_402])).

cnf(c_1108,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_939])).

cnf(c_1508,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK3)) != sK3
    | sK3 = k1_funct_1(sK4,sK2(sK4,sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1108])).

cnf(c_401,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_957,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_401])).

cnf(c_902,plain,
    ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4))
    | ~ r2_hidden(sK3,k2_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_903,plain,
    ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(sK3,k2_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_902])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4676,c_1683,c_1560,c_1508,c_957,c_905,c_903,c_54,c_51,c_24,c_17,c_22,c_19,c_21,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n012.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 10:21:37 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.31  % Running in FOF mode
% 3.42/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/0.96  
% 3.42/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.42/0.96  
% 3.42/0.96  ------  iProver source info
% 3.42/0.96  
% 3.42/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.42/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.42/0.96  git: non_committed_changes: false
% 3.42/0.96  git: last_make_outside_of_git: false
% 3.42/0.96  
% 3.42/0.96  ------ 
% 3.42/0.96  
% 3.42/0.96  ------ Input Options
% 3.42/0.96  
% 3.42/0.96  --out_options                           all
% 3.42/0.96  --tptp_safe_out                         true
% 3.42/0.96  --problem_path                          ""
% 3.42/0.96  --include_path                          ""
% 3.42/0.96  --clausifier                            res/vclausify_rel
% 3.42/0.96  --clausifier_options                    --mode clausify
% 3.42/0.96  --stdin                                 false
% 3.42/0.96  --stats_out                             all
% 3.42/0.96  
% 3.42/0.96  ------ General Options
% 3.42/0.96  
% 3.42/0.96  --fof                                   false
% 3.42/0.96  --time_out_real                         305.
% 3.42/0.96  --time_out_virtual                      -1.
% 3.42/0.96  --symbol_type_check                     false
% 3.42/0.96  --clausify_out                          false
% 3.42/0.96  --sig_cnt_out                           false
% 3.42/0.96  --trig_cnt_out                          false
% 3.42/0.96  --trig_cnt_out_tolerance                1.
% 3.42/0.96  --trig_cnt_out_sk_spl                   false
% 3.42/0.96  --abstr_cl_out                          false
% 3.42/0.96  
% 3.42/0.96  ------ Global Options
% 3.42/0.96  
% 3.42/0.96  --schedule                              default
% 3.42/0.96  --add_important_lit                     false
% 3.42/0.96  --prop_solver_per_cl                    1000
% 3.42/0.96  --min_unsat_core                        false
% 3.42/0.96  --soft_assumptions                      false
% 3.42/0.96  --soft_lemma_size                       3
% 3.42/0.96  --prop_impl_unit_size                   0
% 3.42/0.96  --prop_impl_unit                        []
% 3.42/0.96  --share_sel_clauses                     true
% 3.42/0.96  --reset_solvers                         false
% 3.42/0.96  --bc_imp_inh                            [conj_cone]
% 3.42/0.96  --conj_cone_tolerance                   3.
% 3.42/0.96  --extra_neg_conj                        none
% 3.42/0.96  --large_theory_mode                     true
% 3.42/0.96  --prolific_symb_bound                   200
% 3.42/0.96  --lt_threshold                          2000
% 3.42/0.96  --clause_weak_htbl                      true
% 3.42/0.96  --gc_record_bc_elim                     false
% 3.42/0.96  
% 3.42/0.96  ------ Preprocessing Options
% 3.42/0.96  
% 3.42/0.96  --preprocessing_flag                    true
% 3.42/0.96  --time_out_prep_mult                    0.1
% 3.42/0.96  --splitting_mode                        input
% 3.42/0.96  --splitting_grd                         true
% 3.42/0.96  --splitting_cvd                         false
% 3.42/0.96  --splitting_cvd_svl                     false
% 3.42/0.96  --splitting_nvd                         32
% 3.42/0.96  --sub_typing                            true
% 3.42/0.96  --prep_gs_sim                           true
% 3.42/0.96  --prep_unflatten                        true
% 3.42/0.96  --prep_res_sim                          true
% 3.42/0.96  --prep_upred                            true
% 3.42/0.96  --prep_sem_filter                       exhaustive
% 3.42/0.96  --prep_sem_filter_out                   false
% 3.42/0.96  --pred_elim                             true
% 3.42/0.96  --res_sim_input                         true
% 3.42/0.96  --eq_ax_congr_red                       true
% 3.42/0.96  --pure_diseq_elim                       true
% 3.42/0.96  --brand_transform                       false
% 3.42/0.96  --non_eq_to_eq                          false
% 3.42/0.96  --prep_def_merge                        true
% 3.42/0.96  --prep_def_merge_prop_impl              false
% 3.42/0.96  --prep_def_merge_mbd                    true
% 3.42/0.96  --prep_def_merge_tr_red                 false
% 3.42/0.96  --prep_def_merge_tr_cl                  false
% 3.42/0.96  --smt_preprocessing                     true
% 3.42/0.96  --smt_ac_axioms                         fast
% 3.42/0.96  --preprocessed_out                      false
% 3.42/0.96  --preprocessed_stats                    false
% 3.42/0.96  
% 3.42/0.96  ------ Abstraction refinement Options
% 3.42/0.96  
% 3.42/0.96  --abstr_ref                             []
% 3.42/0.96  --abstr_ref_prep                        false
% 3.42/0.96  --abstr_ref_until_sat                   false
% 3.42/0.96  --abstr_ref_sig_restrict                funpre
% 3.42/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.42/0.96  --abstr_ref_under                       []
% 3.42/0.96  
% 3.42/0.96  ------ SAT Options
% 3.42/0.96  
% 3.42/0.96  --sat_mode                              false
% 3.42/0.96  --sat_fm_restart_options                ""
% 3.42/0.96  --sat_gr_def                            false
% 3.42/0.96  --sat_epr_types                         true
% 3.42/0.96  --sat_non_cyclic_types                  false
% 3.42/0.96  --sat_finite_models                     false
% 3.42/0.96  --sat_fm_lemmas                         false
% 3.42/0.96  --sat_fm_prep                           false
% 3.42/0.96  --sat_fm_uc_incr                        true
% 3.42/0.96  --sat_out_model                         small
% 3.42/0.96  --sat_out_clauses                       false
% 3.42/0.96  
% 3.42/0.96  ------ QBF Options
% 3.42/0.96  
% 3.42/0.96  --qbf_mode                              false
% 3.42/0.96  --qbf_elim_univ                         false
% 3.42/0.96  --qbf_dom_inst                          none
% 3.42/0.96  --qbf_dom_pre_inst                      false
% 3.42/0.96  --qbf_sk_in                             false
% 3.42/0.96  --qbf_pred_elim                         true
% 3.42/0.96  --qbf_split                             512
% 3.42/0.96  
% 3.42/0.96  ------ BMC1 Options
% 3.42/0.96  
% 3.42/0.96  --bmc1_incremental                      false
% 3.42/0.96  --bmc1_axioms                           reachable_all
% 3.42/0.96  --bmc1_min_bound                        0
% 3.42/0.96  --bmc1_max_bound                        -1
% 3.42/0.96  --bmc1_max_bound_default                -1
% 3.42/0.96  --bmc1_symbol_reachability              true
% 3.42/0.96  --bmc1_property_lemmas                  false
% 3.42/0.96  --bmc1_k_induction                      false
% 3.42/0.96  --bmc1_non_equiv_states                 false
% 3.42/0.96  --bmc1_deadlock                         false
% 3.42/0.96  --bmc1_ucm                              false
% 3.42/0.96  --bmc1_add_unsat_core                   none
% 3.42/0.96  --bmc1_unsat_core_children              false
% 3.42/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.42/0.96  --bmc1_out_stat                         full
% 3.42/0.96  --bmc1_ground_init                      false
% 3.42/0.96  --bmc1_pre_inst_next_state              false
% 3.42/0.96  --bmc1_pre_inst_state                   false
% 3.42/0.96  --bmc1_pre_inst_reach_state             false
% 3.42/0.96  --bmc1_out_unsat_core                   false
% 3.42/0.96  --bmc1_aig_witness_out                  false
% 3.42/0.96  --bmc1_verbose                          false
% 3.42/0.96  --bmc1_dump_clauses_tptp                false
% 3.42/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.42/0.96  --bmc1_dump_file                        -
% 3.42/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.42/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.42/0.96  --bmc1_ucm_extend_mode                  1
% 3.42/0.96  --bmc1_ucm_init_mode                    2
% 3.42/0.96  --bmc1_ucm_cone_mode                    none
% 3.42/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.42/0.96  --bmc1_ucm_relax_model                  4
% 3.42/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.42/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.42/0.96  --bmc1_ucm_layered_model                none
% 3.42/0.96  --bmc1_ucm_max_lemma_size               10
% 3.42/0.96  
% 3.42/0.96  ------ AIG Options
% 3.42/0.96  
% 3.42/0.96  --aig_mode                              false
% 3.42/0.96  
% 3.42/0.96  ------ Instantiation Options
% 3.42/0.96  
% 3.42/0.96  --instantiation_flag                    true
% 3.42/0.96  --inst_sos_flag                         false
% 3.42/0.96  --inst_sos_phase                        true
% 3.42/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.42/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.42/0.96  --inst_lit_sel_side                     num_symb
% 3.42/0.96  --inst_solver_per_active                1400
% 3.42/0.96  --inst_solver_calls_frac                1.
% 3.42/0.96  --inst_passive_queue_type               priority_queues
% 3.42/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.42/0.96  --inst_passive_queues_freq              [25;2]
% 3.42/0.96  --inst_dismatching                      true
% 3.42/0.96  --inst_eager_unprocessed_to_passive     true
% 3.42/0.96  --inst_prop_sim_given                   true
% 3.42/0.96  --inst_prop_sim_new                     false
% 3.42/0.96  --inst_subs_new                         false
% 3.42/0.96  --inst_eq_res_simp                      false
% 3.42/0.96  --inst_subs_given                       false
% 3.42/0.96  --inst_orphan_elimination               true
% 3.42/0.96  --inst_learning_loop_flag               true
% 3.42/0.96  --inst_learning_start                   3000
% 3.42/0.96  --inst_learning_factor                  2
% 3.42/0.96  --inst_start_prop_sim_after_learn       3
% 3.42/0.96  --inst_sel_renew                        solver
% 3.42/0.96  --inst_lit_activity_flag                true
% 3.42/0.96  --inst_restr_to_given                   false
% 3.42/0.96  --inst_activity_threshold               500
% 3.42/0.96  --inst_out_proof                        true
% 3.42/0.96  
% 3.42/0.96  ------ Resolution Options
% 3.42/0.96  
% 3.42/0.96  --resolution_flag                       true
% 3.42/0.96  --res_lit_sel                           adaptive
% 3.42/0.96  --res_lit_sel_side                      none
% 3.42/0.96  --res_ordering                          kbo
% 3.42/0.96  --res_to_prop_solver                    active
% 3.42/0.96  --res_prop_simpl_new                    false
% 3.42/0.96  --res_prop_simpl_given                  true
% 3.42/0.96  --res_passive_queue_type                priority_queues
% 3.42/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.42/0.96  --res_passive_queues_freq               [15;5]
% 3.42/0.96  --res_forward_subs                      full
% 3.42/0.96  --res_backward_subs                     full
% 3.42/0.96  --res_forward_subs_resolution           true
% 3.42/0.96  --res_backward_subs_resolution          true
% 3.42/0.96  --res_orphan_elimination                true
% 3.42/0.96  --res_time_limit                        2.
% 3.42/0.96  --res_out_proof                         true
% 3.42/0.96  
% 3.42/0.96  ------ Superposition Options
% 3.42/0.96  
% 3.42/0.96  --superposition_flag                    true
% 3.42/0.96  --sup_passive_queue_type                priority_queues
% 3.42/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.42/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.42/0.96  --demod_completeness_check              fast
% 3.42/0.96  --demod_use_ground                      true
% 3.42/0.96  --sup_to_prop_solver                    passive
% 3.42/0.96  --sup_prop_simpl_new                    true
% 3.42/0.96  --sup_prop_simpl_given                  true
% 3.42/0.96  --sup_fun_splitting                     false
% 3.42/0.96  --sup_smt_interval                      50000
% 3.42/0.96  
% 3.42/0.96  ------ Superposition Simplification Setup
% 3.42/0.96  
% 3.42/0.96  --sup_indices_passive                   []
% 3.42/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.42/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.96  --sup_full_bw                           [BwDemod]
% 3.42/0.96  --sup_immed_triv                        [TrivRules]
% 3.42/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.96  --sup_immed_bw_main                     []
% 3.42/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.42/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.96  
% 3.42/0.96  ------ Combination Options
% 3.42/0.96  
% 3.42/0.96  --comb_res_mult                         3
% 3.42/0.96  --comb_sup_mult                         2
% 3.42/0.96  --comb_inst_mult                        10
% 3.42/0.96  
% 3.42/0.96  ------ Debug Options
% 3.42/0.96  
% 3.42/0.96  --dbg_backtrace                         false
% 3.42/0.96  --dbg_dump_prop_clauses                 false
% 3.42/0.96  --dbg_dump_prop_clauses_file            -
% 3.42/0.96  --dbg_out_stat                          false
% 3.42/0.96  ------ Parsing...
% 3.42/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.42/0.96  
% 3.42/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.42/0.96  
% 3.42/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.42/0.96  
% 3.42/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.42/0.96  ------ Proving...
% 3.42/0.96  ------ Problem Properties 
% 3.42/0.96  
% 3.42/0.96  
% 3.42/0.96  clauses                                 20
% 3.42/0.96  conjectures                             4
% 3.42/0.96  EPR                                     2
% 3.42/0.96  Horn                                    18
% 3.42/0.96  unary                                   5
% 3.42/0.96  binary                                  3
% 3.42/0.96  lits                                    70
% 3.42/0.96  lits eq                                 13
% 3.42/0.96  fd_pure                                 0
% 3.42/0.96  fd_pseudo                               0
% 3.42/0.96  fd_cond                                 0
% 3.42/0.96  fd_pseudo_cond                          3
% 3.42/0.96  AC symbols                              0
% 3.42/0.96  
% 3.42/0.96  ------ Schedule dynamic 5 is on 
% 3.42/0.96  
% 3.42/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.42/0.96  
% 3.42/0.96  
% 3.42/0.96  ------ 
% 3.42/0.96  Current options:
% 3.42/0.96  ------ 
% 3.42/0.96  
% 3.42/0.96  ------ Input Options
% 3.42/0.96  
% 3.42/0.96  --out_options                           all
% 3.42/0.96  --tptp_safe_out                         true
% 3.42/0.96  --problem_path                          ""
% 3.42/0.96  --include_path                          ""
% 3.42/0.96  --clausifier                            res/vclausify_rel
% 3.42/0.96  --clausifier_options                    --mode clausify
% 3.42/0.96  --stdin                                 false
% 3.42/0.96  --stats_out                             all
% 3.42/0.96  
% 3.42/0.96  ------ General Options
% 3.42/0.96  
% 3.42/0.96  --fof                                   false
% 3.42/0.96  --time_out_real                         305.
% 3.42/0.96  --time_out_virtual                      -1.
% 3.42/0.96  --symbol_type_check                     false
% 3.42/0.96  --clausify_out                          false
% 3.42/0.96  --sig_cnt_out                           false
% 3.42/0.96  --trig_cnt_out                          false
% 3.42/0.96  --trig_cnt_out_tolerance                1.
% 3.42/0.96  --trig_cnt_out_sk_spl                   false
% 3.42/0.96  --abstr_cl_out                          false
% 3.42/0.96  
% 3.42/0.96  ------ Global Options
% 3.42/0.96  
% 3.42/0.96  --schedule                              default
% 3.42/0.96  --add_important_lit                     false
% 3.42/0.96  --prop_solver_per_cl                    1000
% 3.42/0.96  --min_unsat_core                        false
% 3.42/0.96  --soft_assumptions                      false
% 3.42/0.96  --soft_lemma_size                       3
% 3.42/0.96  --prop_impl_unit_size                   0
% 3.42/0.96  --prop_impl_unit                        []
% 3.42/0.96  --share_sel_clauses                     true
% 3.42/0.96  --reset_solvers                         false
% 3.42/0.96  --bc_imp_inh                            [conj_cone]
% 3.42/0.96  --conj_cone_tolerance                   3.
% 3.42/0.96  --extra_neg_conj                        none
% 3.42/0.96  --large_theory_mode                     true
% 3.42/0.96  --prolific_symb_bound                   200
% 3.42/0.96  --lt_threshold                          2000
% 3.42/0.96  --clause_weak_htbl                      true
% 3.42/0.96  --gc_record_bc_elim                     false
% 3.42/0.96  
% 3.42/0.96  ------ Preprocessing Options
% 3.42/0.96  
% 3.42/0.96  --preprocessing_flag                    true
% 3.42/0.96  --time_out_prep_mult                    0.1
% 3.42/0.96  --splitting_mode                        input
% 3.42/0.96  --splitting_grd                         true
% 3.42/0.96  --splitting_cvd                         false
% 3.42/0.96  --splitting_cvd_svl                     false
% 3.42/0.96  --splitting_nvd                         32
% 3.42/0.96  --sub_typing                            true
% 3.42/0.96  --prep_gs_sim                           true
% 3.42/0.96  --prep_unflatten                        true
% 3.42/0.96  --prep_res_sim                          true
% 3.42/0.96  --prep_upred                            true
% 3.42/0.96  --prep_sem_filter                       exhaustive
% 3.42/0.96  --prep_sem_filter_out                   false
% 3.42/0.96  --pred_elim                             true
% 3.42/0.96  --res_sim_input                         true
% 3.42/0.96  --eq_ax_congr_red                       true
% 3.42/0.96  --pure_diseq_elim                       true
% 3.42/0.96  --brand_transform                       false
% 3.42/0.96  --non_eq_to_eq                          false
% 3.42/0.96  --prep_def_merge                        true
% 3.42/0.96  --prep_def_merge_prop_impl              false
% 3.42/0.96  --prep_def_merge_mbd                    true
% 3.42/0.96  --prep_def_merge_tr_red                 false
% 3.42/0.96  --prep_def_merge_tr_cl                  false
% 3.42/0.96  --smt_preprocessing                     true
% 3.42/0.96  --smt_ac_axioms                         fast
% 3.42/0.96  --preprocessed_out                      false
% 3.42/0.96  --preprocessed_stats                    false
% 3.42/0.96  
% 3.42/0.96  ------ Abstraction refinement Options
% 3.42/0.96  
% 3.42/0.96  --abstr_ref                             []
% 3.42/0.96  --abstr_ref_prep                        false
% 3.42/0.96  --abstr_ref_until_sat                   false
% 3.42/0.96  --abstr_ref_sig_restrict                funpre
% 3.42/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.42/0.96  --abstr_ref_under                       []
% 3.42/0.96  
% 3.42/0.96  ------ SAT Options
% 3.42/0.96  
% 3.42/0.96  --sat_mode                              false
% 3.42/0.96  --sat_fm_restart_options                ""
% 3.42/0.96  --sat_gr_def                            false
% 3.42/0.96  --sat_epr_types                         true
% 3.42/0.96  --sat_non_cyclic_types                  false
% 3.42/0.96  --sat_finite_models                     false
% 3.42/0.96  --sat_fm_lemmas                         false
% 3.42/0.96  --sat_fm_prep                           false
% 3.42/0.96  --sat_fm_uc_incr                        true
% 3.42/0.96  --sat_out_model                         small
% 3.42/0.96  --sat_out_clauses                       false
% 3.42/0.96  
% 3.42/0.96  ------ QBF Options
% 3.42/0.96  
% 3.42/0.96  --qbf_mode                              false
% 3.42/0.96  --qbf_elim_univ                         false
% 3.42/0.96  --qbf_dom_inst                          none
% 3.42/0.96  --qbf_dom_pre_inst                      false
% 3.42/0.96  --qbf_sk_in                             false
% 3.42/0.96  --qbf_pred_elim                         true
% 3.42/0.96  --qbf_split                             512
% 3.42/0.96  
% 3.42/0.96  ------ BMC1 Options
% 3.42/0.96  
% 3.42/0.96  --bmc1_incremental                      false
% 3.42/0.96  --bmc1_axioms                           reachable_all
% 3.42/0.96  --bmc1_min_bound                        0
% 3.42/0.96  --bmc1_max_bound                        -1
% 3.42/0.96  --bmc1_max_bound_default                -1
% 3.42/0.96  --bmc1_symbol_reachability              true
% 3.42/0.96  --bmc1_property_lemmas                  false
% 3.42/0.96  --bmc1_k_induction                      false
% 3.42/0.96  --bmc1_non_equiv_states                 false
% 3.42/0.96  --bmc1_deadlock                         false
% 3.42/0.96  --bmc1_ucm                              false
% 3.42/0.96  --bmc1_add_unsat_core                   none
% 3.42/0.96  --bmc1_unsat_core_children              false
% 3.42/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.42/0.96  --bmc1_out_stat                         full
% 3.42/0.96  --bmc1_ground_init                      false
% 3.42/0.96  --bmc1_pre_inst_next_state              false
% 3.42/0.96  --bmc1_pre_inst_state                   false
% 3.42/0.96  --bmc1_pre_inst_reach_state             false
% 3.42/0.96  --bmc1_out_unsat_core                   false
% 3.42/0.96  --bmc1_aig_witness_out                  false
% 3.42/0.96  --bmc1_verbose                          false
% 3.42/0.96  --bmc1_dump_clauses_tptp                false
% 3.42/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.42/0.96  --bmc1_dump_file                        -
% 3.42/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.42/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.42/0.96  --bmc1_ucm_extend_mode                  1
% 3.42/0.96  --bmc1_ucm_init_mode                    2
% 3.42/0.96  --bmc1_ucm_cone_mode                    none
% 3.42/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.42/0.96  --bmc1_ucm_relax_model                  4
% 3.42/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.42/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.42/0.96  --bmc1_ucm_layered_model                none
% 3.42/0.96  --bmc1_ucm_max_lemma_size               10
% 3.42/0.96  
% 3.42/0.96  ------ AIG Options
% 3.42/0.96  
% 3.42/0.96  --aig_mode                              false
% 3.42/0.96  
% 3.42/0.96  ------ Instantiation Options
% 3.42/0.96  
% 3.42/0.96  --instantiation_flag                    true
% 3.42/0.96  --inst_sos_flag                         false
% 3.42/0.96  --inst_sos_phase                        true
% 3.42/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.42/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.42/0.96  --inst_lit_sel_side                     none
% 3.42/0.96  --inst_solver_per_active                1400
% 3.42/0.96  --inst_solver_calls_frac                1.
% 3.42/0.96  --inst_passive_queue_type               priority_queues
% 3.42/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.42/0.96  --inst_passive_queues_freq              [25;2]
% 3.42/0.96  --inst_dismatching                      true
% 3.42/0.96  --inst_eager_unprocessed_to_passive     true
% 3.42/0.96  --inst_prop_sim_given                   true
% 3.42/0.96  --inst_prop_sim_new                     false
% 3.42/0.96  --inst_subs_new                         false
% 3.42/0.96  --inst_eq_res_simp                      false
% 3.42/0.96  --inst_subs_given                       false
% 3.42/0.96  --inst_orphan_elimination               true
% 3.42/0.96  --inst_learning_loop_flag               true
% 3.42/0.96  --inst_learning_start                   3000
% 3.42/0.96  --inst_learning_factor                  2
% 3.42/0.96  --inst_start_prop_sim_after_learn       3
% 3.42/0.96  --inst_sel_renew                        solver
% 3.42/0.96  --inst_lit_activity_flag                true
% 3.42/0.96  --inst_restr_to_given                   false
% 3.42/0.96  --inst_activity_threshold               500
% 3.42/0.96  --inst_out_proof                        true
% 3.42/0.96  
% 3.42/0.96  ------ Resolution Options
% 3.42/0.96  
% 3.42/0.96  --resolution_flag                       false
% 3.42/0.96  --res_lit_sel                           adaptive
% 3.42/0.96  --res_lit_sel_side                      none
% 3.42/0.96  --res_ordering                          kbo
% 3.42/0.96  --res_to_prop_solver                    active
% 3.42/0.96  --res_prop_simpl_new                    false
% 3.42/0.96  --res_prop_simpl_given                  true
% 3.42/0.96  --res_passive_queue_type                priority_queues
% 3.42/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.42/0.96  --res_passive_queues_freq               [15;5]
% 3.42/0.96  --res_forward_subs                      full
% 3.42/0.96  --res_backward_subs                     full
% 3.42/0.96  --res_forward_subs_resolution           true
% 3.42/0.96  --res_backward_subs_resolution          true
% 3.42/0.96  --res_orphan_elimination                true
% 3.42/0.96  --res_time_limit                        2.
% 3.42/0.96  --res_out_proof                         true
% 3.42/0.96  
% 3.42/0.96  ------ Superposition Options
% 3.42/0.96  
% 3.42/0.96  --superposition_flag                    true
% 3.42/0.96  --sup_passive_queue_type                priority_queues
% 3.42/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.42/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.42/0.96  --demod_completeness_check              fast
% 3.42/0.96  --demod_use_ground                      true
% 3.42/0.96  --sup_to_prop_solver                    passive
% 3.42/0.96  --sup_prop_simpl_new                    true
% 3.42/0.96  --sup_prop_simpl_given                  true
% 3.42/0.96  --sup_fun_splitting                     false
% 3.42/0.96  --sup_smt_interval                      50000
% 3.42/0.96  
% 3.42/0.96  ------ Superposition Simplification Setup
% 3.42/0.96  
% 3.42/0.96  --sup_indices_passive                   []
% 3.42/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.42/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.42/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.96  --sup_full_bw                           [BwDemod]
% 3.42/0.96  --sup_immed_triv                        [TrivRules]
% 3.42/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.96  --sup_immed_bw_main                     []
% 3.42/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.42/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.42/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.42/0.96  
% 3.42/0.96  ------ Combination Options
% 3.42/0.96  
% 3.42/0.96  --comb_res_mult                         3
% 3.42/0.96  --comb_sup_mult                         2
% 3.42/0.96  --comb_inst_mult                        10
% 3.42/0.96  
% 3.42/0.96  ------ Debug Options
% 3.42/0.96  
% 3.42/0.96  --dbg_backtrace                         false
% 3.42/0.96  --dbg_dump_prop_clauses                 false
% 3.42/0.96  --dbg_dump_prop_clauses_file            -
% 3.42/0.96  --dbg_out_stat                          false
% 3.42/0.96  
% 3.42/0.96  
% 3.42/0.96  
% 3.42/0.96  
% 3.42/0.96  ------ Proving...
% 3.42/0.96  
% 3.42/0.96  
% 3.42/0.96  % SZS status Theorem for theBenchmark.p
% 3.42/0.96  
% 3.42/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.42/0.96  
% 3.42/0.96  fof(f7,conjecture,(
% 3.42/0.96    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 3.42/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.96  
% 3.42/0.96  fof(f8,negated_conjecture,(
% 3.42/0.96    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 3.42/0.96    inference(negated_conjecture,[],[f7])).
% 3.42/0.96  
% 3.42/0.96  fof(f21,plain,(
% 3.42/0.96    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.42/0.96    inference(ennf_transformation,[],[f8])).
% 3.42/0.96  
% 3.42/0.96  fof(f22,plain,(
% 3.42/0.96    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.42/0.96    inference(flattening,[],[f21])).
% 3.42/0.96  
% 3.42/0.96  fof(f31,plain,(
% 3.42/0.96    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3 | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3) & r2_hidden(sK3,k2_relat_1(sK4)) & v2_funct_1(sK4) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 3.42/0.96    introduced(choice_axiom,[])).
% 3.42/0.96  
% 3.42/0.96  fof(f32,plain,(
% 3.42/0.96    (k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3 | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3) & r2_hidden(sK3,k2_relat_1(sK4)) & v2_funct_1(sK4) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 3.42/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f22,f31])).
% 3.42/0.96  
% 3.42/0.96  fof(f52,plain,(
% 3.42/0.96    r2_hidden(sK3,k2_relat_1(sK4))),
% 3.42/0.96    inference(cnf_transformation,[],[f32])).
% 3.42/0.96  
% 3.42/0.96  fof(f1,axiom,(
% 3.42/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.42/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.96  
% 3.42/0.96  fof(f9,plain,(
% 3.42/0.96    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.42/0.96    inference(ennf_transformation,[],[f1])).
% 3.42/0.96  
% 3.42/0.96  fof(f10,plain,(
% 3.42/0.96    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.42/0.96    inference(flattening,[],[f9])).
% 3.42/0.96  
% 3.42/0.96  fof(f23,plain,(
% 3.42/0.96    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.42/0.96    inference(nnf_transformation,[],[f10])).
% 3.42/0.96  
% 3.42/0.96  fof(f24,plain,(
% 3.42/0.96    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.42/0.96    inference(rectify,[],[f23])).
% 3.42/0.96  
% 3.42/0.96  fof(f27,plain,(
% 3.42/0.96    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))))),
% 3.42/0.96    introduced(choice_axiom,[])).
% 3.42/0.96  
% 3.42/0.96  fof(f26,plain,(
% 3.42/0.96    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) = X2 & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))) )),
% 3.42/0.96    introduced(choice_axiom,[])).
% 3.42/0.96  
% 3.42/0.96  fof(f25,plain,(
% 3.42/0.96    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK0(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1))))),
% 3.42/0.96    introduced(choice_axiom,[])).
% 3.42/0.96  
% 3.42/0.96  fof(f28,plain,(
% 3.42/0.96    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & ((k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.42/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).
% 3.42/0.96  
% 3.42/0.96  fof(f33,plain,(
% 3.42/0.96    ( ! [X0,X5,X1] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.42/0.96    inference(cnf_transformation,[],[f28])).
% 3.42/0.96  
% 3.42/0.96  fof(f57,plain,(
% 3.42/0.96    ( ! [X0,X5] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.42/0.96    inference(equality_resolution,[],[f33])).
% 3.42/0.96  
% 3.42/0.96  fof(f6,axiom,(
% 3.42/0.96    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 3.42/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.96  
% 3.42/0.96  fof(f19,plain,(
% 3.42/0.96    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.42/0.96    inference(ennf_transformation,[],[f6])).
% 3.42/0.96  
% 3.42/0.96  fof(f20,plain,(
% 3.42/0.96    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.42/0.96    inference(flattening,[],[f19])).
% 3.42/0.96  
% 3.42/0.96  fof(f47,plain,(
% 3.42/0.96    ( ! [X0,X1] : (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.42/0.96    inference(cnf_transformation,[],[f20])).
% 3.42/0.96  
% 3.42/0.96  fof(f51,plain,(
% 3.42/0.96    v2_funct_1(sK4)),
% 3.42/0.96    inference(cnf_transformation,[],[f32])).
% 3.42/0.96  
% 3.42/0.96  fof(f49,plain,(
% 3.42/0.96    v1_relat_1(sK4)),
% 3.42/0.96    inference(cnf_transformation,[],[f32])).
% 3.42/0.96  
% 3.42/0.96  fof(f50,plain,(
% 3.42/0.96    v1_funct_1(sK4)),
% 3.42/0.96    inference(cnf_transformation,[],[f32])).
% 3.42/0.96  
% 3.42/0.96  fof(f34,plain,(
% 3.42/0.96    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.42/0.96    inference(cnf_transformation,[],[f28])).
% 3.42/0.96  
% 3.42/0.96  fof(f56,plain,(
% 3.42/0.96    ( ! [X0,X5] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.42/0.96    inference(equality_resolution,[],[f34])).
% 3.42/0.96  
% 3.42/0.96  fof(f3,axiom,(
% 3.42/0.96    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 3.42/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.96  
% 3.42/0.96  fof(f13,plain,(
% 3.42/0.96    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.42/0.96    inference(ennf_transformation,[],[f3])).
% 3.42/0.96  
% 3.42/0.96  fof(f14,plain,(
% 3.42/0.96    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.42/0.96    inference(flattening,[],[f13])).
% 3.42/0.96  
% 3.42/0.96  fof(f29,plain,(
% 3.42/0.96    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.42/0.96    inference(nnf_transformation,[],[f14])).
% 3.42/0.96  
% 3.42/0.96  fof(f30,plain,(
% 3.42/0.96    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.42/0.96    inference(flattening,[],[f29])).
% 3.42/0.96  
% 3.42/0.96  fof(f43,plain,(
% 3.42/0.96    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.42/0.96    inference(cnf_transformation,[],[f30])).
% 3.42/0.96  
% 3.42/0.96  fof(f5,axiom,(
% 3.42/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.42/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.96  
% 3.42/0.96  fof(f17,plain,(
% 3.42/0.96    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.42/0.96    inference(ennf_transformation,[],[f5])).
% 3.42/0.96  
% 3.42/0.96  fof(f18,plain,(
% 3.42/0.96    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.42/0.96    inference(flattening,[],[f17])).
% 3.42/0.96  
% 3.42/0.96  fof(f45,plain,(
% 3.42/0.96    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.42/0.96    inference(cnf_transformation,[],[f18])).
% 3.42/0.96  
% 3.42/0.96  fof(f2,axiom,(
% 3.42/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.42/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.96  
% 3.42/0.96  fof(f11,plain,(
% 3.42/0.96    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.42/0.96    inference(ennf_transformation,[],[f2])).
% 3.42/0.96  
% 3.42/0.96  fof(f12,plain,(
% 3.42/0.96    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.42/0.96    inference(flattening,[],[f11])).
% 3.42/0.96  
% 3.42/0.96  fof(f39,plain,(
% 3.42/0.96    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.42/0.96    inference(cnf_transformation,[],[f12])).
% 3.42/0.96  
% 3.42/0.96  fof(f40,plain,(
% 3.42/0.96    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.42/0.96    inference(cnf_transformation,[],[f12])).
% 3.42/0.96  
% 3.42/0.96  fof(f4,axiom,(
% 3.42/0.96    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0))))),
% 3.42/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.42/0.96  
% 3.42/0.96  fof(f15,plain,(
% 3.42/0.96    ! [X0,X1] : (! [X2] : ((k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.42/0.96    inference(ennf_transformation,[],[f4])).
% 3.42/0.96  
% 3.42/0.96  fof(f16,plain,(
% 3.42/0.96    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.42/0.96    inference(flattening,[],[f15])).
% 3.42/0.96  
% 3.42/0.96  fof(f44,plain,(
% 3.42/0.96    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.42/0.96    inference(cnf_transformation,[],[f16])).
% 3.42/0.96  
% 3.42/0.96  fof(f53,plain,(
% 3.42/0.96    k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3 | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3),
% 3.42/0.96    inference(cnf_transformation,[],[f32])).
% 3.42/0.96  
% 3.42/0.96  cnf(c_17,negated_conjecture,
% 3.42/0.96      ( r2_hidden(sK3,k2_relat_1(sK4)) ),
% 3.42/0.96      inference(cnf_transformation,[],[f52]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_706,plain,
% 3.42/0.96      ( r2_hidden(sK3,k2_relat_1(sK4)) = iProver_top ),
% 3.42/0.96      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_5,plain,
% 3.42/0.96      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.42/0.96      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 3.42/0.96      | ~ v1_relat_1(X1)
% 3.42/0.96      | ~ v1_funct_1(X1) ),
% 3.42/0.96      inference(cnf_transformation,[],[f57]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_713,plain,
% 3.42/0.96      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.42/0.96      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.42/0.96      | v1_relat_1(X1) != iProver_top
% 3.42/0.96      | v1_funct_1(X1) != iProver_top ),
% 3.42/0.96      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_15,plain,
% 3.42/0.96      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.42/0.96      | ~ v2_funct_1(X1)
% 3.42/0.96      | ~ v1_relat_1(X1)
% 3.42/0.96      | ~ v1_funct_1(X1)
% 3.42/0.96      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
% 3.42/0.96      inference(cnf_transformation,[],[f47]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_18,negated_conjecture,
% 3.42/0.96      ( v2_funct_1(sK4) ),
% 3.42/0.96      inference(cnf_transformation,[],[f51]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_241,plain,
% 3.42/0.96      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.42/0.96      | ~ v1_relat_1(X1)
% 3.42/0.96      | ~ v1_funct_1(X1)
% 3.42/0.96      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
% 3.42/0.96      | sK4 != X1 ),
% 3.42/0.96      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_242,plain,
% 3.42/0.96      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.42/0.96      | ~ v1_relat_1(sK4)
% 3.42/0.96      | ~ v1_funct_1(sK4)
% 3.42/0.96      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
% 3.42/0.96      inference(unflattening,[status(thm)],[c_241]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_20,negated_conjecture,
% 3.42/0.96      ( v1_relat_1(sK4) ),
% 3.42/0.96      inference(cnf_transformation,[],[f49]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_19,negated_conjecture,
% 3.42/0.96      ( v1_funct_1(sK4) ),
% 3.42/0.96      inference(cnf_transformation,[],[f50]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_246,plain,
% 3.42/0.96      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.42/0.96      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
% 3.42/0.96      inference(global_propositional_subsumption,
% 3.42/0.96                [status(thm)],
% 3.42/0.96                [c_242,c_20,c_19]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_703,plain,
% 3.42/0.96      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0
% 3.42/0.96      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.42/0.96      inference(predicate_to_equality,[status(thm)],[c_246]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_1317,plain,
% 3.42/0.96      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK2(sK4,X0))) = sK2(sK4,X0)
% 3.42/0.96      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 3.42/0.96      | v1_relat_1(sK4) != iProver_top
% 3.42/0.96      | v1_funct_1(sK4) != iProver_top ),
% 3.42/0.96      inference(superposition,[status(thm)],[c_713,c_703]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_21,plain,
% 3.42/0.96      ( v1_relat_1(sK4) = iProver_top ),
% 3.42/0.96      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_22,plain,
% 3.42/0.96      ( v1_funct_1(sK4) = iProver_top ),
% 3.42/0.96      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_1660,plain,
% 3.42/0.96      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK2(sK4,X0))) = sK2(sK4,X0)
% 3.42/0.96      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 3.42/0.96      inference(global_propositional_subsumption,
% 3.42/0.96                [status(thm)],
% 3.42/0.96                [c_1317,c_21,c_22]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_1668,plain,
% 3.42/0.96      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK2(sK4,sK3))) = sK2(sK4,sK3) ),
% 3.42/0.96      inference(superposition,[status(thm)],[c_706,c_1660]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_4,plain,
% 3.42/0.96      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.42/0.96      | ~ v1_relat_1(X1)
% 3.42/0.96      | ~ v1_funct_1(X1)
% 3.42/0.96      | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
% 3.42/0.96      inference(cnf_transformation,[],[f56]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_714,plain,
% 3.42/0.96      ( k1_funct_1(X0,sK2(X0,X1)) = X1
% 3.42/0.96      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.42/0.96      | v1_relat_1(X0) != iProver_top
% 3.42/0.96      | v1_funct_1(X0) != iProver_top ),
% 3.42/0.96      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_1222,plain,
% 3.42/0.96      ( k1_funct_1(sK4,sK2(sK4,sK3)) = sK3
% 3.42/0.96      | v1_relat_1(sK4) != iProver_top
% 3.42/0.96      | v1_funct_1(sK4) != iProver_top ),
% 3.42/0.96      inference(superposition,[status(thm)],[c_706,c_714]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_905,plain,
% 3.42/0.96      ( ~ r2_hidden(sK3,k2_relat_1(sK4))
% 3.42/0.96      | ~ v1_relat_1(sK4)
% 3.42/0.96      | ~ v1_funct_1(sK4)
% 3.42/0.96      | k1_funct_1(sK4,sK2(sK4,sK3)) = sK3 ),
% 3.42/0.96      inference(instantiation,[status(thm)],[c_4]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_1373,plain,
% 3.42/0.96      ( k1_funct_1(sK4,sK2(sK4,sK3)) = sK3 ),
% 3.42/0.96      inference(global_propositional_subsumption,
% 3.42/0.96                [status(thm)],
% 3.42/0.96                [c_1222,c_20,c_19,c_17,c_905]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_1675,plain,
% 3.42/0.96      ( k1_funct_1(k2_funct_1(sK4),sK3) = sK2(sK4,sK3) ),
% 3.42/0.96      inference(light_normalisation,[status(thm)],[c_1668,c_1373]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_8,plain,
% 3.42/0.96      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.42/0.96      | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 3.42/0.96      | ~ r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2))
% 3.42/0.96      | ~ v1_relat_1(X2)
% 3.42/0.96      | ~ v1_relat_1(X1)
% 3.42/0.96      | ~ v1_funct_1(X2)
% 3.42/0.96      | ~ v1_funct_1(X1) ),
% 3.42/0.96      inference(cnf_transformation,[],[f43]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_710,plain,
% 3.42/0.96      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.42/0.96      | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2))) = iProver_top
% 3.42/0.96      | r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2)) != iProver_top
% 3.42/0.96      | v1_relat_1(X1) != iProver_top
% 3.42/0.96      | v1_relat_1(X2) != iProver_top
% 3.42/0.96      | v1_funct_1(X1) != iProver_top
% 3.42/0.96      | v1_funct_1(X2) != iProver_top ),
% 3.42/0.96      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_3735,plain,
% 3.42/0.96      ( r2_hidden(sK2(sK4,sK3),k1_relat_1(X0)) != iProver_top
% 3.42/0.96      | r2_hidden(sK3,k1_relat_1(k5_relat_1(k2_funct_1(sK4),X0))) = iProver_top
% 3.42/0.96      | r2_hidden(sK3,k1_relat_1(k2_funct_1(sK4))) != iProver_top
% 3.42/0.96      | v1_relat_1(X0) != iProver_top
% 3.42/0.96      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 3.42/0.96      | v1_funct_1(X0) != iProver_top
% 3.42/0.96      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.42/0.96      inference(superposition,[status(thm)],[c_1675,c_710]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_13,plain,
% 3.42/0.96      ( ~ v2_funct_1(X0)
% 3.42/0.96      | ~ v1_relat_1(X0)
% 3.42/0.96      | ~ v1_funct_1(X0)
% 3.42/0.96      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.42/0.96      inference(cnf_transformation,[],[f45]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_225,plain,
% 3.42/0.96      ( ~ v1_relat_1(X0)
% 3.42/0.96      | ~ v1_funct_1(X0)
% 3.42/0.96      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.42/0.96      | sK4 != X0 ),
% 3.42/0.96      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_226,plain,
% 3.42/0.96      ( ~ v1_relat_1(sK4)
% 3.42/0.96      | ~ v1_funct_1(sK4)
% 3.42/0.96      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.42/0.96      inference(unflattening,[status(thm)],[c_225]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_32,plain,
% 3.42/0.96      ( ~ v2_funct_1(sK4)
% 3.42/0.96      | ~ v1_relat_1(sK4)
% 3.42/0.96      | ~ v1_funct_1(sK4)
% 3.42/0.96      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.42/0.96      inference(instantiation,[status(thm)],[c_13]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_228,plain,
% 3.42/0.96      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.42/0.96      inference(global_propositional_subsumption,
% 3.42/0.96                [status(thm)],
% 3.42/0.96                [c_226,c_20,c_19,c_18,c_32]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_3820,plain,
% 3.42/0.96      ( r2_hidden(sK2(sK4,sK3),k1_relat_1(X0)) != iProver_top
% 3.42/0.96      | r2_hidden(sK3,k1_relat_1(k5_relat_1(k2_funct_1(sK4),X0))) = iProver_top
% 3.42/0.96      | r2_hidden(sK3,k2_relat_1(sK4)) != iProver_top
% 3.42/0.96      | v1_relat_1(X0) != iProver_top
% 3.42/0.96      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 3.42/0.96      | v1_funct_1(X0) != iProver_top
% 3.42/0.96      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.42/0.96      inference(light_normalisation,[status(thm)],[c_3735,c_228]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_24,plain,
% 3.42/0.96      ( r2_hidden(sK3,k2_relat_1(sK4)) = iProver_top ),
% 3.42/0.96      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_7,plain,
% 3.42/0.96      ( ~ v1_relat_1(X0)
% 3.42/0.96      | v1_relat_1(k2_funct_1(X0))
% 3.42/0.96      | ~ v1_funct_1(X0) ),
% 3.42/0.96      inference(cnf_transformation,[],[f39]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_49,plain,
% 3.42/0.96      ( v1_relat_1(X0) != iProver_top
% 3.42/0.96      | v1_relat_1(k2_funct_1(X0)) = iProver_top
% 3.42/0.96      | v1_funct_1(X0) != iProver_top ),
% 3.42/0.96      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_51,plain,
% 3.42/0.96      ( v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 3.42/0.96      | v1_relat_1(sK4) != iProver_top
% 3.42/0.96      | v1_funct_1(sK4) != iProver_top ),
% 3.42/0.96      inference(instantiation,[status(thm)],[c_49]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_6,plain,
% 3.42/0.96      ( ~ v1_relat_1(X0)
% 3.42/0.96      | ~ v1_funct_1(X0)
% 3.42/0.96      | v1_funct_1(k2_funct_1(X0)) ),
% 3.42/0.96      inference(cnf_transformation,[],[f40]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_52,plain,
% 3.42/0.96      ( v1_relat_1(X0) != iProver_top
% 3.42/0.96      | v1_funct_1(X0) != iProver_top
% 3.42/0.96      | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
% 3.42/0.96      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_54,plain,
% 3.42/0.96      ( v1_relat_1(sK4) != iProver_top
% 3.42/0.96      | v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 3.42/0.96      | v1_funct_1(sK4) != iProver_top ),
% 3.42/0.96      inference(instantiation,[status(thm)],[c_52]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_4619,plain,
% 3.42/0.96      ( v1_funct_1(X0) != iProver_top
% 3.42/0.96      | r2_hidden(sK3,k1_relat_1(k5_relat_1(k2_funct_1(sK4),X0))) = iProver_top
% 3.42/0.96      | r2_hidden(sK2(sK4,sK3),k1_relat_1(X0)) != iProver_top
% 3.42/0.96      | v1_relat_1(X0) != iProver_top ),
% 3.42/0.96      inference(global_propositional_subsumption,
% 3.42/0.96                [status(thm)],
% 3.42/0.96                [c_3820,c_21,c_22,c_24,c_51,c_54]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_4620,plain,
% 3.42/0.96      ( r2_hidden(sK2(sK4,sK3),k1_relat_1(X0)) != iProver_top
% 3.42/0.96      | r2_hidden(sK3,k1_relat_1(k5_relat_1(k2_funct_1(sK4),X0))) = iProver_top
% 3.42/0.96      | v1_relat_1(X0) != iProver_top
% 3.42/0.96      | v1_funct_1(X0) != iProver_top ),
% 3.42/0.96      inference(renaming,[status(thm)],[c_4619]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_11,plain,
% 3.42/0.96      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 3.42/0.96      | ~ v1_relat_1(X2)
% 3.42/0.96      | ~ v1_relat_1(X1)
% 3.42/0.96      | ~ v1_funct_1(X2)
% 3.42/0.96      | ~ v1_funct_1(X1)
% 3.42/0.96      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 3.42/0.96      inference(cnf_transformation,[],[f44]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_707,plain,
% 3.42/0.96      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 3.42/0.96      | r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
% 3.42/0.96      | v1_relat_1(X0) != iProver_top
% 3.42/0.96      | v1_relat_1(X1) != iProver_top
% 3.42/0.96      | v1_funct_1(X0) != iProver_top
% 3.42/0.96      | v1_funct_1(X1) != iProver_top ),
% 3.42/0.96      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_4632,plain,
% 3.42/0.96      ( k1_funct_1(X0,k1_funct_1(k2_funct_1(sK4),sK3)) = k1_funct_1(k5_relat_1(k2_funct_1(sK4),X0),sK3)
% 3.42/0.96      | r2_hidden(sK2(sK4,sK3),k1_relat_1(X0)) != iProver_top
% 3.42/0.96      | v1_relat_1(X0) != iProver_top
% 3.42/0.96      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 3.42/0.96      | v1_funct_1(X0) != iProver_top
% 3.42/0.96      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.42/0.96      inference(superposition,[status(thm)],[c_4620,c_707]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_4639,plain,
% 3.42/0.96      ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),X0),sK3) = k1_funct_1(X0,sK2(sK4,sK3))
% 3.42/0.96      | r2_hidden(sK2(sK4,sK3),k1_relat_1(X0)) != iProver_top
% 3.42/0.96      | v1_relat_1(X0) != iProver_top
% 3.42/0.96      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 3.42/0.96      | v1_funct_1(X0) != iProver_top
% 3.42/0.96      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.42/0.96      inference(light_normalisation,[status(thm)],[c_4632,c_1675]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_4676,plain,
% 3.42/0.96      ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = k1_funct_1(sK4,sK2(sK4,sK3))
% 3.42/0.96      | r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4)) != iProver_top
% 3.42/0.96      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 3.42/0.96      | v1_relat_1(sK4) != iProver_top
% 3.42/0.96      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.42/0.96      | v1_funct_1(sK4) != iProver_top ),
% 3.42/0.96      inference(instantiation,[status(thm)],[c_4639]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_16,negated_conjecture,
% 3.42/0.96      ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
% 3.42/0.96      | k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),sK3)) != sK3 ),
% 3.42/0.96      inference(cnf_transformation,[],[f53]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_1681,plain,
% 3.42/0.96      ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
% 3.42/0.96      | k1_funct_1(sK4,sK2(sK4,sK3)) != sK3 ),
% 3.42/0.96      inference(demodulation,[status(thm)],[c_1675,c_16]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_1682,plain,
% 3.42/0.96      ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3
% 3.42/0.96      | sK3 != sK3 ),
% 3.42/0.96      inference(light_normalisation,[status(thm)],[c_1681,c_1373]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_1683,plain,
% 3.42/0.96      ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != sK3 ),
% 3.42/0.96      inference(equality_resolution_simp,[status(thm)],[c_1682]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_402,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_900,plain,
% 3.42/0.96      ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != X0
% 3.42/0.96      | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = sK3
% 3.42/0.96      | sK3 != X0 ),
% 3.42/0.96      inference(instantiation,[status(thm)],[c_402]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_1560,plain,
% 3.42/0.96      ( k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) != k1_funct_1(sK4,sK2(sK4,sK3))
% 3.42/0.96      | k1_funct_1(k5_relat_1(k2_funct_1(sK4),sK4),sK3) = sK3
% 3.42/0.96      | sK3 != k1_funct_1(sK4,sK2(sK4,sK3)) ),
% 3.42/0.96      inference(instantiation,[status(thm)],[c_900]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_939,plain,
% 3.42/0.96      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.42/0.96      inference(instantiation,[status(thm)],[c_402]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_1108,plain,
% 3.42/0.96      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.42/0.96      inference(instantiation,[status(thm)],[c_939]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_1508,plain,
% 3.42/0.96      ( k1_funct_1(sK4,sK2(sK4,sK3)) != sK3
% 3.42/0.96      | sK3 = k1_funct_1(sK4,sK2(sK4,sK3))
% 3.42/0.96      | sK3 != sK3 ),
% 3.42/0.96      inference(instantiation,[status(thm)],[c_1108]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_401,plain,( X0 = X0 ),theory(equality) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_957,plain,
% 3.42/0.96      ( sK3 = sK3 ),
% 3.42/0.96      inference(instantiation,[status(thm)],[c_401]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_902,plain,
% 3.42/0.96      ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4))
% 3.42/0.96      | ~ r2_hidden(sK3,k2_relat_1(sK4))
% 3.42/0.96      | ~ v1_relat_1(sK4)
% 3.42/0.96      | ~ v1_funct_1(sK4) ),
% 3.42/0.96      inference(instantiation,[status(thm)],[c_5]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(c_903,plain,
% 3.42/0.96      ( r2_hidden(sK2(sK4,sK3),k1_relat_1(sK4)) = iProver_top
% 3.42/0.96      | r2_hidden(sK3,k2_relat_1(sK4)) != iProver_top
% 3.42/0.96      | v1_relat_1(sK4) != iProver_top
% 3.42/0.96      | v1_funct_1(sK4) != iProver_top ),
% 3.42/0.96      inference(predicate_to_equality,[status(thm)],[c_902]) ).
% 3.42/0.96  
% 3.42/0.96  cnf(contradiction,plain,
% 3.42/0.96      ( $false ),
% 3.42/0.96      inference(minisat,
% 3.42/0.96                [status(thm)],
% 3.42/0.96                [c_4676,c_1683,c_1560,c_1508,c_957,c_905,c_903,c_54,c_51,
% 3.42/0.96                 c_24,c_17,c_22,c_19,c_21,c_20]) ).
% 3.42/0.96  
% 3.42/0.96  
% 3.42/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.42/0.96  
% 3.42/0.96  ------                               Statistics
% 3.42/0.96  
% 3.42/0.96  ------ General
% 3.42/0.96  
% 3.42/0.96  abstr_ref_over_cycles:                  0
% 3.42/0.96  abstr_ref_under_cycles:                 0
% 3.42/0.96  gc_basic_clause_elim:                   0
% 3.42/0.96  forced_gc_time:                         0
% 3.42/0.96  parsing_time:                           0.006
% 3.42/0.96  unif_index_cands_time:                  0.
% 3.42/0.96  unif_index_add_time:                    0.
% 3.42/0.96  orderings_time:                         0.
% 3.42/0.96  out_proof_time:                         0.008
% 3.42/0.96  total_time:                             0.15
% 3.42/0.96  num_of_symbols:                         45
% 3.42/0.96  num_of_terms:                           3943
% 3.42/0.96  
% 3.42/0.96  ------ Preprocessing
% 3.42/0.96  
% 3.42/0.96  num_of_splits:                          0
% 3.42/0.96  num_of_split_atoms:                     0
% 3.42/0.96  num_of_reused_defs:                     0
% 3.42/0.96  num_eq_ax_congr_red:                    18
% 3.42/0.96  num_of_sem_filtered_clauses:            1
% 3.42/0.96  num_of_subtypes:                        0
% 3.42/0.96  monotx_restored_types:                  0
% 3.42/0.96  sat_num_of_epr_types:                   0
% 3.42/0.96  sat_num_of_non_cyclic_types:            0
% 3.42/0.96  sat_guarded_non_collapsed_types:        0
% 3.42/0.96  num_pure_diseq_elim:                    0
% 3.42/0.96  simp_replaced_by:                       0
% 3.42/0.96  res_preprocessed:                       102
% 3.42/0.96  prep_upred:                             0
% 3.42/0.96  prep_unflattend:                        4
% 3.42/0.96  smt_new_axioms:                         0
% 3.42/0.96  pred_elim_cands:                        3
% 3.42/0.96  pred_elim:                              1
% 3.42/0.96  pred_elim_cl:                           1
% 3.42/0.96  pred_elim_cycles:                       3
% 3.42/0.96  merged_defs:                            0
% 3.42/0.96  merged_defs_ncl:                        0
% 3.42/0.96  bin_hyper_res:                          0
% 3.42/0.96  prep_cycles:                            4
% 3.42/0.96  pred_elim_time:                         0.001
% 3.42/0.96  splitting_time:                         0.
% 3.42/0.96  sem_filter_time:                        0.
% 3.42/0.96  monotx_time:                            0.
% 3.42/0.96  subtype_inf_time:                       0.
% 3.42/0.96  
% 3.42/0.96  ------ Problem properties
% 3.42/0.96  
% 3.42/0.96  clauses:                                20
% 3.42/0.96  conjectures:                            4
% 3.42/0.96  epr:                                    2
% 3.42/0.96  horn:                                   18
% 3.42/0.96  ground:                                 6
% 3.42/0.96  unary:                                  5
% 3.42/0.96  binary:                                 3
% 3.42/0.96  lits:                                   70
% 3.42/0.96  lits_eq:                                13
% 3.42/0.96  fd_pure:                                0
% 3.42/0.96  fd_pseudo:                              0
% 3.42/0.96  fd_cond:                                0
% 3.42/0.96  fd_pseudo_cond:                         3
% 3.42/0.96  ac_symbols:                             0
% 3.42/0.96  
% 3.42/0.96  ------ Propositional Solver
% 3.42/0.96  
% 3.42/0.96  prop_solver_calls:                      26
% 3.42/0.96  prop_fast_solver_calls:                 897
% 3.42/0.96  smt_solver_calls:                       0
% 3.42/0.96  smt_fast_solver_calls:                  0
% 3.42/0.96  prop_num_of_clauses:                    1617
% 3.42/0.96  prop_preprocess_simplified:             4678
% 3.42/0.96  prop_fo_subsumed:                       40
% 3.42/0.96  prop_solver_time:                       0.
% 3.42/0.96  smt_solver_time:                        0.
% 3.42/0.96  smt_fast_solver_time:                   0.
% 3.42/0.96  prop_fast_solver_time:                  0.
% 3.42/0.96  prop_unsat_core_time:                   0.
% 3.42/0.96  
% 3.42/0.96  ------ QBF
% 3.42/0.96  
% 3.42/0.96  qbf_q_res:                              0
% 3.42/0.96  qbf_num_tautologies:                    0
% 3.42/0.96  qbf_prep_cycles:                        0
% 3.42/0.96  
% 3.42/0.96  ------ BMC1
% 3.42/0.96  
% 3.42/0.96  bmc1_current_bound:                     -1
% 3.42/0.96  bmc1_last_solved_bound:                 -1
% 3.42/0.96  bmc1_unsat_core_size:                   -1
% 3.42/0.96  bmc1_unsat_core_parents_size:           -1
% 3.42/0.96  bmc1_merge_next_fun:                    0
% 3.42/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.42/0.96  
% 3.42/0.96  ------ Instantiation
% 3.42/0.96  
% 3.42/0.96  inst_num_of_clauses:                    424
% 3.42/0.96  inst_num_in_passive:                    71
% 3.42/0.96  inst_num_in_active:                     199
% 3.42/0.96  inst_num_in_unprocessed:                154
% 3.42/0.96  inst_num_of_loops:                      220
% 3.42/0.96  inst_num_of_learning_restarts:          0
% 3.42/0.96  inst_num_moves_active_passive:          18
% 3.42/0.96  inst_lit_activity:                      0
% 3.42/0.96  inst_lit_activity_moves:                0
% 3.42/0.96  inst_num_tautologies:                   0
% 3.42/0.96  inst_num_prop_implied:                  0
% 3.42/0.96  inst_num_existing_simplified:           0
% 3.42/0.96  inst_num_eq_res_simplified:             0
% 3.42/0.96  inst_num_child_elim:                    0
% 3.42/0.96  inst_num_of_dismatching_blockings:      86
% 3.42/0.96  inst_num_of_non_proper_insts:           335
% 3.42/0.96  inst_num_of_duplicates:                 0
% 3.42/0.96  inst_inst_num_from_inst_to_res:         0
% 3.42/0.96  inst_dismatching_checking_time:         0.
% 3.42/0.96  
% 3.42/0.96  ------ Resolution
% 3.42/0.96  
% 3.42/0.96  res_num_of_clauses:                     0
% 3.42/0.96  res_num_in_passive:                     0
% 3.42/0.96  res_num_in_active:                      0
% 3.42/0.96  res_num_of_loops:                       106
% 3.42/0.96  res_forward_subset_subsumed:            27
% 3.42/0.96  res_backward_subset_subsumed:           0
% 3.42/0.96  res_forward_subsumed:                   0
% 3.42/0.96  res_backward_subsumed:                  0
% 3.42/0.96  res_forward_subsumption_resolution:     0
% 3.42/0.96  res_backward_subsumption_resolution:    0
% 3.42/0.96  res_clause_to_clause_subsumption:       241
% 3.42/0.96  res_orphan_elimination:                 0
% 3.42/0.96  res_tautology_del:                      26
% 3.42/0.96  res_num_eq_res_simplified:              0
% 3.42/0.96  res_num_sel_changes:                    0
% 3.42/0.96  res_moves_from_active_to_pass:          0
% 3.42/0.96  
% 3.42/0.96  ------ Superposition
% 3.42/0.96  
% 3.42/0.96  sup_time_total:                         0.
% 3.42/0.96  sup_time_generating:                    0.
% 3.42/0.96  sup_time_sim_full:                      0.
% 3.42/0.96  sup_time_sim_immed:                     0.
% 3.42/0.96  
% 3.42/0.96  sup_num_of_clauses:                     134
% 3.42/0.96  sup_num_in_active:                      42
% 3.42/0.96  sup_num_in_passive:                     92
% 3.42/0.96  sup_num_of_loops:                       42
% 3.42/0.96  sup_fw_superposition:                   66
% 3.42/0.96  sup_bw_superposition:                   71
% 3.42/0.96  sup_immediate_simplified:               28
% 3.42/0.96  sup_given_eliminated:                   0
% 3.42/0.96  comparisons_done:                       0
% 3.42/0.96  comparisons_avoided:                    2
% 3.42/0.96  
% 3.42/0.96  ------ Simplifications
% 3.42/0.96  
% 3.42/0.96  
% 3.42/0.96  sim_fw_subset_subsumed:                 6
% 3.42/0.96  sim_bw_subset_subsumed:                 0
% 3.42/0.96  sim_fw_subsumed:                        2
% 3.42/0.96  sim_bw_subsumed:                        0
% 3.42/0.96  sim_fw_subsumption_res:                 0
% 3.42/0.96  sim_bw_subsumption_res:                 0
% 3.42/0.96  sim_tautology_del:                      4
% 3.42/0.96  sim_eq_tautology_del:                   8
% 3.42/0.96  sim_eq_res_simp:                        1
% 3.42/0.96  sim_fw_demodulated:                     3
% 3.42/0.96  sim_bw_demodulated:                     1
% 3.42/0.96  sim_light_normalised:                   21
% 3.42/0.96  sim_joinable_taut:                      0
% 3.42/0.96  sim_joinable_simp:                      0
% 3.42/0.96  sim_ac_normalised:                      0
% 3.42/0.96  sim_smt_subsumption:                    0
% 3.42/0.96  
%------------------------------------------------------------------------------
