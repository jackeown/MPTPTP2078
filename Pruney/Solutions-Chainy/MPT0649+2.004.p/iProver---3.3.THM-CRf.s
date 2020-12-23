%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:21 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 162 expanded)
%              Number of clauses        :   40 (  46 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  408 ( 852 expanded)
%              Number of equality atoms :   83 ( 217 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).

fof(f40,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f56])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k1_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
            & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
          | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
        & r2_hidden(X0,k1_relat_1(X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),sK2) != sK2
        | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2 )
      & r2_hidden(sK2,k1_relat_1(sK3))
      & v2_funct_1(sK3)
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),sK2) != sK2
      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2 )
    & r2_hidden(sK2,k1_relat_1(sK3))
    & v2_funct_1(sK3)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f37])).

fof(f61,plain,
    ( k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),sK2) != sK2
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f46,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_405,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1017,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_2597,plain,
    ( X0 != k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2))
    | X0 = sK2
    | sK2 != k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_1017])).

cnf(c_2672,plain,
    ( k1_funct_1(X0,X1) != k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2))
    | k1_funct_1(X0,X1) = sK2
    | sK2 != k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_2597])).

cnf(c_6258,plain,
    ( k1_funct_1(k5_relat_1(sK3,k4_relat_1(sK3)),sK2) != k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2))
    | k1_funct_1(k5_relat_1(sK3,k4_relat_1(sK3)),sK2) = sK2
    | sK2 != k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_2672])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1263,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k5_relat_1(X0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(k5_relat_1(X0,X1),sK2) = k1_funct_1(X1,k1_funct_1(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2459,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k5_relat_1(sK3,k4_relat_1(sK3))))
    | ~ v1_funct_1(k4_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(k5_relat_1(sK3,k4_relat_1(sK3)),sK2) = k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_995,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_1156,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_995])).

cnf(c_1598,plain,
    ( k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2)) != sK2
    | sK2 = k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1156])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_968,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k1_relat_1(X0))
    | r2_hidden(sK2,k1_relat_1(k5_relat_1(sK3,X0)))
    | ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1256,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k1_relat_1(k4_relat_1(sK3)))
    | r2_hidden(sK2,k1_relat_1(k5_relat_1(sK3,k4_relat_1(sK3))))
    | ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(k4_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_17,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1045,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k1_relat_1(k4_relat_1(sK3)))
    | ~ r2_hidden(k4_tarski(k1_funct_1(sK3,sK2),sK2),k4_relat_1(sK3))
    | ~ v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1036,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(sK3,sK2),sK2),k4_relat_1(sK3))
    | ~ v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_404,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1012,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_2,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k4_relat_1(X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_983,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK3,sK2),sK2),k4_relat_1(sK3))
    | ~ r2_hidden(k4_tarski(sK2,k1_funct_1(sK3,sK2)),sK3)
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_960,plain,
    ( r2_hidden(k4_tarski(sK2,k1_funct_1(sK3,sK2)),sK3)
    | ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_18,negated_conjecture,
    ( k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),sK2) != sK2
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_262,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_263,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_58,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_265,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_263,c_22,c_21,c_20,c_58])).

cnf(c_780,plain,
    ( k1_funct_1(k5_relat_1(sK3,k4_relat_1(sK3)),sK2) != sK2
    | k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2)) != sK2 ),
    inference(light_normalisation,[status(thm)],[c_18,c_265])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k4_relat_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_55,plain,
    ( v1_funct_1(k4_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_52,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6258,c_2459,c_1598,c_1256,c_1045,c_1036,c_1012,c_983,c_960,c_780,c_55,c_52,c_19,c_20,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:28:30 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  % Running in FOF mode
% 2.16/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.16/1.00  
% 2.16/1.00  ------  iProver source info
% 2.16/1.00  
% 2.16/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.16/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.16/1.00  git: non_committed_changes: false
% 2.16/1.00  git: last_make_outside_of_git: false
% 2.16/1.00  
% 2.16/1.00  ------ 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options
% 2.16/1.00  
% 2.16/1.00  --out_options                           all
% 2.16/1.00  --tptp_safe_out                         true
% 2.16/1.00  --problem_path                          ""
% 2.16/1.00  --include_path                          ""
% 2.16/1.00  --clausifier                            res/vclausify_rel
% 2.16/1.00  --clausifier_options                    --mode clausify
% 2.16/1.00  --stdin                                 false
% 2.16/1.00  --stats_out                             all
% 2.16/1.00  
% 2.16/1.00  ------ General Options
% 2.16/1.00  
% 2.16/1.00  --fof                                   false
% 2.16/1.00  --time_out_real                         305.
% 2.16/1.00  --time_out_virtual                      -1.
% 2.16/1.00  --symbol_type_check                     false
% 2.16/1.00  --clausify_out                          false
% 2.16/1.00  --sig_cnt_out                           false
% 2.16/1.00  --trig_cnt_out                          false
% 2.16/1.00  --trig_cnt_out_tolerance                1.
% 2.16/1.00  --trig_cnt_out_sk_spl                   false
% 2.16/1.00  --abstr_cl_out                          false
% 2.16/1.00  
% 2.16/1.00  ------ Global Options
% 2.16/1.00  
% 2.16/1.00  --schedule                              default
% 2.16/1.00  --add_important_lit                     false
% 2.16/1.00  --prop_solver_per_cl                    1000
% 2.16/1.00  --min_unsat_core                        false
% 2.16/1.00  --soft_assumptions                      false
% 2.16/1.00  --soft_lemma_size                       3
% 2.16/1.00  --prop_impl_unit_size                   0
% 2.16/1.00  --prop_impl_unit                        []
% 2.16/1.00  --share_sel_clauses                     true
% 2.16/1.00  --reset_solvers                         false
% 2.16/1.00  --bc_imp_inh                            [conj_cone]
% 2.16/1.00  --conj_cone_tolerance                   3.
% 2.16/1.00  --extra_neg_conj                        none
% 2.16/1.00  --large_theory_mode                     true
% 2.16/1.00  --prolific_symb_bound                   200
% 2.16/1.00  --lt_threshold                          2000
% 2.16/1.00  --clause_weak_htbl                      true
% 2.16/1.00  --gc_record_bc_elim                     false
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing Options
% 2.16/1.00  
% 2.16/1.00  --preprocessing_flag                    true
% 2.16/1.00  --time_out_prep_mult                    0.1
% 2.16/1.00  --splitting_mode                        input
% 2.16/1.00  --splitting_grd                         true
% 2.16/1.00  --splitting_cvd                         false
% 2.16/1.00  --splitting_cvd_svl                     false
% 2.16/1.00  --splitting_nvd                         32
% 2.16/1.00  --sub_typing                            true
% 2.16/1.00  --prep_gs_sim                           true
% 2.16/1.00  --prep_unflatten                        true
% 2.16/1.00  --prep_res_sim                          true
% 2.16/1.00  --prep_upred                            true
% 2.16/1.00  --prep_sem_filter                       exhaustive
% 2.16/1.00  --prep_sem_filter_out                   false
% 2.16/1.00  --pred_elim                             true
% 2.16/1.00  --res_sim_input                         true
% 2.16/1.00  --eq_ax_congr_red                       true
% 2.16/1.00  --pure_diseq_elim                       true
% 2.16/1.00  --brand_transform                       false
% 2.16/1.00  --non_eq_to_eq                          false
% 2.16/1.00  --prep_def_merge                        true
% 2.16/1.00  --prep_def_merge_prop_impl              false
% 2.16/1.00  --prep_def_merge_mbd                    true
% 2.16/1.00  --prep_def_merge_tr_red                 false
% 2.16/1.00  --prep_def_merge_tr_cl                  false
% 2.16/1.00  --smt_preprocessing                     true
% 2.16/1.00  --smt_ac_axioms                         fast
% 2.16/1.00  --preprocessed_out                      false
% 2.16/1.00  --preprocessed_stats                    false
% 2.16/1.00  
% 2.16/1.00  ------ Abstraction refinement Options
% 2.16/1.00  
% 2.16/1.00  --abstr_ref                             []
% 2.16/1.00  --abstr_ref_prep                        false
% 2.16/1.00  --abstr_ref_until_sat                   false
% 2.16/1.00  --abstr_ref_sig_restrict                funpre
% 2.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.00  --abstr_ref_under                       []
% 2.16/1.00  
% 2.16/1.00  ------ SAT Options
% 2.16/1.00  
% 2.16/1.00  --sat_mode                              false
% 2.16/1.00  --sat_fm_restart_options                ""
% 2.16/1.00  --sat_gr_def                            false
% 2.16/1.00  --sat_epr_types                         true
% 2.16/1.00  --sat_non_cyclic_types                  false
% 2.16/1.00  --sat_finite_models                     false
% 2.16/1.00  --sat_fm_lemmas                         false
% 2.16/1.00  --sat_fm_prep                           false
% 2.16/1.00  --sat_fm_uc_incr                        true
% 2.16/1.00  --sat_out_model                         small
% 2.16/1.00  --sat_out_clauses                       false
% 2.16/1.00  
% 2.16/1.00  ------ QBF Options
% 2.16/1.00  
% 2.16/1.00  --qbf_mode                              false
% 2.16/1.00  --qbf_elim_univ                         false
% 2.16/1.00  --qbf_dom_inst                          none
% 2.16/1.00  --qbf_dom_pre_inst                      false
% 2.16/1.00  --qbf_sk_in                             false
% 2.16/1.00  --qbf_pred_elim                         true
% 2.16/1.00  --qbf_split                             512
% 2.16/1.00  
% 2.16/1.00  ------ BMC1 Options
% 2.16/1.00  
% 2.16/1.00  --bmc1_incremental                      false
% 2.16/1.00  --bmc1_axioms                           reachable_all
% 2.16/1.00  --bmc1_min_bound                        0
% 2.16/1.00  --bmc1_max_bound                        -1
% 2.16/1.00  --bmc1_max_bound_default                -1
% 2.16/1.00  --bmc1_symbol_reachability              true
% 2.16/1.00  --bmc1_property_lemmas                  false
% 2.16/1.00  --bmc1_k_induction                      false
% 2.16/1.00  --bmc1_non_equiv_states                 false
% 2.16/1.00  --bmc1_deadlock                         false
% 2.16/1.00  --bmc1_ucm                              false
% 2.16/1.00  --bmc1_add_unsat_core                   none
% 2.16/1.00  --bmc1_unsat_core_children              false
% 2.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.00  --bmc1_out_stat                         full
% 2.16/1.00  --bmc1_ground_init                      false
% 2.16/1.00  --bmc1_pre_inst_next_state              false
% 2.16/1.00  --bmc1_pre_inst_state                   false
% 2.16/1.00  --bmc1_pre_inst_reach_state             false
% 2.16/1.00  --bmc1_out_unsat_core                   false
% 2.16/1.00  --bmc1_aig_witness_out                  false
% 2.16/1.00  --bmc1_verbose                          false
% 2.16/1.00  --bmc1_dump_clauses_tptp                false
% 2.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.00  --bmc1_dump_file                        -
% 2.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.00  --bmc1_ucm_extend_mode                  1
% 2.16/1.00  --bmc1_ucm_init_mode                    2
% 2.16/1.00  --bmc1_ucm_cone_mode                    none
% 2.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.00  --bmc1_ucm_relax_model                  4
% 2.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.00  --bmc1_ucm_layered_model                none
% 2.16/1.00  --bmc1_ucm_max_lemma_size               10
% 2.16/1.00  
% 2.16/1.00  ------ AIG Options
% 2.16/1.00  
% 2.16/1.00  --aig_mode                              false
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation Options
% 2.16/1.00  
% 2.16/1.00  --instantiation_flag                    true
% 2.16/1.00  --inst_sos_flag                         false
% 2.16/1.00  --inst_sos_phase                        true
% 2.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel_side                     num_symb
% 2.16/1.00  --inst_solver_per_active                1400
% 2.16/1.00  --inst_solver_calls_frac                1.
% 2.16/1.00  --inst_passive_queue_type               priority_queues
% 2.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.00  --inst_passive_queues_freq              [25;2]
% 2.16/1.00  --inst_dismatching                      true
% 2.16/1.00  --inst_eager_unprocessed_to_passive     true
% 2.16/1.00  --inst_prop_sim_given                   true
% 2.16/1.00  --inst_prop_sim_new                     false
% 2.16/1.00  --inst_subs_new                         false
% 2.16/1.00  --inst_eq_res_simp                      false
% 2.16/1.00  --inst_subs_given                       false
% 2.16/1.00  --inst_orphan_elimination               true
% 2.16/1.00  --inst_learning_loop_flag               true
% 2.16/1.00  --inst_learning_start                   3000
% 2.16/1.00  --inst_learning_factor                  2
% 2.16/1.00  --inst_start_prop_sim_after_learn       3
% 2.16/1.00  --inst_sel_renew                        solver
% 2.16/1.00  --inst_lit_activity_flag                true
% 2.16/1.00  --inst_restr_to_given                   false
% 2.16/1.00  --inst_activity_threshold               500
% 2.16/1.00  --inst_out_proof                        true
% 2.16/1.00  
% 2.16/1.00  ------ Resolution Options
% 2.16/1.00  
% 2.16/1.00  --resolution_flag                       true
% 2.16/1.00  --res_lit_sel                           adaptive
% 2.16/1.00  --res_lit_sel_side                      none
% 2.16/1.00  --res_ordering                          kbo
% 2.16/1.00  --res_to_prop_solver                    active
% 2.16/1.00  --res_prop_simpl_new                    false
% 2.16/1.00  --res_prop_simpl_given                  true
% 2.16/1.00  --res_passive_queue_type                priority_queues
% 2.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.00  --res_passive_queues_freq               [15;5]
% 2.16/1.00  --res_forward_subs                      full
% 2.16/1.00  --res_backward_subs                     full
% 2.16/1.00  --res_forward_subs_resolution           true
% 2.16/1.00  --res_backward_subs_resolution          true
% 2.16/1.00  --res_orphan_elimination                true
% 2.16/1.00  --res_time_limit                        2.
% 2.16/1.00  --res_out_proof                         true
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Options
% 2.16/1.00  
% 2.16/1.00  --superposition_flag                    true
% 2.16/1.00  --sup_passive_queue_type                priority_queues
% 2.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.00  --demod_completeness_check              fast
% 2.16/1.00  --demod_use_ground                      true
% 2.16/1.00  --sup_to_prop_solver                    passive
% 2.16/1.00  --sup_prop_simpl_new                    true
% 2.16/1.00  --sup_prop_simpl_given                  true
% 2.16/1.00  --sup_fun_splitting                     false
% 2.16/1.00  --sup_smt_interval                      50000
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Simplification Setup
% 2.16/1.00  
% 2.16/1.00  --sup_indices_passive                   []
% 2.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_full_bw                           [BwDemod]
% 2.16/1.00  --sup_immed_triv                        [TrivRules]
% 2.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_immed_bw_main                     []
% 2.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  
% 2.16/1.00  ------ Combination Options
% 2.16/1.00  
% 2.16/1.00  --comb_res_mult                         3
% 2.16/1.00  --comb_sup_mult                         2
% 2.16/1.00  --comb_inst_mult                        10
% 2.16/1.00  
% 2.16/1.00  ------ Debug Options
% 2.16/1.00  
% 2.16/1.00  --dbg_backtrace                         false
% 2.16/1.00  --dbg_dump_prop_clauses                 false
% 2.16/1.00  --dbg_dump_prop_clauses_file            -
% 2.16/1.00  --dbg_out_stat                          false
% 2.16/1.00  ------ Parsing...
% 2.16/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.16/1.00  ------ Proving...
% 2.16/1.00  ------ Problem Properties 
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  clauses                                 21
% 2.16/1.00  conjectures                             4
% 2.16/1.00  EPR                                     2
% 2.16/1.00  Horn                                    20
% 2.16/1.00  unary                                   5
% 2.16/1.00  binary                                  4
% 2.16/1.00  lits                                    72
% 2.16/1.00  lits eq                                 9
% 2.16/1.00  fd_pure                                 0
% 2.16/1.00  fd_pseudo                               0
% 2.16/1.00  fd_cond                                 0
% 2.16/1.00  fd_pseudo_cond                          3
% 2.16/1.00  AC symbols                              0
% 2.16/1.00  
% 2.16/1.00  ------ Schedule dynamic 5 is on 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  ------ 
% 2.16/1.00  Current options:
% 2.16/1.00  ------ 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options
% 2.16/1.00  
% 2.16/1.00  --out_options                           all
% 2.16/1.00  --tptp_safe_out                         true
% 2.16/1.00  --problem_path                          ""
% 2.16/1.00  --include_path                          ""
% 2.16/1.00  --clausifier                            res/vclausify_rel
% 2.16/1.00  --clausifier_options                    --mode clausify
% 2.16/1.00  --stdin                                 false
% 2.16/1.00  --stats_out                             all
% 2.16/1.00  
% 2.16/1.00  ------ General Options
% 2.16/1.00  
% 2.16/1.00  --fof                                   false
% 2.16/1.00  --time_out_real                         305.
% 2.16/1.00  --time_out_virtual                      -1.
% 2.16/1.00  --symbol_type_check                     false
% 2.16/1.00  --clausify_out                          false
% 2.16/1.00  --sig_cnt_out                           false
% 2.16/1.00  --trig_cnt_out                          false
% 2.16/1.00  --trig_cnt_out_tolerance                1.
% 2.16/1.00  --trig_cnt_out_sk_spl                   false
% 2.16/1.00  --abstr_cl_out                          false
% 2.16/1.00  
% 2.16/1.00  ------ Global Options
% 2.16/1.00  
% 2.16/1.00  --schedule                              default
% 2.16/1.00  --add_important_lit                     false
% 2.16/1.00  --prop_solver_per_cl                    1000
% 2.16/1.00  --min_unsat_core                        false
% 2.16/1.00  --soft_assumptions                      false
% 2.16/1.00  --soft_lemma_size                       3
% 2.16/1.00  --prop_impl_unit_size                   0
% 2.16/1.00  --prop_impl_unit                        []
% 2.16/1.00  --share_sel_clauses                     true
% 2.16/1.00  --reset_solvers                         false
% 2.16/1.00  --bc_imp_inh                            [conj_cone]
% 2.16/1.00  --conj_cone_tolerance                   3.
% 2.16/1.00  --extra_neg_conj                        none
% 2.16/1.00  --large_theory_mode                     true
% 2.16/1.00  --prolific_symb_bound                   200
% 2.16/1.00  --lt_threshold                          2000
% 2.16/1.00  --clause_weak_htbl                      true
% 2.16/1.00  --gc_record_bc_elim                     false
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing Options
% 2.16/1.00  
% 2.16/1.00  --preprocessing_flag                    true
% 2.16/1.00  --time_out_prep_mult                    0.1
% 2.16/1.00  --splitting_mode                        input
% 2.16/1.00  --splitting_grd                         true
% 2.16/1.00  --splitting_cvd                         false
% 2.16/1.00  --splitting_cvd_svl                     false
% 2.16/1.00  --splitting_nvd                         32
% 2.16/1.00  --sub_typing                            true
% 2.16/1.00  --prep_gs_sim                           true
% 2.16/1.00  --prep_unflatten                        true
% 2.16/1.00  --prep_res_sim                          true
% 2.16/1.00  --prep_upred                            true
% 2.16/1.00  --prep_sem_filter                       exhaustive
% 2.16/1.00  --prep_sem_filter_out                   false
% 2.16/1.00  --pred_elim                             true
% 2.16/1.00  --res_sim_input                         true
% 2.16/1.00  --eq_ax_congr_red                       true
% 2.16/1.00  --pure_diseq_elim                       true
% 2.16/1.00  --brand_transform                       false
% 2.16/1.00  --non_eq_to_eq                          false
% 2.16/1.00  --prep_def_merge                        true
% 2.16/1.00  --prep_def_merge_prop_impl              false
% 2.16/1.00  --prep_def_merge_mbd                    true
% 2.16/1.00  --prep_def_merge_tr_red                 false
% 2.16/1.00  --prep_def_merge_tr_cl                  false
% 2.16/1.00  --smt_preprocessing                     true
% 2.16/1.00  --smt_ac_axioms                         fast
% 2.16/1.00  --preprocessed_out                      false
% 2.16/1.00  --preprocessed_stats                    false
% 2.16/1.00  
% 2.16/1.00  ------ Abstraction refinement Options
% 2.16/1.00  
% 2.16/1.00  --abstr_ref                             []
% 2.16/1.00  --abstr_ref_prep                        false
% 2.16/1.00  --abstr_ref_until_sat                   false
% 2.16/1.00  --abstr_ref_sig_restrict                funpre
% 2.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.00  --abstr_ref_under                       []
% 2.16/1.00  
% 2.16/1.00  ------ SAT Options
% 2.16/1.00  
% 2.16/1.00  --sat_mode                              false
% 2.16/1.00  --sat_fm_restart_options                ""
% 2.16/1.00  --sat_gr_def                            false
% 2.16/1.00  --sat_epr_types                         true
% 2.16/1.00  --sat_non_cyclic_types                  false
% 2.16/1.00  --sat_finite_models                     false
% 2.16/1.00  --sat_fm_lemmas                         false
% 2.16/1.00  --sat_fm_prep                           false
% 2.16/1.00  --sat_fm_uc_incr                        true
% 2.16/1.00  --sat_out_model                         small
% 2.16/1.00  --sat_out_clauses                       false
% 2.16/1.00  
% 2.16/1.00  ------ QBF Options
% 2.16/1.00  
% 2.16/1.00  --qbf_mode                              false
% 2.16/1.00  --qbf_elim_univ                         false
% 2.16/1.00  --qbf_dom_inst                          none
% 2.16/1.00  --qbf_dom_pre_inst                      false
% 2.16/1.00  --qbf_sk_in                             false
% 2.16/1.00  --qbf_pred_elim                         true
% 2.16/1.00  --qbf_split                             512
% 2.16/1.00  
% 2.16/1.00  ------ BMC1 Options
% 2.16/1.00  
% 2.16/1.00  --bmc1_incremental                      false
% 2.16/1.00  --bmc1_axioms                           reachable_all
% 2.16/1.00  --bmc1_min_bound                        0
% 2.16/1.00  --bmc1_max_bound                        -1
% 2.16/1.00  --bmc1_max_bound_default                -1
% 2.16/1.00  --bmc1_symbol_reachability              true
% 2.16/1.00  --bmc1_property_lemmas                  false
% 2.16/1.00  --bmc1_k_induction                      false
% 2.16/1.00  --bmc1_non_equiv_states                 false
% 2.16/1.00  --bmc1_deadlock                         false
% 2.16/1.00  --bmc1_ucm                              false
% 2.16/1.00  --bmc1_add_unsat_core                   none
% 2.16/1.00  --bmc1_unsat_core_children              false
% 2.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.00  --bmc1_out_stat                         full
% 2.16/1.00  --bmc1_ground_init                      false
% 2.16/1.00  --bmc1_pre_inst_next_state              false
% 2.16/1.00  --bmc1_pre_inst_state                   false
% 2.16/1.00  --bmc1_pre_inst_reach_state             false
% 2.16/1.00  --bmc1_out_unsat_core                   false
% 2.16/1.00  --bmc1_aig_witness_out                  false
% 2.16/1.00  --bmc1_verbose                          false
% 2.16/1.00  --bmc1_dump_clauses_tptp                false
% 2.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.00  --bmc1_dump_file                        -
% 2.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.00  --bmc1_ucm_extend_mode                  1
% 2.16/1.00  --bmc1_ucm_init_mode                    2
% 2.16/1.00  --bmc1_ucm_cone_mode                    none
% 2.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.00  --bmc1_ucm_relax_model                  4
% 2.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.00  --bmc1_ucm_layered_model                none
% 2.16/1.00  --bmc1_ucm_max_lemma_size               10
% 2.16/1.00  
% 2.16/1.00  ------ AIG Options
% 2.16/1.00  
% 2.16/1.00  --aig_mode                              false
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation Options
% 2.16/1.00  
% 2.16/1.00  --instantiation_flag                    true
% 2.16/1.00  --inst_sos_flag                         false
% 2.16/1.00  --inst_sos_phase                        true
% 2.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel_side                     none
% 2.16/1.00  --inst_solver_per_active                1400
% 2.16/1.00  --inst_solver_calls_frac                1.
% 2.16/1.00  --inst_passive_queue_type               priority_queues
% 2.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.00  --inst_passive_queues_freq              [25;2]
% 2.16/1.00  --inst_dismatching                      true
% 2.16/1.00  --inst_eager_unprocessed_to_passive     true
% 2.16/1.00  --inst_prop_sim_given                   true
% 2.16/1.00  --inst_prop_sim_new                     false
% 2.16/1.00  --inst_subs_new                         false
% 2.16/1.00  --inst_eq_res_simp                      false
% 2.16/1.00  --inst_subs_given                       false
% 2.16/1.00  --inst_orphan_elimination               true
% 2.16/1.00  --inst_learning_loop_flag               true
% 2.16/1.00  --inst_learning_start                   3000
% 2.16/1.00  --inst_learning_factor                  2
% 2.16/1.00  --inst_start_prop_sim_after_learn       3
% 2.16/1.00  --inst_sel_renew                        solver
% 2.16/1.00  --inst_lit_activity_flag                true
% 2.16/1.00  --inst_restr_to_given                   false
% 2.16/1.00  --inst_activity_threshold               500
% 2.16/1.00  --inst_out_proof                        true
% 2.16/1.00  
% 2.16/1.00  ------ Resolution Options
% 2.16/1.00  
% 2.16/1.00  --resolution_flag                       false
% 2.16/1.00  --res_lit_sel                           adaptive
% 2.16/1.00  --res_lit_sel_side                      none
% 2.16/1.00  --res_ordering                          kbo
% 2.16/1.00  --res_to_prop_solver                    active
% 2.16/1.00  --res_prop_simpl_new                    false
% 2.16/1.00  --res_prop_simpl_given                  true
% 2.16/1.00  --res_passive_queue_type                priority_queues
% 2.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.00  --res_passive_queues_freq               [15;5]
% 2.16/1.00  --res_forward_subs                      full
% 2.16/1.00  --res_backward_subs                     full
% 2.16/1.00  --res_forward_subs_resolution           true
% 2.16/1.00  --res_backward_subs_resolution          true
% 2.16/1.00  --res_orphan_elimination                true
% 2.16/1.00  --res_time_limit                        2.
% 2.16/1.00  --res_out_proof                         true
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Options
% 2.16/1.00  
% 2.16/1.00  --superposition_flag                    true
% 2.16/1.00  --sup_passive_queue_type                priority_queues
% 2.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.00  --demod_completeness_check              fast
% 2.16/1.00  --demod_use_ground                      true
% 2.16/1.00  --sup_to_prop_solver                    passive
% 2.16/1.00  --sup_prop_simpl_new                    true
% 2.16/1.00  --sup_prop_simpl_given                  true
% 2.16/1.00  --sup_fun_splitting                     false
% 2.16/1.00  --sup_smt_interval                      50000
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Simplification Setup
% 2.16/1.00  
% 2.16/1.00  --sup_indices_passive                   []
% 2.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_full_bw                           [BwDemod]
% 2.16/1.00  --sup_immed_triv                        [TrivRules]
% 2.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_immed_bw_main                     []
% 2.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  
% 2.16/1.00  ------ Combination Options
% 2.16/1.00  
% 2.16/1.00  --comb_res_mult                         3
% 2.16/1.00  --comb_sup_mult                         2
% 2.16/1.00  --comb_inst_mult                        10
% 2.16/1.00  
% 2.16/1.00  ------ Debug Options
% 2.16/1.00  
% 2.16/1.00  --dbg_backtrace                         false
% 2.16/1.00  --dbg_dump_prop_clauses                 false
% 2.16/1.00  --dbg_dump_prop_clauses_file            -
% 2.16/1.00  --dbg_out_stat                          false
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  ------ Proving...
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  % SZS status Theorem for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  fof(f8,axiom,(
% 2.16/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0))))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f23,plain,(
% 2.16/1.00    ! [X0,X1] : (! [X2] : ((k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.16/1.00    inference(ennf_transformation,[],[f8])).
% 2.16/1.00  
% 2.16/1.00  fof(f24,plain,(
% 2.16/1.00    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.16/1.00    inference(flattening,[],[f23])).
% 2.16/1.00  
% 2.16/1.00  fof(f53,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f24])).
% 2.16/1.00  
% 2.16/1.00  fof(f7,axiom,(
% 2.16/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f21,plain,(
% 2.16/1.00    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.16/1.00    inference(ennf_transformation,[],[f7])).
% 2.16/1.00  
% 2.16/1.00  fof(f22,plain,(
% 2.16/1.00    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.16/1.00    inference(flattening,[],[f21])).
% 2.16/1.00  
% 2.16/1.00  fof(f33,plain,(
% 2.16/1.00    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.16/1.00    inference(nnf_transformation,[],[f22])).
% 2.16/1.00  
% 2.16/1.00  fof(f34,plain,(
% 2.16/1.00    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.16/1.00    inference(flattening,[],[f33])).
% 2.16/1.00  
% 2.16/1.00  fof(f52,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f34])).
% 2.16/1.00  
% 2.16/1.00  fof(f9,axiom,(
% 2.16/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f25,plain,(
% 2.16/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.16/1.00    inference(ennf_transformation,[],[f9])).
% 2.16/1.00  
% 2.16/1.00  fof(f26,plain,(
% 2.16/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.16/1.00    inference(flattening,[],[f25])).
% 2.16/1.00  
% 2.16/1.00  fof(f35,plain,(
% 2.16/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.16/1.00    inference(nnf_transformation,[],[f26])).
% 2.16/1.00  
% 2.16/1.00  fof(f36,plain,(
% 2.16/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.16/1.00    inference(flattening,[],[f35])).
% 2.16/1.00  
% 2.16/1.00  fof(f54,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f36])).
% 2.16/1.00  
% 2.16/1.00  fof(f55,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f36])).
% 2.16/1.00  
% 2.16/1.00  fof(f1,axiom,(
% 2.16/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f12,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.16/1.00    inference(ennf_transformation,[],[f1])).
% 2.16/1.00  
% 2.16/1.00  fof(f29,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X3,X2),X0)) & (r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.16/1.00    inference(nnf_transformation,[],[f12])).
% 2.16/1.00  
% 2.16/1.00  fof(f30,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.16/1.00    inference(rectify,[],[f29])).
% 2.16/1.00  
% 2.16/1.00  fof(f31,plain,(
% 2.16/1.00    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1))))),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f32,plain,(
% 2.16/1.00    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ((~r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f31])).
% 2.16/1.00  
% 2.16/1.00  fof(f40,plain,(
% 2.16/1.00    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0) | k4_relat_1(X0) != X1 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f32])).
% 2.16/1.00  
% 2.16/1.00  fof(f62,plain,(
% 2.16/1.00    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X4),X0) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.16/1.00    inference(equality_resolution,[],[f40])).
% 2.16/1.00  
% 2.16/1.00  fof(f56,plain,(
% 2.16/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f36])).
% 2.16/1.00  
% 2.16/1.00  fof(f64,plain,(
% 2.16/1.00    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.16/1.00    inference(equality_resolution,[],[f56])).
% 2.16/1.00  
% 2.16/1.00  fof(f10,conjecture,(
% 2.16/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f11,negated_conjecture,(
% 2.16/1.00    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 2.16/1.00    inference(negated_conjecture,[],[f10])).
% 2.16/1.00  
% 2.16/1.00  fof(f27,plain,(
% 2.16/1.00    ? [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & (r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.16/1.00    inference(ennf_transformation,[],[f11])).
% 2.16/1.00  
% 2.16/1.00  fof(f28,plain,(
% 2.16/1.00    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.16/1.00    inference(flattening,[],[f27])).
% 2.16/1.00  
% 2.16/1.00  fof(f37,plain,(
% 2.16/1.00    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),sK2) != sK2 | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2) & r2_hidden(sK2,k1_relat_1(sK3)) & v2_funct_1(sK3) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 2.16/1.00    introduced(choice_axiom,[])).
% 2.16/1.00  
% 2.16/1.00  fof(f38,plain,(
% 2.16/1.00    (k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),sK2) != sK2 | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2) & r2_hidden(sK2,k1_relat_1(sK3)) & v2_funct_1(sK3) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 2.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f37])).
% 2.16/1.00  
% 2.16/1.00  fof(f61,plain,(
% 2.16/1.00    k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),sK2) != sK2 | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2),
% 2.16/1.00    inference(cnf_transformation,[],[f38])).
% 2.16/1.00  
% 2.16/1.00  fof(f4,axiom,(
% 2.16/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f15,plain,(
% 2.16/1.00    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f4])).
% 2.16/1.00  
% 2.16/1.00  fof(f16,plain,(
% 2.16/1.00    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/1.00    inference(flattening,[],[f15])).
% 2.16/1.00  
% 2.16/1.00  fof(f46,plain,(
% 2.16/1.00    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f16])).
% 2.16/1.00  
% 2.16/1.00  fof(f59,plain,(
% 2.16/1.00    v2_funct_1(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f38])).
% 2.16/1.00  
% 2.16/1.00  fof(f57,plain,(
% 2.16/1.00    v1_relat_1(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f38])).
% 2.16/1.00  
% 2.16/1.00  fof(f58,plain,(
% 2.16/1.00    v1_funct_1(sK3)),
% 2.16/1.00    inference(cnf_transformation,[],[f38])).
% 2.16/1.00  
% 2.16/1.00  fof(f5,axiom,(
% 2.16/1.00    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))))),
% 2.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.00  
% 2.16/1.00  fof(f17,plain,(
% 2.16/1.00    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.16/1.00    inference(ennf_transformation,[],[f5])).
% 2.16/1.00  
% 2.16/1.00  fof(f18,plain,(
% 2.16/1.00    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.16/1.00    inference(flattening,[],[f17])).
% 2.16/1.00  
% 2.16/1.00  fof(f48,plain,(
% 2.16/1.00    ( ! [X0] : (v1_funct_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f18])).
% 2.16/1.00  
% 2.16/1.00  fof(f47,plain,(
% 2.16/1.00    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/1.00    inference(cnf_transformation,[],[f18])).
% 2.16/1.00  
% 2.16/1.00  fof(f60,plain,(
% 2.16/1.00    r2_hidden(sK2,k1_relat_1(sK3))),
% 2.16/1.00    inference(cnf_transformation,[],[f38])).
% 2.16/1.00  
% 2.16/1.00  cnf(c_405,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1017,plain,
% 2.16/1.00      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_405]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2597,plain,
% 2.16/1.00      ( X0 != k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2))
% 2.16/1.00      | X0 = sK2
% 2.16/1.00      | sK2 != k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_1017]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2672,plain,
% 2.16/1.00      ( k1_funct_1(X0,X1) != k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2))
% 2.16/1.00      | k1_funct_1(X0,X1) = sK2
% 2.16/1.00      | sK2 != k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2597]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_6258,plain,
% 2.16/1.00      ( k1_funct_1(k5_relat_1(sK3,k4_relat_1(sK3)),sK2) != k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2))
% 2.16/1.00      | k1_funct_1(k5_relat_1(sK3,k4_relat_1(sK3)),sK2) = sK2
% 2.16/1.00      | sK2 != k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2672]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_14,plain,
% 2.16/1.00      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 2.16/1.00      | ~ v1_funct_1(X2)
% 2.16/1.00      | ~ v1_funct_1(X1)
% 2.16/1.00      | ~ v1_relat_1(X2)
% 2.16/1.00      | ~ v1_relat_1(X1)
% 2.16/1.00      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 2.16/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1263,plain,
% 2.16/1.00      ( ~ r2_hidden(sK2,k1_relat_1(k5_relat_1(X0,X1)))
% 2.16/1.00      | ~ v1_funct_1(X0)
% 2.16/1.00      | ~ v1_funct_1(X1)
% 2.16/1.00      | ~ v1_relat_1(X1)
% 2.16/1.00      | ~ v1_relat_1(X0)
% 2.16/1.00      | k1_funct_1(k5_relat_1(X0,X1),sK2) = k1_funct_1(X1,k1_funct_1(X0,sK2)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2459,plain,
% 2.16/1.00      ( ~ r2_hidden(sK2,k1_relat_1(k5_relat_1(sK3,k4_relat_1(sK3))))
% 2.16/1.00      | ~ v1_funct_1(k4_relat_1(sK3))
% 2.16/1.00      | ~ v1_funct_1(sK3)
% 2.16/1.00      | ~ v1_relat_1(k4_relat_1(sK3))
% 2.16/1.00      | ~ v1_relat_1(sK3)
% 2.16/1.00      | k1_funct_1(k5_relat_1(sK3,k4_relat_1(sK3)),sK2) = k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_1263]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_995,plain,
% 2.16/1.00      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_405]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1156,plain,
% 2.16/1.00      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_995]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1598,plain,
% 2.16/1.00      ( k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2)) != sK2
% 2.16/1.00      | sK2 = k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2))
% 2.16/1.00      | sK2 != sK2 ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_1156]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_11,plain,
% 2.16/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.16/1.00      | r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 2.16/1.00      | ~ r2_hidden(k1_funct_1(X1,X0),k1_relat_1(X2))
% 2.16/1.00      | ~ v1_funct_1(X2)
% 2.16/1.00      | ~ v1_funct_1(X1)
% 2.16/1.00      | ~ v1_relat_1(X2)
% 2.16/1.00      | ~ v1_relat_1(X1) ),
% 2.16/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_968,plain,
% 2.16/1.00      ( ~ r2_hidden(k1_funct_1(sK3,sK2),k1_relat_1(X0))
% 2.16/1.00      | r2_hidden(sK2,k1_relat_1(k5_relat_1(sK3,X0)))
% 2.16/1.00      | ~ r2_hidden(sK2,k1_relat_1(sK3))
% 2.16/1.00      | ~ v1_funct_1(X0)
% 2.16/1.00      | ~ v1_funct_1(sK3)
% 2.16/1.00      | ~ v1_relat_1(X0)
% 2.16/1.00      | ~ v1_relat_1(sK3) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1256,plain,
% 2.16/1.00      ( ~ r2_hidden(k1_funct_1(sK3,sK2),k1_relat_1(k4_relat_1(sK3)))
% 2.16/1.00      | r2_hidden(sK2,k1_relat_1(k5_relat_1(sK3,k4_relat_1(sK3))))
% 2.16/1.00      | ~ r2_hidden(sK2,k1_relat_1(sK3))
% 2.16/1.00      | ~ v1_funct_1(k4_relat_1(sK3))
% 2.16/1.00      | ~ v1_funct_1(sK3)
% 2.16/1.00      | ~ v1_relat_1(k4_relat_1(sK3))
% 2.16/1.00      | ~ v1_relat_1(sK3) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_968]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_17,plain,
% 2.16/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 2.16/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 2.16/1.00      | ~ v1_funct_1(X1)
% 2.16/1.00      | ~ v1_relat_1(X1) ),
% 2.16/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1045,plain,
% 2.16/1.00      ( r2_hidden(k1_funct_1(sK3,sK2),k1_relat_1(k4_relat_1(sK3)))
% 2.16/1.00      | ~ r2_hidden(k4_tarski(k1_funct_1(sK3,sK2),sK2),k4_relat_1(sK3))
% 2.16/1.00      | ~ v1_funct_1(k4_relat_1(sK3))
% 2.16/1.00      | ~ v1_relat_1(k4_relat_1(sK3)) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_16,plain,
% 2.16/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.16/1.00      | ~ v1_funct_1(X2)
% 2.16/1.00      | ~ v1_relat_1(X2)
% 2.16/1.00      | k1_funct_1(X2,X0) = X1 ),
% 2.16/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1036,plain,
% 2.16/1.00      ( ~ r2_hidden(k4_tarski(k1_funct_1(sK3,sK2),sK2),k4_relat_1(sK3))
% 2.16/1.00      | ~ v1_funct_1(k4_relat_1(sK3))
% 2.16/1.00      | ~ v1_relat_1(k4_relat_1(sK3))
% 2.16/1.00      | k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2)) = sK2 ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_404,plain,( X0 = X0 ),theory(equality) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_1012,plain,
% 2.16/1.00      ( sK2 = sK2 ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_404]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2,plain,
% 2.16/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.16/1.00      | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
% 2.16/1.00      | ~ v1_relat_1(X2)
% 2.16/1.00      | ~ v1_relat_1(k4_relat_1(X2)) ),
% 2.16/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_983,plain,
% 2.16/1.00      ( r2_hidden(k4_tarski(k1_funct_1(sK3,sK2),sK2),k4_relat_1(sK3))
% 2.16/1.00      | ~ r2_hidden(k4_tarski(sK2,k1_funct_1(sK3,sK2)),sK3)
% 2.16/1.00      | ~ v1_relat_1(k4_relat_1(sK3))
% 2.16/1.00      | ~ v1_relat_1(sK3) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_15,plain,
% 2.16/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.16/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.16/1.00      | ~ v1_funct_1(X1)
% 2.16/1.00      | ~ v1_relat_1(X1) ),
% 2.16/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_960,plain,
% 2.16/1.00      ( r2_hidden(k4_tarski(sK2,k1_funct_1(sK3,sK2)),sK3)
% 2.16/1.00      | ~ r2_hidden(sK2,k1_relat_1(sK3))
% 2.16/1.00      | ~ v1_funct_1(sK3)
% 2.16/1.00      | ~ v1_relat_1(sK3) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_18,negated_conjecture,
% 2.16/1.00      ( k1_funct_1(k5_relat_1(sK3,k2_funct_1(sK3)),sK2) != sK2
% 2.16/1.00      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2 ),
% 2.16/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_7,plain,
% 2.16/1.00      ( ~ v1_funct_1(X0)
% 2.16/1.00      | ~ v2_funct_1(X0)
% 2.16/1.00      | ~ v1_relat_1(X0)
% 2.16/1.00      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_20,negated_conjecture,
% 2.16/1.00      ( v2_funct_1(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_262,plain,
% 2.16/1.00      ( ~ v1_funct_1(X0)
% 2.16/1.00      | ~ v1_relat_1(X0)
% 2.16/1.00      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.16/1.00      | sK3 != X0 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_263,plain,
% 2.16/1.00      ( ~ v1_funct_1(sK3)
% 2.16/1.00      | ~ v1_relat_1(sK3)
% 2.16/1.00      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_262]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_22,negated_conjecture,
% 2.16/1.00      ( v1_relat_1(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_21,negated_conjecture,
% 2.16/1.00      ( v1_funct_1(sK3) ),
% 2.16/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_58,plain,
% 2.16/1.00      ( ~ v1_funct_1(sK3)
% 2.16/1.00      | ~ v2_funct_1(sK3)
% 2.16/1.00      | ~ v1_relat_1(sK3)
% 2.16/1.00      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_265,plain,
% 2.16/1.00      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_263,c_22,c_21,c_20,c_58]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_780,plain,
% 2.16/1.00      ( k1_funct_1(k5_relat_1(sK3,k4_relat_1(sK3)),sK2) != sK2
% 2.16/1.00      | k1_funct_1(k4_relat_1(sK3),k1_funct_1(sK3,sK2)) != sK2 ),
% 2.16/1.00      inference(light_normalisation,[status(thm)],[c_18,c_265]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_8,plain,
% 2.16/1.00      ( ~ v1_funct_1(X0)
% 2.16/1.00      | v1_funct_1(k4_relat_1(X0))
% 2.16/1.00      | ~ v2_funct_1(X0)
% 2.16/1.00      | ~ v1_relat_1(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_55,plain,
% 2.16/1.00      ( v1_funct_1(k4_relat_1(sK3))
% 2.16/1.00      | ~ v1_funct_1(sK3)
% 2.16/1.00      | ~ v2_funct_1(sK3)
% 2.16/1.00      | ~ v1_relat_1(sK3) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_9,plain,
% 2.16/1.00      ( ~ v1_funct_1(X0)
% 2.16/1.00      | ~ v2_funct_1(X0)
% 2.16/1.00      | ~ v1_relat_1(X0)
% 2.16/1.00      | v1_relat_1(k4_relat_1(X0)) ),
% 2.16/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_52,plain,
% 2.16/1.00      ( ~ v1_funct_1(sK3)
% 2.16/1.00      | ~ v2_funct_1(sK3)
% 2.16/1.00      | v1_relat_1(k4_relat_1(sK3))
% 2.16/1.00      | ~ v1_relat_1(sK3) ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_19,negated_conjecture,
% 2.16/1.00      ( r2_hidden(sK2,k1_relat_1(sK3)) ),
% 2.16/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(contradiction,plain,
% 2.16/1.00      ( $false ),
% 2.16/1.00      inference(minisat,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_6258,c_2459,c_1598,c_1256,c_1045,c_1036,c_1012,c_983,
% 2.16/1.00                 c_960,c_780,c_55,c_52,c_19,c_20,c_21,c_22]) ).
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  ------                               Statistics
% 2.16/1.00  
% 2.16/1.00  ------ General
% 2.16/1.00  
% 2.16/1.00  abstr_ref_over_cycles:                  0
% 2.16/1.00  abstr_ref_under_cycles:                 0
% 2.16/1.00  gc_basic_clause_elim:                   0
% 2.16/1.00  forced_gc_time:                         0
% 2.16/1.00  parsing_time:                           0.009
% 2.16/1.00  unif_index_cands_time:                  0.
% 2.16/1.00  unif_index_add_time:                    0.
% 2.16/1.00  orderings_time:                         0.
% 2.16/1.00  out_proof_time:                         0.007
% 2.16/1.00  total_time:                             0.177
% 2.16/1.00  num_of_symbols:                         46
% 2.16/1.00  num_of_terms:                           6340
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing
% 2.16/1.00  
% 2.16/1.00  num_of_splits:                          0
% 2.16/1.00  num_of_split_atoms:                     0
% 2.16/1.00  num_of_reused_defs:                     0
% 2.16/1.00  num_eq_ax_congr_red:                    13
% 2.16/1.00  num_of_sem_filtered_clauses:            1
% 2.16/1.00  num_of_subtypes:                        0
% 2.16/1.00  monotx_restored_types:                  0
% 2.16/1.00  sat_num_of_epr_types:                   0
% 2.16/1.00  sat_num_of_non_cyclic_types:            0
% 2.16/1.00  sat_guarded_non_collapsed_types:        0
% 2.16/1.00  num_pure_diseq_elim:                    0
% 2.16/1.00  simp_replaced_by:                       0
% 2.16/1.00  res_preprocessed:                       110
% 2.16/1.00  prep_upred:                             0
% 2.16/1.00  prep_unflattend:                        2
% 2.16/1.00  smt_new_axioms:                         0
% 2.16/1.00  pred_elim_cands:                        3
% 2.16/1.00  pred_elim:                              1
% 2.16/1.00  pred_elim_cl:                           1
% 2.16/1.00  pred_elim_cycles:                       3
% 2.16/1.00  merged_defs:                            0
% 2.16/1.00  merged_defs_ncl:                        0
% 2.16/1.00  bin_hyper_res:                          0
% 2.16/1.00  prep_cycles:                            4
% 2.16/1.00  pred_elim_time:                         0.004
% 2.16/1.00  splitting_time:                         0.
% 2.16/1.00  sem_filter_time:                        0.
% 2.16/1.00  monotx_time:                            0.
% 2.16/1.00  subtype_inf_time:                       0.
% 2.16/1.00  
% 2.16/1.00  ------ Problem properties
% 2.16/1.00  
% 2.16/1.00  clauses:                                21
% 2.16/1.00  conjectures:                            4
% 2.16/1.00  epr:                                    2
% 2.16/1.00  horn:                                   20
% 2.16/1.00  ground:                                 6
% 2.16/1.00  unary:                                  5
% 2.16/1.00  binary:                                 4
% 2.16/1.00  lits:                                   72
% 2.16/1.00  lits_eq:                                9
% 2.16/1.00  fd_pure:                                0
% 2.16/1.00  fd_pseudo:                              0
% 2.16/1.00  fd_cond:                                0
% 2.16/1.00  fd_pseudo_cond:                         3
% 2.16/1.00  ac_symbols:                             0
% 2.16/1.00  
% 2.16/1.00  ------ Propositional Solver
% 2.16/1.00  
% 2.16/1.00  prop_solver_calls:                      28
% 2.16/1.00  prop_fast_solver_calls:                 982
% 2.16/1.00  smt_solver_calls:                       0
% 2.16/1.00  smt_fast_solver_calls:                  0
% 2.16/1.00  prop_num_of_clauses:                    2259
% 2.16/1.00  prop_preprocess_simplified:             6303
% 2.16/1.00  prop_fo_subsumed:                       21
% 2.16/1.00  prop_solver_time:                       0.
% 2.16/1.00  smt_solver_time:                        0.
% 2.16/1.00  smt_fast_solver_time:                   0.
% 2.16/1.00  prop_fast_solver_time:                  0.
% 2.16/1.00  prop_unsat_core_time:                   0.
% 2.16/1.00  
% 2.16/1.00  ------ QBF
% 2.16/1.00  
% 2.16/1.00  qbf_q_res:                              0
% 2.16/1.00  qbf_num_tautologies:                    0
% 2.16/1.00  qbf_prep_cycles:                        0
% 2.16/1.00  
% 2.16/1.00  ------ BMC1
% 2.16/1.00  
% 2.16/1.00  bmc1_current_bound:                     -1
% 2.16/1.00  bmc1_last_solved_bound:                 -1
% 2.16/1.00  bmc1_unsat_core_size:                   -1
% 2.16/1.00  bmc1_unsat_core_parents_size:           -1
% 2.16/1.00  bmc1_merge_next_fun:                    0
% 2.16/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation
% 2.16/1.00  
% 2.16/1.00  inst_num_of_clauses:                    701
% 2.16/1.00  inst_num_in_passive:                    235
% 2.16/1.00  inst_num_in_active:                     348
% 2.16/1.00  inst_num_in_unprocessed:                117
% 2.16/1.00  inst_num_of_loops:                      379
% 2.16/1.00  inst_num_of_learning_restarts:          0
% 2.16/1.00  inst_num_moves_active_passive:          26
% 2.16/1.00  inst_lit_activity:                      0
% 2.16/1.00  inst_lit_activity_moves:                0
% 2.16/1.00  inst_num_tautologies:                   0
% 2.16/1.00  inst_num_prop_implied:                  0
% 2.16/1.00  inst_num_existing_simplified:           0
% 2.16/1.00  inst_num_eq_res_simplified:             0
% 2.16/1.00  inst_num_child_elim:                    0
% 2.16/1.00  inst_num_of_dismatching_blockings:      158
% 2.16/1.00  inst_num_of_non_proper_insts:           621
% 2.16/1.00  inst_num_of_duplicates:                 0
% 2.16/1.00  inst_inst_num_from_inst_to_res:         0
% 2.16/1.00  inst_dismatching_checking_time:         0.
% 2.16/1.00  
% 2.16/1.00  ------ Resolution
% 2.16/1.00  
% 2.16/1.00  res_num_of_clauses:                     0
% 2.16/1.00  res_num_in_passive:                     0
% 2.16/1.00  res_num_in_active:                      0
% 2.16/1.00  res_num_of_loops:                       114
% 2.16/1.00  res_forward_subset_subsumed:            73
% 2.16/1.00  res_backward_subset_subsumed:           0
% 2.16/1.00  res_forward_subsumed:                   0
% 2.16/1.00  res_backward_subsumed:                  0
% 2.16/1.00  res_forward_subsumption_resolution:     0
% 2.16/1.00  res_backward_subsumption_resolution:    0
% 2.16/1.00  res_clause_to_clause_subsumption:       691
% 2.16/1.00  res_orphan_elimination:                 0
% 2.16/1.00  res_tautology_del:                      95
% 2.16/1.00  res_num_eq_res_simplified:              0
% 2.16/1.00  res_num_sel_changes:                    0
% 2.16/1.00  res_moves_from_active_to_pass:          0
% 2.16/1.00  
% 2.16/1.00  ------ Superposition
% 2.16/1.00  
% 2.16/1.00  sup_time_total:                         0.
% 2.16/1.00  sup_time_generating:                    0.
% 2.16/1.00  sup_time_sim_full:                      0.
% 2.16/1.00  sup_time_sim_immed:                     0.
% 2.16/1.00  
% 2.16/1.00  sup_num_of_clauses:                     150
% 2.16/1.00  sup_num_in_active:                      70
% 2.16/1.00  sup_num_in_passive:                     80
% 2.16/1.00  sup_num_of_loops:                       74
% 2.16/1.00  sup_fw_superposition:                   77
% 2.16/1.00  sup_bw_superposition:                   61
% 2.16/1.00  sup_immediate_simplified:               27
% 2.16/1.00  sup_given_eliminated:                   0
% 2.16/1.00  comparisons_done:                       0
% 2.16/1.00  comparisons_avoided:                    0
% 2.16/1.00  
% 2.16/1.00  ------ Simplifications
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  sim_fw_subset_subsumed:                 1
% 2.16/1.00  sim_bw_subset_subsumed:                 0
% 2.16/1.00  sim_fw_subsumed:                        1
% 2.16/1.00  sim_bw_subsumed:                        0
% 2.16/1.00  sim_fw_subsumption_res:                 2
% 2.16/1.00  sim_bw_subsumption_res:                 0
% 2.16/1.00  sim_tautology_del:                      6
% 2.16/1.00  sim_eq_tautology_del:                   1
% 2.16/1.00  sim_eq_res_simp:                        0
% 2.16/1.00  sim_fw_demodulated:                     0
% 2.16/1.00  sim_bw_demodulated:                     4
% 2.16/1.00  sim_light_normalised:                   31
% 2.16/1.00  sim_joinable_taut:                      0
% 2.16/1.00  sim_joinable_simp:                      0
% 2.16/1.00  sim_ac_normalised:                      0
% 2.16/1.00  sim_smt_subsumption:                    0
% 2.16/1.00  
%------------------------------------------------------------------------------
