%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:41 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 990 expanded)
%              Number of clauses        :   92 ( 266 expanded)
%              Number of leaves         :   13 ( 238 expanded)
%              Depth                    :   19
%              Number of atoms          :  559 (9826 expanded)
%              Number of equality atoms :  297 (4683 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2,X3] :
                  ( ( r2_hidden(X3,k1_relat_1(X1))
                    & r2_hidden(X2,k1_relat_1(X0)) )
                 => ( k1_funct_1(X0,X2) = X3
                  <=> k1_funct_1(X1,X3) = X2 ) )
              & k2_relat_1(X0) = k1_relat_1(X1)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( ! [X2,X3] :
                    ( ( r2_hidden(X3,k1_relat_1(X1))
                      & r2_hidden(X2,k1_relat_1(X0)) )
                   => ( k1_funct_1(X0,X2) = X3
                    <=> k1_funct_1(X1,X3) = X2 ) )
                & k2_relat_1(X0) = k1_relat_1(X1)
                & k2_relat_1(X1) = k1_relat_1(X0)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( ( k1_funct_1(X0,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(X0,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( ( k1_funct_1(X0,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(X0,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k2_relat_1(X1) = k1_relat_1(X0)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k2_funct_1(X0) != sK2
        & ! [X3,X2] :
            ( ( ( k1_funct_1(X0,X2) = X3
                | k1_funct_1(sK2,X3) != X2 )
              & ( k1_funct_1(sK2,X3) = X2
                | k1_funct_1(X0,X2) != X3 ) )
            | ~ r2_hidden(X3,k1_relat_1(sK2))
            | ~ r2_hidden(X2,k1_relat_1(X0)) )
        & k2_relat_1(X0) = k1_relat_1(sK2)
        & k2_relat_1(sK2) = k1_relat_1(X0)
        & v2_funct_1(X0)
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & ! [X2,X3] :
                ( ( ( k1_funct_1(X0,X2) = X3
                    | k1_funct_1(X1,X3) != X2 )
                  & ( k1_funct_1(X1,X3) = X2
                    | k1_funct_1(X0,X2) != X3 ) )
                | ~ r2_hidden(X3,k1_relat_1(X1))
                | ~ r2_hidden(X2,k1_relat_1(X0)) )
            & k2_relat_1(X0) = k1_relat_1(X1)
            & k2_relat_1(X1) = k1_relat_1(X0)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK1) != X1
          & ! [X3,X2] :
              ( ( ( k1_funct_1(sK1,X2) = X3
                  | k1_funct_1(X1,X3) != X2 )
                & ( k1_funct_1(X1,X3) = X2
                  | k1_funct_1(sK1,X2) != X3 ) )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(sK1)) )
          & k2_relat_1(sK1) = k1_relat_1(X1)
          & k2_relat_1(X1) = k1_relat_1(sK1)
          & v2_funct_1(sK1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k2_funct_1(sK1) != sK2
    & ! [X2,X3] :
        ( ( ( k1_funct_1(sK1,X2) = X3
            | k1_funct_1(sK2,X3) != X2 )
          & ( k1_funct_1(sK2,X3) = X2
            | k1_funct_1(sK1,X2) != X3 ) )
        | ~ r2_hidden(X3,k1_relat_1(sK2))
        | ~ r2_hidden(X2,k1_relat_1(sK1)) )
    & k2_relat_1(sK1) = k1_relat_1(sK2)
    & k2_relat_1(sK2) = k1_relat_1(sK1)
    & v2_funct_1(sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).

fof(f64,plain,(
    k2_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
            & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f34])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X0] :
      ( v1_funct_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f48,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    k2_funct_1(sK1) != sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    k2_relat_1(sK2) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK1,X2) = X3
      | k1_funct_1(sK2,X3) != X2
      | ~ r2_hidden(X3,k1_relat_1(sK2))
      | ~ r2_hidden(X2,k1_relat_1(sK1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,k1_funct_1(sK2,X3)) = X3
      | ~ r2_hidden(X3,k1_relat_1(sK2))
      | ~ r2_hidden(k1_funct_1(sK2,X3),k1_relat_1(sK1)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_21,negated_conjecture,
    ( k2_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_499,negated_conjecture,
    ( k2_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_27,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_494,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_940,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_512,plain,
    ( ~ v1_relat_1(X0_44)
    | k1_relat_1(k4_relat_1(X0_44)) = k2_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_926,plain,
    ( k1_relat_1(k4_relat_1(X0_44)) = k2_relat_1(X0_44)
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_1589,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_940,c_926])).

cnf(c_17,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_503,plain,
    ( r2_hidden(sK0(X0_44,X1_44),k1_relat_1(X0_44))
    | ~ v1_funct_1(X0_44)
    | ~ v1_funct_1(X1_44)
    | ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(X1_44)
    | X1_44 = X0_44
    | k1_relat_1(X1_44) != k1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_934,plain,
    ( X0_44 = X1_44
    | k1_relat_1(X0_44) != k1_relat_1(X1_44)
    | r2_hidden(sK0(X1_44,X0_44),k1_relat_1(X1_44)) = iProver_top
    | v1_funct_1(X0_44) != iProver_top
    | v1_funct_1(X1_44) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_3903,plain,
    ( k4_relat_1(sK1) = X0_44
    | k1_relat_1(X0_44) != k2_relat_1(sK1)
    | r2_hidden(sK0(X0_44,k4_relat_1(sK1)),k1_relat_1(X0_44)) = iProver_top
    | v1_funct_1(X0_44) != iProver_top
    | v1_funct_1(k4_relat_1(sK1)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(k4_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_934])).

cnf(c_28,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_29,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_32,plain,
    ( v2_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_54,plain,
    ( v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_56,plain,
    ( v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(k4_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k4_relat_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_57,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_relat_1(X0)) = iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_59,plain,
    ( v1_funct_1(k4_relat_1(sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_23970,plain,
    ( v1_relat_1(X0_44) != iProver_top
    | k4_relat_1(sK1) = X0_44
    | k1_relat_1(X0_44) != k2_relat_1(sK1)
    | r2_hidden(sK0(X0_44,k4_relat_1(sK1)),k1_relat_1(X0_44)) = iProver_top
    | v1_funct_1(X0_44) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3903,c_28,c_29,c_32,c_56,c_59])).

cnf(c_23971,plain,
    ( k4_relat_1(sK1) = X0_44
    | k1_relat_1(X0_44) != k2_relat_1(sK1)
    | r2_hidden(sK0(X0_44,k4_relat_1(sK1)),k1_relat_1(X0_44)) = iProver_top
    | v1_funct_1(X0_44) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(renaming,[status(thm)],[c_23970])).

cnf(c_23981,plain,
    ( k4_relat_1(sK1) = sK2
    | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_499,c_23971])).

cnf(c_24023,plain,
    ( k4_relat_1(sK1) = sK2
    | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k2_relat_1(sK1)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23981,c_499])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_290,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_291,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_67,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_293,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_291,c_27,c_26,c_23,c_67])).

cnf(c_492,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_293])).

cnf(c_18,negated_conjecture,
    ( k2_funct_1(sK1) != sK2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_502,negated_conjecture,
    ( k2_funct_1(sK1) != sK2 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_965,plain,
    ( k4_relat_1(sK1) != sK2 ),
    inference(demodulation,[status(thm)],[c_492,c_502])).

cnf(c_3906,plain,
    ( sK2 = X0_44
    | k1_relat_1(X0_44) != k2_relat_1(sK1)
    | r2_hidden(sK0(sK2,X0_44),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(X0_44) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_499,c_934])).

cnf(c_3979,plain,
    ( sK2 = X0_44
    | k1_relat_1(X0_44) != k2_relat_1(sK1)
    | r2_hidden(sK0(sK2,X0_44),k2_relat_1(sK1)) = iProver_top
    | v1_funct_1(X0_44) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0_44) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3906,c_499])).

cnf(c_25,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_30,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_31,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5333,plain,
    ( v1_relat_1(X0_44) != iProver_top
    | sK2 = X0_44
    | k1_relat_1(X0_44) != k2_relat_1(sK1)
    | r2_hidden(sK0(sK2,X0_44),k2_relat_1(sK1)) = iProver_top
    | v1_funct_1(X0_44) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3979,c_30,c_31])).

cnf(c_5334,plain,
    ( sK2 = X0_44
    | k1_relat_1(X0_44) != k2_relat_1(sK1)
    | r2_hidden(sK0(sK2,X0_44),k2_relat_1(sK1)) = iProver_top
    | v1_funct_1(X0_44) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(renaming,[status(thm)],[c_5333])).

cnf(c_5346,plain,
    ( k4_relat_1(sK1) = sK2
    | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k2_relat_1(sK1)) = iProver_top
    | v1_funct_1(k4_relat_1(sK1)) != iProver_top
    | v1_relat_1(k4_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_5334])).

cnf(c_24035,plain,
    ( r2_hidden(sK0(sK2,k4_relat_1(sK1)),k2_relat_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24023,c_28,c_29,c_32,c_56,c_59,c_965,c_5346])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_505,plain,
    ( ~ r2_hidden(X0_42,k1_relat_1(X0_44))
    | r2_hidden(k1_funct_1(X0_44,X0_42),k2_relat_1(X0_44))
    | ~ v1_funct_1(X0_44)
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_932,plain,
    ( r2_hidden(X0_42,k1_relat_1(X0_44)) != iProver_top
    | r2_hidden(k1_funct_1(X0_44,X0_42),k2_relat_1(X0_44)) = iProver_top
    | v1_funct_1(X0_44) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_298,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_299,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_303,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_299,c_27,c_26])).

cnf(c_491,plain,
    ( ~ r2_hidden(X0_42,k1_relat_1(sK1))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0_42)) = X0_42 ),
    inference(subtyping,[status(esa)],[c_303])).

cnf(c_942,plain,
    ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0_42)) = X0_42
    | r2_hidden(X0_42,k1_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_22,negated_conjecture,
    ( k2_relat_1(sK2) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_498,negated_conjecture,
    ( k2_relat_1(sK2) = k1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_995,plain,
    ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0_42)) = X0_42
    | r2_hidden(X0_42,k2_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_942,c_492,c_498])).

cnf(c_2438,plain,
    ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,k1_funct_1(sK2,X0_42))) = k1_funct_1(sK2,X0_42)
    | r2_hidden(X0_42,k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_932,c_995])).

cnf(c_2465,plain,
    ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,k1_funct_1(sK2,X0_42))) = k1_funct_1(sK2,X0_42)
    | r2_hidden(X0_42,k2_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2438,c_499])).

cnf(c_2721,plain,
    ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,k1_funct_1(sK2,X0_42))) = k1_funct_1(sK2,X0_42)
    | r2_hidden(X0_42,k2_relat_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2465,c_30,c_31])).

cnf(c_24146,plain,
    ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1))))) = k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1))) ),
    inference(superposition,[status(thm)],[c_24035,c_2721])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,X0),k1_relat_1(sK1))
    | k1_funct_1(sK1,k1_funct_1(sK2,X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_501,negated_conjecture,
    ( ~ r2_hidden(X0_42,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,X0_42),k1_relat_1(sK1))
    | k1_funct_1(sK1,k1_funct_1(sK2,X0_42)) = X0_42 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_935,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,X0_42)) = X0_42
    | r2_hidden(X0_42,k1_relat_1(sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK2,X0_42),k1_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_1011,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,X0_42)) = X0_42
    | r2_hidden(X0_42,k2_relat_1(sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK2,X0_42),k2_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_935,c_498,c_499])).

cnf(c_2439,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,X0_42)) = X0_42
    | r2_hidden(X0_42,k1_relat_1(sK2)) != iProver_top
    | r2_hidden(X0_42,k2_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_932,c_1011])).

cnf(c_2456,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,X0_42)) = X0_42
    | r2_hidden(X0_42,k2_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2439,c_499])).

cnf(c_2611,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,X0_42)) = X0_42
    | r2_hidden(X0_42,k2_relat_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2456,c_30,c_31])).

cnf(c_24148,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1)))) = sK0(sK2,k4_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_24035,c_2611])).

cnf(c_24152,plain,
    ( k1_funct_1(k4_relat_1(sK1),sK0(sK2,k4_relat_1(sK1))) = k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1))) ),
    inference(light_normalisation,[status(thm)],[c_24146,c_24148])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_504,plain,
    ( ~ v1_funct_1(X0_44)
    | ~ v1_funct_1(X1_44)
    | ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(X1_44)
    | X1_44 = X0_44
    | k1_relat_1(X1_44) != k1_relat_1(X0_44)
    | k1_funct_1(X1_44,sK0(X0_44,X1_44)) != k1_funct_1(X0_44,sK0(X0_44,X1_44)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1239,plain,
    ( ~ v1_funct_1(X0_44)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(X0_44)
    | ~ v1_relat_1(sK2)
    | X0_44 = sK2
    | k1_relat_1(X0_44) != k1_relat_1(sK2)
    | k1_funct_1(X0_44,sK0(sK2,X0_44)) != k1_funct_1(sK2,sK0(sK2,X0_44)) ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_5409,plain,
    ( ~ v1_funct_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | k4_relat_1(sK1) = sK2
    | k1_relat_1(k4_relat_1(sK1)) != k1_relat_1(sK2)
    | k1_funct_1(k4_relat_1(sK1),sK0(sK2,k4_relat_1(sK1))) != k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_1239])).

cnf(c_521,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_2113,plain,
    ( X0_43 != X1_43
    | k1_relat_1(X0_44) != X1_43
    | k1_relat_1(X0_44) = X0_43 ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_2703,plain,
    ( X0_43 != k2_relat_1(X0_44)
    | k1_relat_1(k4_relat_1(X0_44)) = X0_43
    | k1_relat_1(k4_relat_1(X0_44)) != k2_relat_1(X0_44) ),
    inference(instantiation,[status(thm)],[c_2113])).

cnf(c_4988,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(sK2)
    | k1_relat_1(k4_relat_1(sK1)) != k2_relat_1(sK1)
    | k1_relat_1(sK2) != k2_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2703])).

cnf(c_1308,plain,
    ( X0_43 != X1_43
    | k1_relat_1(sK2) != X1_43
    | k1_relat_1(sK2) = X0_43 ),
    inference(instantiation,[status(thm)],[c_521])).

cnf(c_1498,plain,
    ( X0_43 != k1_relat_1(sK2)
    | k1_relat_1(sK2) = X0_43
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_2242,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1498])).

cnf(c_526,plain,
    ( X0_44 != X1_44
    | k1_relat_1(X0_44) = k1_relat_1(X1_44) ),
    theory(equality)).

cnf(c_1219,plain,
    ( sK2 != X0_44
    | k1_relat_1(sK2) = k1_relat_1(X0_44) ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_1270,plain,
    ( sK2 != sK2
    | k1_relat_1(sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_519,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_1190,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_519])).

cnf(c_555,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(k4_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_512])).

cnf(c_58,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_55,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | v1_relat_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24152,c_5409,c_4988,c_2242,c_1270,c_1190,c_965,c_499,c_555,c_58,c_55,c_23,c_24,c_25,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:55:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.66/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.66/1.48  
% 7.66/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.66/1.48  
% 7.66/1.48  ------  iProver source info
% 7.66/1.48  
% 7.66/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.66/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.66/1.48  git: non_committed_changes: false
% 7.66/1.48  git: last_make_outside_of_git: false
% 7.66/1.48  
% 7.66/1.48  ------ 
% 7.66/1.48  
% 7.66/1.48  ------ Input Options
% 7.66/1.48  
% 7.66/1.48  --out_options                           all
% 7.66/1.48  --tptp_safe_out                         true
% 7.66/1.48  --problem_path                          ""
% 7.66/1.48  --include_path                          ""
% 7.66/1.48  --clausifier                            res/vclausify_rel
% 7.66/1.48  --clausifier_options                    --mode clausify
% 7.66/1.48  --stdin                                 false
% 7.66/1.48  --stats_out                             all
% 7.66/1.48  
% 7.66/1.48  ------ General Options
% 7.66/1.48  
% 7.66/1.48  --fof                                   false
% 7.66/1.48  --time_out_real                         305.
% 7.66/1.48  --time_out_virtual                      -1.
% 7.66/1.48  --symbol_type_check                     false
% 7.66/1.48  --clausify_out                          false
% 7.66/1.48  --sig_cnt_out                           false
% 7.66/1.48  --trig_cnt_out                          false
% 7.66/1.48  --trig_cnt_out_tolerance                1.
% 7.66/1.48  --trig_cnt_out_sk_spl                   false
% 7.66/1.48  --abstr_cl_out                          false
% 7.66/1.48  
% 7.66/1.48  ------ Global Options
% 7.66/1.48  
% 7.66/1.48  --schedule                              default
% 7.66/1.48  --add_important_lit                     false
% 7.66/1.48  --prop_solver_per_cl                    1000
% 7.66/1.48  --min_unsat_core                        false
% 7.66/1.48  --soft_assumptions                      false
% 7.66/1.48  --soft_lemma_size                       3
% 7.66/1.48  --prop_impl_unit_size                   0
% 7.66/1.48  --prop_impl_unit                        []
% 7.66/1.48  --share_sel_clauses                     true
% 7.66/1.48  --reset_solvers                         false
% 7.66/1.48  --bc_imp_inh                            [conj_cone]
% 7.66/1.48  --conj_cone_tolerance                   3.
% 7.66/1.48  --extra_neg_conj                        none
% 7.66/1.48  --large_theory_mode                     true
% 7.66/1.48  --prolific_symb_bound                   200
% 7.66/1.48  --lt_threshold                          2000
% 7.66/1.48  --clause_weak_htbl                      true
% 7.66/1.48  --gc_record_bc_elim                     false
% 7.66/1.48  
% 7.66/1.48  ------ Preprocessing Options
% 7.66/1.48  
% 7.66/1.48  --preprocessing_flag                    true
% 7.66/1.48  --time_out_prep_mult                    0.1
% 7.66/1.48  --splitting_mode                        input
% 7.66/1.48  --splitting_grd                         true
% 7.66/1.48  --splitting_cvd                         false
% 7.66/1.48  --splitting_cvd_svl                     false
% 7.66/1.48  --splitting_nvd                         32
% 7.66/1.48  --sub_typing                            true
% 7.66/1.48  --prep_gs_sim                           true
% 7.66/1.48  --prep_unflatten                        true
% 7.66/1.48  --prep_res_sim                          true
% 7.66/1.48  --prep_upred                            true
% 7.66/1.48  --prep_sem_filter                       exhaustive
% 7.66/1.48  --prep_sem_filter_out                   false
% 7.66/1.48  --pred_elim                             true
% 7.66/1.48  --res_sim_input                         true
% 7.66/1.48  --eq_ax_congr_red                       true
% 7.66/1.48  --pure_diseq_elim                       true
% 7.66/1.48  --brand_transform                       false
% 7.66/1.48  --non_eq_to_eq                          false
% 7.66/1.48  --prep_def_merge                        true
% 7.66/1.48  --prep_def_merge_prop_impl              false
% 7.66/1.48  --prep_def_merge_mbd                    true
% 7.66/1.48  --prep_def_merge_tr_red                 false
% 7.66/1.48  --prep_def_merge_tr_cl                  false
% 7.66/1.48  --smt_preprocessing                     true
% 7.66/1.48  --smt_ac_axioms                         fast
% 7.66/1.48  --preprocessed_out                      false
% 7.66/1.48  --preprocessed_stats                    false
% 7.66/1.48  
% 7.66/1.48  ------ Abstraction refinement Options
% 7.66/1.48  
% 7.66/1.48  --abstr_ref                             []
% 7.66/1.48  --abstr_ref_prep                        false
% 7.66/1.48  --abstr_ref_until_sat                   false
% 7.66/1.48  --abstr_ref_sig_restrict                funpre
% 7.66/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.66/1.48  --abstr_ref_under                       []
% 7.66/1.48  
% 7.66/1.48  ------ SAT Options
% 7.66/1.48  
% 7.66/1.48  --sat_mode                              false
% 7.66/1.48  --sat_fm_restart_options                ""
% 7.66/1.48  --sat_gr_def                            false
% 7.66/1.48  --sat_epr_types                         true
% 7.66/1.48  --sat_non_cyclic_types                  false
% 7.66/1.48  --sat_finite_models                     false
% 7.66/1.48  --sat_fm_lemmas                         false
% 7.66/1.48  --sat_fm_prep                           false
% 7.66/1.48  --sat_fm_uc_incr                        true
% 7.66/1.48  --sat_out_model                         small
% 7.66/1.48  --sat_out_clauses                       false
% 7.66/1.48  
% 7.66/1.48  ------ QBF Options
% 7.66/1.48  
% 7.66/1.48  --qbf_mode                              false
% 7.66/1.48  --qbf_elim_univ                         false
% 7.66/1.48  --qbf_dom_inst                          none
% 7.66/1.48  --qbf_dom_pre_inst                      false
% 7.66/1.48  --qbf_sk_in                             false
% 7.66/1.48  --qbf_pred_elim                         true
% 7.66/1.48  --qbf_split                             512
% 7.66/1.48  
% 7.66/1.48  ------ BMC1 Options
% 7.66/1.48  
% 7.66/1.48  --bmc1_incremental                      false
% 7.66/1.48  --bmc1_axioms                           reachable_all
% 7.66/1.48  --bmc1_min_bound                        0
% 7.66/1.48  --bmc1_max_bound                        -1
% 7.66/1.48  --bmc1_max_bound_default                -1
% 7.66/1.48  --bmc1_symbol_reachability              true
% 7.66/1.48  --bmc1_property_lemmas                  false
% 7.66/1.48  --bmc1_k_induction                      false
% 7.66/1.48  --bmc1_non_equiv_states                 false
% 7.66/1.48  --bmc1_deadlock                         false
% 7.66/1.48  --bmc1_ucm                              false
% 7.66/1.48  --bmc1_add_unsat_core                   none
% 7.66/1.48  --bmc1_unsat_core_children              false
% 7.66/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.66/1.48  --bmc1_out_stat                         full
% 7.66/1.48  --bmc1_ground_init                      false
% 7.66/1.48  --bmc1_pre_inst_next_state              false
% 7.66/1.48  --bmc1_pre_inst_state                   false
% 7.66/1.48  --bmc1_pre_inst_reach_state             false
% 7.66/1.48  --bmc1_out_unsat_core                   false
% 7.66/1.48  --bmc1_aig_witness_out                  false
% 7.66/1.48  --bmc1_verbose                          false
% 7.66/1.48  --bmc1_dump_clauses_tptp                false
% 7.66/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.66/1.48  --bmc1_dump_file                        -
% 7.66/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.66/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.66/1.48  --bmc1_ucm_extend_mode                  1
% 7.66/1.48  --bmc1_ucm_init_mode                    2
% 7.66/1.48  --bmc1_ucm_cone_mode                    none
% 7.66/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.66/1.48  --bmc1_ucm_relax_model                  4
% 7.66/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.66/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.66/1.48  --bmc1_ucm_layered_model                none
% 7.66/1.48  --bmc1_ucm_max_lemma_size               10
% 7.66/1.48  
% 7.66/1.48  ------ AIG Options
% 7.66/1.48  
% 7.66/1.48  --aig_mode                              false
% 7.66/1.48  
% 7.66/1.48  ------ Instantiation Options
% 7.66/1.48  
% 7.66/1.48  --instantiation_flag                    true
% 7.66/1.48  --inst_sos_flag                         false
% 7.66/1.48  --inst_sos_phase                        true
% 7.66/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.66/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.66/1.48  --inst_lit_sel_side                     num_symb
% 7.66/1.48  --inst_solver_per_active                1400
% 7.66/1.48  --inst_solver_calls_frac                1.
% 7.66/1.48  --inst_passive_queue_type               priority_queues
% 7.66/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.66/1.48  --inst_passive_queues_freq              [25;2]
% 7.66/1.48  --inst_dismatching                      true
% 7.66/1.48  --inst_eager_unprocessed_to_passive     true
% 7.66/1.48  --inst_prop_sim_given                   true
% 7.66/1.48  --inst_prop_sim_new                     false
% 7.66/1.48  --inst_subs_new                         false
% 7.66/1.48  --inst_eq_res_simp                      false
% 7.66/1.48  --inst_subs_given                       false
% 7.66/1.48  --inst_orphan_elimination               true
% 7.66/1.48  --inst_learning_loop_flag               true
% 7.66/1.48  --inst_learning_start                   3000
% 7.66/1.48  --inst_learning_factor                  2
% 7.66/1.48  --inst_start_prop_sim_after_learn       3
% 7.66/1.48  --inst_sel_renew                        solver
% 7.66/1.48  --inst_lit_activity_flag                true
% 7.66/1.48  --inst_restr_to_given                   false
% 7.66/1.48  --inst_activity_threshold               500
% 7.66/1.48  --inst_out_proof                        true
% 7.66/1.48  
% 7.66/1.48  ------ Resolution Options
% 7.66/1.48  
% 7.66/1.48  --resolution_flag                       true
% 7.66/1.48  --res_lit_sel                           adaptive
% 7.66/1.48  --res_lit_sel_side                      none
% 7.66/1.48  --res_ordering                          kbo
% 7.66/1.48  --res_to_prop_solver                    active
% 7.66/1.48  --res_prop_simpl_new                    false
% 7.66/1.48  --res_prop_simpl_given                  true
% 7.66/1.48  --res_passive_queue_type                priority_queues
% 7.66/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.66/1.48  --res_passive_queues_freq               [15;5]
% 7.66/1.48  --res_forward_subs                      full
% 7.66/1.48  --res_backward_subs                     full
% 7.66/1.48  --res_forward_subs_resolution           true
% 7.66/1.48  --res_backward_subs_resolution          true
% 7.66/1.48  --res_orphan_elimination                true
% 7.66/1.48  --res_time_limit                        2.
% 7.66/1.48  --res_out_proof                         true
% 7.66/1.48  
% 7.66/1.48  ------ Superposition Options
% 7.66/1.48  
% 7.66/1.48  --superposition_flag                    true
% 7.66/1.48  --sup_passive_queue_type                priority_queues
% 7.66/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.66/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.66/1.48  --demod_completeness_check              fast
% 7.66/1.48  --demod_use_ground                      true
% 7.66/1.48  --sup_to_prop_solver                    passive
% 7.66/1.48  --sup_prop_simpl_new                    true
% 7.66/1.48  --sup_prop_simpl_given                  true
% 7.66/1.48  --sup_fun_splitting                     false
% 7.66/1.48  --sup_smt_interval                      50000
% 7.66/1.48  
% 7.66/1.48  ------ Superposition Simplification Setup
% 7.66/1.48  
% 7.66/1.48  --sup_indices_passive                   []
% 7.66/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.66/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.48  --sup_full_bw                           [BwDemod]
% 7.66/1.48  --sup_immed_triv                        [TrivRules]
% 7.66/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.48  --sup_immed_bw_main                     []
% 7.66/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.66/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.48  
% 7.66/1.48  ------ Combination Options
% 7.66/1.48  
% 7.66/1.48  --comb_res_mult                         3
% 7.66/1.48  --comb_sup_mult                         2
% 7.66/1.48  --comb_inst_mult                        10
% 7.66/1.48  
% 7.66/1.48  ------ Debug Options
% 7.66/1.48  
% 7.66/1.48  --dbg_backtrace                         false
% 7.66/1.48  --dbg_dump_prop_clauses                 false
% 7.66/1.48  --dbg_dump_prop_clauses_file            -
% 7.66/1.48  --dbg_out_stat                          false
% 7.66/1.48  ------ Parsing...
% 7.66/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.66/1.48  
% 7.66/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.66/1.48  
% 7.66/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.66/1.48  
% 7.66/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.66/1.48  ------ Proving...
% 7.66/1.48  ------ Problem Properties 
% 7.66/1.48  
% 7.66/1.48  
% 7.66/1.48  clauses                                 26
% 7.66/1.48  conjectures                             9
% 7.66/1.48  EPR                                     4
% 7.66/1.48  Horn                                    25
% 7.66/1.48  unary                                   12
% 7.66/1.48  binary                                  8
% 7.66/1.48  lits                                    55
% 7.66/1.48  lits eq                                 20
% 7.66/1.48  fd_pure                                 0
% 7.66/1.48  fd_pseudo                               0
% 7.66/1.48  fd_cond                                 0
% 7.66/1.48  fd_pseudo_cond                          2
% 7.66/1.48  AC symbols                              0
% 7.66/1.48  
% 7.66/1.48  ------ Schedule dynamic 5 is on 
% 7.66/1.48  
% 7.66/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.66/1.48  
% 7.66/1.48  
% 7.66/1.48  ------ 
% 7.66/1.48  Current options:
% 7.66/1.48  ------ 
% 7.66/1.48  
% 7.66/1.48  ------ Input Options
% 7.66/1.48  
% 7.66/1.48  --out_options                           all
% 7.66/1.48  --tptp_safe_out                         true
% 7.66/1.48  --problem_path                          ""
% 7.66/1.48  --include_path                          ""
% 7.66/1.48  --clausifier                            res/vclausify_rel
% 7.66/1.48  --clausifier_options                    --mode clausify
% 7.66/1.48  --stdin                                 false
% 7.66/1.48  --stats_out                             all
% 7.66/1.48  
% 7.66/1.48  ------ General Options
% 7.66/1.48  
% 7.66/1.48  --fof                                   false
% 7.66/1.48  --time_out_real                         305.
% 7.66/1.48  --time_out_virtual                      -1.
% 7.66/1.48  --symbol_type_check                     false
% 7.66/1.48  --clausify_out                          false
% 7.66/1.48  --sig_cnt_out                           false
% 7.66/1.48  --trig_cnt_out                          false
% 7.66/1.48  --trig_cnt_out_tolerance                1.
% 7.66/1.48  --trig_cnt_out_sk_spl                   false
% 7.66/1.48  --abstr_cl_out                          false
% 7.66/1.48  
% 7.66/1.48  ------ Global Options
% 7.66/1.48  
% 7.66/1.48  --schedule                              default
% 7.66/1.48  --add_important_lit                     false
% 7.66/1.48  --prop_solver_per_cl                    1000
% 7.66/1.48  --min_unsat_core                        false
% 7.66/1.48  --soft_assumptions                      false
% 7.66/1.48  --soft_lemma_size                       3
% 7.66/1.48  --prop_impl_unit_size                   0
% 7.66/1.48  --prop_impl_unit                        []
% 7.66/1.48  --share_sel_clauses                     true
% 7.66/1.48  --reset_solvers                         false
% 7.66/1.48  --bc_imp_inh                            [conj_cone]
% 7.66/1.48  --conj_cone_tolerance                   3.
% 7.66/1.48  --extra_neg_conj                        none
% 7.66/1.48  --large_theory_mode                     true
% 7.66/1.48  --prolific_symb_bound                   200
% 7.66/1.48  --lt_threshold                          2000
% 7.66/1.48  --clause_weak_htbl                      true
% 7.66/1.48  --gc_record_bc_elim                     false
% 7.66/1.48  
% 7.66/1.48  ------ Preprocessing Options
% 7.66/1.48  
% 7.66/1.48  --preprocessing_flag                    true
% 7.66/1.48  --time_out_prep_mult                    0.1
% 7.66/1.48  --splitting_mode                        input
% 7.66/1.48  --splitting_grd                         true
% 7.66/1.48  --splitting_cvd                         false
% 7.66/1.48  --splitting_cvd_svl                     false
% 7.66/1.48  --splitting_nvd                         32
% 7.66/1.48  --sub_typing                            true
% 7.66/1.48  --prep_gs_sim                           true
% 7.66/1.48  --prep_unflatten                        true
% 7.66/1.48  --prep_res_sim                          true
% 7.66/1.48  --prep_upred                            true
% 7.66/1.48  --prep_sem_filter                       exhaustive
% 7.66/1.48  --prep_sem_filter_out                   false
% 7.66/1.48  --pred_elim                             true
% 7.66/1.48  --res_sim_input                         true
% 7.66/1.48  --eq_ax_congr_red                       true
% 7.66/1.48  --pure_diseq_elim                       true
% 7.66/1.48  --brand_transform                       false
% 7.66/1.48  --non_eq_to_eq                          false
% 7.66/1.48  --prep_def_merge                        true
% 7.66/1.48  --prep_def_merge_prop_impl              false
% 7.66/1.48  --prep_def_merge_mbd                    true
% 7.66/1.48  --prep_def_merge_tr_red                 false
% 7.66/1.48  --prep_def_merge_tr_cl                  false
% 7.66/1.48  --smt_preprocessing                     true
% 7.66/1.48  --smt_ac_axioms                         fast
% 7.66/1.48  --preprocessed_out                      false
% 7.66/1.48  --preprocessed_stats                    false
% 7.66/1.48  
% 7.66/1.48  ------ Abstraction refinement Options
% 7.66/1.48  
% 7.66/1.48  --abstr_ref                             []
% 7.66/1.48  --abstr_ref_prep                        false
% 7.66/1.48  --abstr_ref_until_sat                   false
% 7.66/1.48  --abstr_ref_sig_restrict                funpre
% 7.66/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.66/1.48  --abstr_ref_under                       []
% 7.66/1.48  
% 7.66/1.48  ------ SAT Options
% 7.66/1.48  
% 7.66/1.48  --sat_mode                              false
% 7.66/1.48  --sat_fm_restart_options                ""
% 7.66/1.48  --sat_gr_def                            false
% 7.66/1.48  --sat_epr_types                         true
% 7.66/1.48  --sat_non_cyclic_types                  false
% 7.66/1.48  --sat_finite_models                     false
% 7.66/1.48  --sat_fm_lemmas                         false
% 7.66/1.48  --sat_fm_prep                           false
% 7.66/1.48  --sat_fm_uc_incr                        true
% 7.66/1.48  --sat_out_model                         small
% 7.66/1.48  --sat_out_clauses                       false
% 7.66/1.48  
% 7.66/1.48  ------ QBF Options
% 7.66/1.48  
% 7.66/1.48  --qbf_mode                              false
% 7.66/1.48  --qbf_elim_univ                         false
% 7.66/1.48  --qbf_dom_inst                          none
% 7.66/1.48  --qbf_dom_pre_inst                      false
% 7.66/1.48  --qbf_sk_in                             false
% 7.66/1.48  --qbf_pred_elim                         true
% 7.66/1.48  --qbf_split                             512
% 7.66/1.48  
% 7.66/1.48  ------ BMC1 Options
% 7.66/1.48  
% 7.66/1.48  --bmc1_incremental                      false
% 7.66/1.48  --bmc1_axioms                           reachable_all
% 7.66/1.48  --bmc1_min_bound                        0
% 7.66/1.48  --bmc1_max_bound                        -1
% 7.66/1.48  --bmc1_max_bound_default                -1
% 7.66/1.48  --bmc1_symbol_reachability              true
% 7.66/1.48  --bmc1_property_lemmas                  false
% 7.66/1.48  --bmc1_k_induction                      false
% 7.66/1.48  --bmc1_non_equiv_states                 false
% 7.66/1.48  --bmc1_deadlock                         false
% 7.66/1.48  --bmc1_ucm                              false
% 7.66/1.48  --bmc1_add_unsat_core                   none
% 7.66/1.48  --bmc1_unsat_core_children              false
% 7.66/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.66/1.48  --bmc1_out_stat                         full
% 7.66/1.48  --bmc1_ground_init                      false
% 7.66/1.48  --bmc1_pre_inst_next_state              false
% 7.66/1.48  --bmc1_pre_inst_state                   false
% 7.66/1.48  --bmc1_pre_inst_reach_state             false
% 7.66/1.48  --bmc1_out_unsat_core                   false
% 7.66/1.48  --bmc1_aig_witness_out                  false
% 7.66/1.48  --bmc1_verbose                          false
% 7.66/1.48  --bmc1_dump_clauses_tptp                false
% 7.66/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.66/1.48  --bmc1_dump_file                        -
% 7.66/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.66/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.66/1.48  --bmc1_ucm_extend_mode                  1
% 7.66/1.48  --bmc1_ucm_init_mode                    2
% 7.66/1.48  --bmc1_ucm_cone_mode                    none
% 7.66/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.66/1.48  --bmc1_ucm_relax_model                  4
% 7.66/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.66/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.66/1.48  --bmc1_ucm_layered_model                none
% 7.66/1.48  --bmc1_ucm_max_lemma_size               10
% 7.66/1.48  
% 7.66/1.48  ------ AIG Options
% 7.66/1.48  
% 7.66/1.48  --aig_mode                              false
% 7.66/1.48  
% 7.66/1.48  ------ Instantiation Options
% 7.66/1.48  
% 7.66/1.48  --instantiation_flag                    true
% 7.66/1.48  --inst_sos_flag                         false
% 7.66/1.48  --inst_sos_phase                        true
% 7.66/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.66/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.66/1.48  --inst_lit_sel_side                     none
% 7.66/1.48  --inst_solver_per_active                1400
% 7.66/1.48  --inst_solver_calls_frac                1.
% 7.66/1.48  --inst_passive_queue_type               priority_queues
% 7.66/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.66/1.48  --inst_passive_queues_freq              [25;2]
% 7.66/1.48  --inst_dismatching                      true
% 7.66/1.48  --inst_eager_unprocessed_to_passive     true
% 7.66/1.48  --inst_prop_sim_given                   true
% 7.66/1.48  --inst_prop_sim_new                     false
% 7.66/1.48  --inst_subs_new                         false
% 7.66/1.48  --inst_eq_res_simp                      false
% 7.66/1.48  --inst_subs_given                       false
% 7.66/1.48  --inst_orphan_elimination               true
% 7.66/1.48  --inst_learning_loop_flag               true
% 7.66/1.48  --inst_learning_start                   3000
% 7.66/1.48  --inst_learning_factor                  2
% 7.66/1.48  --inst_start_prop_sim_after_learn       3
% 7.66/1.48  --inst_sel_renew                        solver
% 7.66/1.48  --inst_lit_activity_flag                true
% 7.66/1.48  --inst_restr_to_given                   false
% 7.66/1.48  --inst_activity_threshold               500
% 7.66/1.48  --inst_out_proof                        true
% 7.66/1.48  
% 7.66/1.48  ------ Resolution Options
% 7.66/1.48  
% 7.66/1.48  --resolution_flag                       false
% 7.66/1.48  --res_lit_sel                           adaptive
% 7.66/1.48  --res_lit_sel_side                      none
% 7.66/1.48  --res_ordering                          kbo
% 7.66/1.48  --res_to_prop_solver                    active
% 7.66/1.48  --res_prop_simpl_new                    false
% 7.66/1.48  --res_prop_simpl_given                  true
% 7.66/1.48  --res_passive_queue_type                priority_queues
% 7.66/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.66/1.48  --res_passive_queues_freq               [15;5]
% 7.66/1.48  --res_forward_subs                      full
% 7.66/1.48  --res_backward_subs                     full
% 7.66/1.48  --res_forward_subs_resolution           true
% 7.66/1.48  --res_backward_subs_resolution          true
% 7.66/1.48  --res_orphan_elimination                true
% 7.66/1.48  --res_time_limit                        2.
% 7.66/1.48  --res_out_proof                         true
% 7.66/1.48  
% 7.66/1.48  ------ Superposition Options
% 7.66/1.48  
% 7.66/1.48  --superposition_flag                    true
% 7.66/1.48  --sup_passive_queue_type                priority_queues
% 7.66/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.66/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.66/1.48  --demod_completeness_check              fast
% 7.66/1.48  --demod_use_ground                      true
% 7.66/1.48  --sup_to_prop_solver                    passive
% 7.66/1.48  --sup_prop_simpl_new                    true
% 7.66/1.48  --sup_prop_simpl_given                  true
% 7.66/1.48  --sup_fun_splitting                     false
% 7.66/1.48  --sup_smt_interval                      50000
% 7.66/1.48  
% 7.66/1.48  ------ Superposition Simplification Setup
% 7.66/1.48  
% 7.66/1.48  --sup_indices_passive                   []
% 7.66/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.66/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.48  --sup_full_bw                           [BwDemod]
% 7.66/1.48  --sup_immed_triv                        [TrivRules]
% 7.66/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.48  --sup_immed_bw_main                     []
% 7.66/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.66/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.48  
% 7.66/1.48  ------ Combination Options
% 7.66/1.48  
% 7.66/1.48  --comb_res_mult                         3
% 7.66/1.48  --comb_sup_mult                         2
% 7.66/1.48  --comb_inst_mult                        10
% 7.66/1.48  
% 7.66/1.48  ------ Debug Options
% 7.66/1.48  
% 7.66/1.48  --dbg_backtrace                         false
% 7.66/1.48  --dbg_dump_prop_clauses                 false
% 7.66/1.48  --dbg_dump_prop_clauses_file            -
% 7.66/1.48  --dbg_out_stat                          false
% 7.66/1.48  
% 7.66/1.48  
% 7.66/1.48  
% 7.66/1.48  
% 7.66/1.48  ------ Proving...
% 7.66/1.48  
% 7.66/1.48  
% 7.66/1.48  % SZS status Theorem for theBenchmark.p
% 7.66/1.48  
% 7.66/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.66/1.48  
% 7.66/1.48  fof(f14,conjecture,(
% 7.66/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 7.66/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f15,negated_conjecture,(
% 7.66/1.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 7.66/1.48    inference(negated_conjecture,[],[f14])).
% 7.66/1.48  
% 7.66/1.48  fof(f32,plain,(
% 7.66/1.48    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | (~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 7.66/1.48    inference(ennf_transformation,[],[f15])).
% 7.66/1.48  
% 7.66/1.48  fof(f33,plain,(
% 7.66/1.48    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.66/1.48    inference(flattening,[],[f32])).
% 7.66/1.48  
% 7.66/1.48  fof(f36,plain,(
% 7.66/1.48    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.66/1.48    inference(nnf_transformation,[],[f33])).
% 7.66/1.48  
% 7.66/1.48  fof(f38,plain,(
% 7.66/1.48    ( ! [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) != sK2 & ! [X3,X2] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(sK2,X3) != X2) & (k1_funct_1(sK2,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK2)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(sK2) & k2_relat_1(sK2) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(sK2) & v1_relat_1(sK2))) )),
% 7.66/1.48    introduced(choice_axiom,[])).
% 7.66/1.48  
% 7.66/1.48  fof(f37,plain,(
% 7.66/1.48    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : (((k1_funct_1(X0,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK1) != X1 & ! [X3,X2] : (((k1_funct_1(sK1,X2) = X3 | k1_funct_1(X1,X3) != X2) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(sK1,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(sK1))) & k2_relat_1(sK1) = k1_relat_1(X1) & k2_relat_1(X1) = k1_relat_1(sK1) & v2_funct_1(sK1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 7.66/1.48    introduced(choice_axiom,[])).
% 7.66/1.48  
% 7.66/1.48  fof(f39,plain,(
% 7.66/1.48    (k2_funct_1(sK1) != sK2 & ! [X2,X3] : (((k1_funct_1(sK1,X2) = X3 | k1_funct_1(sK2,X3) != X2) & (k1_funct_1(sK2,X3) = X2 | k1_funct_1(sK1,X2) != X3)) | ~r2_hidden(X3,k1_relat_1(sK2)) | ~r2_hidden(X2,k1_relat_1(sK1))) & k2_relat_1(sK1) = k1_relat_1(sK2) & k2_relat_1(sK2) = k1_relat_1(sK1) & v2_funct_1(sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 7.66/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).
% 7.66/1.48  
% 7.66/1.48  fof(f64,plain,(
% 7.66/1.48    k2_relat_1(sK1) = k1_relat_1(sK2)),
% 7.66/1.48    inference(cnf_transformation,[],[f39])).
% 7.66/1.48  
% 7.66/1.48  fof(f58,plain,(
% 7.66/1.48    v1_relat_1(sK1)),
% 7.66/1.48    inference(cnf_transformation,[],[f39])).
% 7.66/1.48  
% 7.66/1.48  fof(f3,axiom,(
% 7.66/1.48    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 7.66/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f18,plain,(
% 7.66/1.48    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.66/1.48    inference(ennf_transformation,[],[f3])).
% 7.66/1.48  
% 7.66/1.48  fof(f42,plain,(
% 7.66/1.48    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.66/1.48    inference(cnf_transformation,[],[f18])).
% 7.66/1.48  
% 7.66/1.48  fof(f13,axiom,(
% 7.66/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 7.66/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f30,plain,(
% 7.66/1.48    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.66/1.48    inference(ennf_transformation,[],[f13])).
% 7.66/1.48  
% 7.66/1.48  fof(f31,plain,(
% 7.66/1.48    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.66/1.48    inference(flattening,[],[f30])).
% 7.66/1.48  
% 7.66/1.48  fof(f34,plain,(
% 7.66/1.48    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 7.66/1.48    introduced(choice_axiom,[])).
% 7.66/1.48  
% 7.66/1.48  fof(f35,plain,(
% 7.66/1.48    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.66/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f34])).
% 7.66/1.48  
% 7.66/1.48  fof(f56,plain,(
% 7.66/1.48    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.66/1.48    inference(cnf_transformation,[],[f35])).
% 7.66/1.48  
% 7.66/1.48  fof(f59,plain,(
% 7.66/1.48    v1_funct_1(sK1)),
% 7.66/1.48    inference(cnf_transformation,[],[f39])).
% 7.66/1.48  
% 7.66/1.48  fof(f62,plain,(
% 7.66/1.48    v2_funct_1(sK1)),
% 7.66/1.48    inference(cnf_transformation,[],[f39])).
% 7.66/1.48  
% 7.66/1.48  fof(f10,axiom,(
% 7.66/1.48    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))))),
% 7.66/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f24,plain,(
% 7.66/1.48    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.66/1.48    inference(ennf_transformation,[],[f10])).
% 7.66/1.48  
% 7.66/1.48  fof(f25,plain,(
% 7.66/1.48    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.66/1.48    inference(flattening,[],[f24])).
% 7.66/1.48  
% 7.66/1.48  fof(f51,plain,(
% 7.66/1.48    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.66/1.48    inference(cnf_transformation,[],[f25])).
% 7.66/1.48  
% 7.66/1.48  fof(f52,plain,(
% 7.66/1.48    ( ! [X0] : (v1_funct_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.66/1.48    inference(cnf_transformation,[],[f25])).
% 7.66/1.48  
% 7.66/1.48  fof(f8,axiom,(
% 7.66/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 7.66/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f22,plain,(
% 7.66/1.48    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.66/1.48    inference(ennf_transformation,[],[f8])).
% 7.66/1.48  
% 7.66/1.48  fof(f23,plain,(
% 7.66/1.48    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.66/1.48    inference(flattening,[],[f22])).
% 7.66/1.48  
% 7.66/1.48  fof(f48,plain,(
% 7.66/1.48    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.66/1.48    inference(cnf_transformation,[],[f23])).
% 7.66/1.48  
% 7.66/1.48  fof(f67,plain,(
% 7.66/1.48    k2_funct_1(sK1) != sK2),
% 7.66/1.48    inference(cnf_transformation,[],[f39])).
% 7.66/1.48  
% 7.66/1.48  fof(f60,plain,(
% 7.66/1.48    v1_relat_1(sK2)),
% 7.66/1.48    inference(cnf_transformation,[],[f39])).
% 7.66/1.48  
% 7.66/1.48  fof(f61,plain,(
% 7.66/1.48    v1_funct_1(sK2)),
% 7.66/1.48    inference(cnf_transformation,[],[f39])).
% 7.66/1.48  
% 7.66/1.48  fof(f11,axiom,(
% 7.66/1.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 7.66/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f26,plain,(
% 7.66/1.48    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.66/1.48    inference(ennf_transformation,[],[f11])).
% 7.66/1.48  
% 7.66/1.48  fof(f27,plain,(
% 7.66/1.48    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.66/1.48    inference(flattening,[],[f26])).
% 7.66/1.48  
% 7.66/1.48  fof(f53,plain,(
% 7.66/1.48    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.66/1.48    inference(cnf_transformation,[],[f27])).
% 7.66/1.48  
% 7.66/1.48  fof(f12,axiom,(
% 7.66/1.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 7.66/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.48  
% 7.66/1.48  fof(f28,plain,(
% 7.66/1.48    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.66/1.48    inference(ennf_transformation,[],[f12])).
% 7.66/1.48  
% 7.66/1.48  fof(f29,plain,(
% 7.66/1.48    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.66/1.48    inference(flattening,[],[f28])).
% 7.66/1.48  
% 7.66/1.48  fof(f54,plain,(
% 7.66/1.48    ( ! [X0,X1] : (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.66/1.48    inference(cnf_transformation,[],[f29])).
% 7.66/1.48  
% 7.66/1.48  fof(f63,plain,(
% 7.66/1.48    k2_relat_1(sK2) = k1_relat_1(sK1)),
% 7.66/1.48    inference(cnf_transformation,[],[f39])).
% 7.66/1.48  
% 7.66/1.48  fof(f66,plain,(
% 7.66/1.48    ( ! [X2,X3] : (k1_funct_1(sK1,X2) = X3 | k1_funct_1(sK2,X3) != X2 | ~r2_hidden(X3,k1_relat_1(sK2)) | ~r2_hidden(X2,k1_relat_1(sK1))) )),
% 7.66/1.48    inference(cnf_transformation,[],[f39])).
% 7.66/1.48  
% 7.66/1.48  fof(f68,plain,(
% 7.66/1.48    ( ! [X3] : (k1_funct_1(sK1,k1_funct_1(sK2,X3)) = X3 | ~r2_hidden(X3,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,X3),k1_relat_1(sK1))) )),
% 7.66/1.48    inference(equality_resolution,[],[f66])).
% 7.66/1.48  
% 7.66/1.48  fof(f57,plain,(
% 7.66/1.48    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.66/1.48    inference(cnf_transformation,[],[f35])).
% 7.66/1.48  
% 7.66/1.48  cnf(c_21,negated_conjecture,
% 7.66/1.48      ( k2_relat_1(sK1) = k1_relat_1(sK2) ),
% 7.66/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_499,negated_conjecture,
% 7.66/1.48      ( k2_relat_1(sK1) = k1_relat_1(sK2) ),
% 7.66/1.48      inference(subtyping,[status(esa)],[c_21]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_27,negated_conjecture,
% 7.66/1.48      ( v1_relat_1(sK1) ),
% 7.66/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_494,negated_conjecture,
% 7.66/1.48      ( v1_relat_1(sK1) ),
% 7.66/1.48      inference(subtyping,[status(esa)],[c_27]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_940,plain,
% 7.66/1.48      ( v1_relat_1(sK1) = iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_3,plain,
% 7.66/1.48      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 7.66/1.48      inference(cnf_transformation,[],[f42]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_512,plain,
% 7.66/1.48      ( ~ v1_relat_1(X0_44)
% 7.66/1.48      | k1_relat_1(k4_relat_1(X0_44)) = k2_relat_1(X0_44) ),
% 7.66/1.48      inference(subtyping,[status(esa)],[c_3]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_926,plain,
% 7.66/1.48      ( k1_relat_1(k4_relat_1(X0_44)) = k2_relat_1(X0_44)
% 7.66/1.48      | v1_relat_1(X0_44) != iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_1589,plain,
% 7.66/1.48      ( k1_relat_1(k4_relat_1(sK1)) = k2_relat_1(sK1) ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_940,c_926]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_17,plain,
% 7.66/1.48      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 7.66/1.48      | ~ v1_funct_1(X0)
% 7.66/1.48      | ~ v1_funct_1(X1)
% 7.66/1.48      | ~ v1_relat_1(X0)
% 7.66/1.48      | ~ v1_relat_1(X1)
% 7.66/1.48      | X1 = X0
% 7.66/1.48      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 7.66/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_503,plain,
% 7.66/1.48      ( r2_hidden(sK0(X0_44,X1_44),k1_relat_1(X0_44))
% 7.66/1.48      | ~ v1_funct_1(X0_44)
% 7.66/1.48      | ~ v1_funct_1(X1_44)
% 7.66/1.48      | ~ v1_relat_1(X0_44)
% 7.66/1.48      | ~ v1_relat_1(X1_44)
% 7.66/1.48      | X1_44 = X0_44
% 7.66/1.48      | k1_relat_1(X1_44) != k1_relat_1(X0_44) ),
% 7.66/1.48      inference(subtyping,[status(esa)],[c_17]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_934,plain,
% 7.66/1.48      ( X0_44 = X1_44
% 7.66/1.48      | k1_relat_1(X0_44) != k1_relat_1(X1_44)
% 7.66/1.48      | r2_hidden(sK0(X1_44,X0_44),k1_relat_1(X1_44)) = iProver_top
% 7.66/1.48      | v1_funct_1(X0_44) != iProver_top
% 7.66/1.48      | v1_funct_1(X1_44) != iProver_top
% 7.66/1.48      | v1_relat_1(X0_44) != iProver_top
% 7.66/1.48      | v1_relat_1(X1_44) != iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_3903,plain,
% 7.66/1.48      ( k4_relat_1(sK1) = X0_44
% 7.66/1.48      | k1_relat_1(X0_44) != k2_relat_1(sK1)
% 7.66/1.48      | r2_hidden(sK0(X0_44,k4_relat_1(sK1)),k1_relat_1(X0_44)) = iProver_top
% 7.66/1.48      | v1_funct_1(X0_44) != iProver_top
% 7.66/1.48      | v1_funct_1(k4_relat_1(sK1)) != iProver_top
% 7.66/1.48      | v1_relat_1(X0_44) != iProver_top
% 7.66/1.48      | v1_relat_1(k4_relat_1(sK1)) != iProver_top ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_1589,c_934]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_28,plain,
% 7.66/1.48      ( v1_relat_1(sK1) = iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_26,negated_conjecture,
% 7.66/1.48      ( v1_funct_1(sK1) ),
% 7.66/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_29,plain,
% 7.66/1.48      ( v1_funct_1(sK1) = iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_23,negated_conjecture,
% 7.66/1.48      ( v2_funct_1(sK1) ),
% 7.66/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_32,plain,
% 7.66/1.48      ( v2_funct_1(sK1) = iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_12,plain,
% 7.66/1.48      ( ~ v1_funct_1(X0)
% 7.66/1.48      | ~ v2_funct_1(X0)
% 7.66/1.48      | ~ v1_relat_1(X0)
% 7.66/1.48      | v1_relat_1(k4_relat_1(X0)) ),
% 7.66/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_54,plain,
% 7.66/1.48      ( v1_funct_1(X0) != iProver_top
% 7.66/1.48      | v2_funct_1(X0) != iProver_top
% 7.66/1.48      | v1_relat_1(X0) != iProver_top
% 7.66/1.48      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_56,plain,
% 7.66/1.48      ( v1_funct_1(sK1) != iProver_top
% 7.66/1.48      | v2_funct_1(sK1) != iProver_top
% 7.66/1.48      | v1_relat_1(k4_relat_1(sK1)) = iProver_top
% 7.66/1.48      | v1_relat_1(sK1) != iProver_top ),
% 7.66/1.48      inference(instantiation,[status(thm)],[c_54]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_11,plain,
% 7.66/1.48      ( ~ v1_funct_1(X0)
% 7.66/1.48      | v1_funct_1(k4_relat_1(X0))
% 7.66/1.48      | ~ v2_funct_1(X0)
% 7.66/1.48      | ~ v1_relat_1(X0) ),
% 7.66/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_57,plain,
% 7.66/1.48      ( v1_funct_1(X0) != iProver_top
% 7.66/1.48      | v1_funct_1(k4_relat_1(X0)) = iProver_top
% 7.66/1.48      | v2_funct_1(X0) != iProver_top
% 7.66/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.66/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_59,plain,
% 7.66/1.48      ( v1_funct_1(k4_relat_1(sK1)) = iProver_top
% 7.66/1.48      | v1_funct_1(sK1) != iProver_top
% 7.66/1.48      | v2_funct_1(sK1) != iProver_top
% 7.66/1.48      | v1_relat_1(sK1) != iProver_top ),
% 7.66/1.48      inference(instantiation,[status(thm)],[c_57]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_23970,plain,
% 7.66/1.48      ( v1_relat_1(X0_44) != iProver_top
% 7.66/1.48      | k4_relat_1(sK1) = X0_44
% 7.66/1.48      | k1_relat_1(X0_44) != k2_relat_1(sK1)
% 7.66/1.48      | r2_hidden(sK0(X0_44,k4_relat_1(sK1)),k1_relat_1(X0_44)) = iProver_top
% 7.66/1.48      | v1_funct_1(X0_44) != iProver_top ),
% 7.66/1.48      inference(global_propositional_subsumption,
% 7.66/1.48                [status(thm)],
% 7.66/1.48                [c_3903,c_28,c_29,c_32,c_56,c_59]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_23971,plain,
% 7.66/1.48      ( k4_relat_1(sK1) = X0_44
% 7.66/1.48      | k1_relat_1(X0_44) != k2_relat_1(sK1)
% 7.66/1.48      | r2_hidden(sK0(X0_44,k4_relat_1(sK1)),k1_relat_1(X0_44)) = iProver_top
% 7.66/1.48      | v1_funct_1(X0_44) != iProver_top
% 7.66/1.48      | v1_relat_1(X0_44) != iProver_top ),
% 7.66/1.48      inference(renaming,[status(thm)],[c_23970]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_23981,plain,
% 7.66/1.48      ( k4_relat_1(sK1) = sK2
% 7.66/1.48      | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k1_relat_1(sK2)) = iProver_top
% 7.66/1.48      | v1_funct_1(sK2) != iProver_top
% 7.66/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.66/1.48      inference(superposition,[status(thm)],[c_499,c_23971]) ).
% 7.66/1.48  
% 7.66/1.48  cnf(c_24023,plain,
% 7.66/1.48      ( k4_relat_1(sK1) = sK2
% 7.66/1.48      | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k2_relat_1(sK1)) = iProver_top
% 7.66/1.49      | v1_funct_1(sK2) != iProver_top
% 7.66/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.66/1.49      inference(light_normalisation,[status(thm)],[c_23981,c_499]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_8,plain,
% 7.66/1.49      ( ~ v1_funct_1(X0)
% 7.66/1.49      | ~ v2_funct_1(X0)
% 7.66/1.49      | ~ v1_relat_1(X0)
% 7.66/1.49      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 7.66/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_290,plain,
% 7.66/1.49      ( ~ v1_funct_1(X0)
% 7.66/1.49      | ~ v1_relat_1(X0)
% 7.66/1.49      | k2_funct_1(X0) = k4_relat_1(X0)
% 7.66/1.49      | sK1 != X0 ),
% 7.66/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_23]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_291,plain,
% 7.66/1.49      ( ~ v1_funct_1(sK1)
% 7.66/1.49      | ~ v1_relat_1(sK1)
% 7.66/1.49      | k2_funct_1(sK1) = k4_relat_1(sK1) ),
% 7.66/1.49      inference(unflattening,[status(thm)],[c_290]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_67,plain,
% 7.66/1.49      ( ~ v1_funct_1(sK1)
% 7.66/1.49      | ~ v2_funct_1(sK1)
% 7.66/1.49      | ~ v1_relat_1(sK1)
% 7.66/1.49      | k2_funct_1(sK1) = k4_relat_1(sK1) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_293,plain,
% 7.66/1.49      ( k2_funct_1(sK1) = k4_relat_1(sK1) ),
% 7.66/1.49      inference(global_propositional_subsumption,
% 7.66/1.49                [status(thm)],
% 7.66/1.49                [c_291,c_27,c_26,c_23,c_67]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_492,plain,
% 7.66/1.49      ( k2_funct_1(sK1) = k4_relat_1(sK1) ),
% 7.66/1.49      inference(subtyping,[status(esa)],[c_293]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_18,negated_conjecture,
% 7.66/1.49      ( k2_funct_1(sK1) != sK2 ),
% 7.66/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_502,negated_conjecture,
% 7.66/1.49      ( k2_funct_1(sK1) != sK2 ),
% 7.66/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_965,plain,
% 7.66/1.49      ( k4_relat_1(sK1) != sK2 ),
% 7.66/1.49      inference(demodulation,[status(thm)],[c_492,c_502]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_3906,plain,
% 7.66/1.49      ( sK2 = X0_44
% 7.66/1.49      | k1_relat_1(X0_44) != k2_relat_1(sK1)
% 7.66/1.49      | r2_hidden(sK0(sK2,X0_44),k1_relat_1(sK2)) = iProver_top
% 7.66/1.49      | v1_funct_1(X0_44) != iProver_top
% 7.66/1.49      | v1_funct_1(sK2) != iProver_top
% 7.66/1.49      | v1_relat_1(X0_44) != iProver_top
% 7.66/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.66/1.49      inference(superposition,[status(thm)],[c_499,c_934]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_3979,plain,
% 7.66/1.49      ( sK2 = X0_44
% 7.66/1.49      | k1_relat_1(X0_44) != k2_relat_1(sK1)
% 7.66/1.49      | r2_hidden(sK0(sK2,X0_44),k2_relat_1(sK1)) = iProver_top
% 7.66/1.49      | v1_funct_1(X0_44) != iProver_top
% 7.66/1.49      | v1_funct_1(sK2) != iProver_top
% 7.66/1.49      | v1_relat_1(X0_44) != iProver_top
% 7.66/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.66/1.49      inference(light_normalisation,[status(thm)],[c_3906,c_499]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_25,negated_conjecture,
% 7.66/1.49      ( v1_relat_1(sK2) ),
% 7.66/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_30,plain,
% 7.66/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 7.66/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_24,negated_conjecture,
% 7.66/1.49      ( v1_funct_1(sK2) ),
% 7.66/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_31,plain,
% 7.66/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 7.66/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_5333,plain,
% 7.66/1.49      ( v1_relat_1(X0_44) != iProver_top
% 7.66/1.49      | sK2 = X0_44
% 7.66/1.49      | k1_relat_1(X0_44) != k2_relat_1(sK1)
% 7.66/1.49      | r2_hidden(sK0(sK2,X0_44),k2_relat_1(sK1)) = iProver_top
% 7.66/1.49      | v1_funct_1(X0_44) != iProver_top ),
% 7.66/1.49      inference(global_propositional_subsumption,
% 7.66/1.49                [status(thm)],
% 7.66/1.49                [c_3979,c_30,c_31]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_5334,plain,
% 7.66/1.49      ( sK2 = X0_44
% 7.66/1.49      | k1_relat_1(X0_44) != k2_relat_1(sK1)
% 7.66/1.49      | r2_hidden(sK0(sK2,X0_44),k2_relat_1(sK1)) = iProver_top
% 7.66/1.49      | v1_funct_1(X0_44) != iProver_top
% 7.66/1.49      | v1_relat_1(X0_44) != iProver_top ),
% 7.66/1.49      inference(renaming,[status(thm)],[c_5333]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_5346,plain,
% 7.66/1.49      ( k4_relat_1(sK1) = sK2
% 7.66/1.49      | r2_hidden(sK0(sK2,k4_relat_1(sK1)),k2_relat_1(sK1)) = iProver_top
% 7.66/1.49      | v1_funct_1(k4_relat_1(sK1)) != iProver_top
% 7.66/1.49      | v1_relat_1(k4_relat_1(sK1)) != iProver_top ),
% 7.66/1.49      inference(superposition,[status(thm)],[c_1589,c_5334]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_24035,plain,
% 7.66/1.49      ( r2_hidden(sK0(sK2,k4_relat_1(sK1)),k2_relat_1(sK1)) = iProver_top ),
% 7.66/1.49      inference(global_propositional_subsumption,
% 7.66/1.49                [status(thm)],
% 7.66/1.49                [c_24023,c_28,c_29,c_32,c_56,c_59,c_965,c_5346]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_13,plain,
% 7.66/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.66/1.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.66/1.49      | ~ v1_funct_1(X1)
% 7.66/1.49      | ~ v1_relat_1(X1) ),
% 7.66/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_505,plain,
% 7.66/1.49      ( ~ r2_hidden(X0_42,k1_relat_1(X0_44))
% 7.66/1.49      | r2_hidden(k1_funct_1(X0_44,X0_42),k2_relat_1(X0_44))
% 7.66/1.49      | ~ v1_funct_1(X0_44)
% 7.66/1.49      | ~ v1_relat_1(X0_44) ),
% 7.66/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_932,plain,
% 7.66/1.49      ( r2_hidden(X0_42,k1_relat_1(X0_44)) != iProver_top
% 7.66/1.49      | r2_hidden(k1_funct_1(X0_44,X0_42),k2_relat_1(X0_44)) = iProver_top
% 7.66/1.49      | v1_funct_1(X0_44) != iProver_top
% 7.66/1.49      | v1_relat_1(X0_44) != iProver_top ),
% 7.66/1.49      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_15,plain,
% 7.66/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.66/1.49      | ~ v1_funct_1(X1)
% 7.66/1.49      | ~ v2_funct_1(X1)
% 7.66/1.49      | ~ v1_relat_1(X1)
% 7.66/1.49      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
% 7.66/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_298,plain,
% 7.66/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.66/1.49      | ~ v1_funct_1(X1)
% 7.66/1.49      | ~ v1_relat_1(X1)
% 7.66/1.49      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
% 7.66/1.49      | sK1 != X1 ),
% 7.66/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_299,plain,
% 7.66/1.49      ( ~ r2_hidden(X0,k1_relat_1(sK1))
% 7.66/1.49      | ~ v1_funct_1(sK1)
% 7.66/1.49      | ~ v1_relat_1(sK1)
% 7.66/1.49      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ),
% 7.66/1.49      inference(unflattening,[status(thm)],[c_298]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_303,plain,
% 7.66/1.49      ( ~ r2_hidden(X0,k1_relat_1(sK1))
% 7.66/1.49      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ),
% 7.66/1.49      inference(global_propositional_subsumption,
% 7.66/1.49                [status(thm)],
% 7.66/1.49                [c_299,c_27,c_26]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_491,plain,
% 7.66/1.49      ( ~ r2_hidden(X0_42,k1_relat_1(sK1))
% 7.66/1.49      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0_42)) = X0_42 ),
% 7.66/1.49      inference(subtyping,[status(esa)],[c_303]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_942,plain,
% 7.66/1.49      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0_42)) = X0_42
% 7.66/1.49      | r2_hidden(X0_42,k1_relat_1(sK1)) != iProver_top ),
% 7.66/1.49      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_22,negated_conjecture,
% 7.66/1.49      ( k2_relat_1(sK2) = k1_relat_1(sK1) ),
% 7.66/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_498,negated_conjecture,
% 7.66/1.49      ( k2_relat_1(sK2) = k1_relat_1(sK1) ),
% 7.66/1.49      inference(subtyping,[status(esa)],[c_22]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_995,plain,
% 7.66/1.49      ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0_42)) = X0_42
% 7.66/1.49      | r2_hidden(X0_42,k2_relat_1(sK2)) != iProver_top ),
% 7.66/1.49      inference(light_normalisation,[status(thm)],[c_942,c_492,c_498]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2438,plain,
% 7.66/1.49      ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,k1_funct_1(sK2,X0_42))) = k1_funct_1(sK2,X0_42)
% 7.66/1.49      | r2_hidden(X0_42,k1_relat_1(sK2)) != iProver_top
% 7.66/1.49      | v1_funct_1(sK2) != iProver_top
% 7.66/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.66/1.49      inference(superposition,[status(thm)],[c_932,c_995]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2465,plain,
% 7.66/1.49      ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,k1_funct_1(sK2,X0_42))) = k1_funct_1(sK2,X0_42)
% 7.66/1.49      | r2_hidden(X0_42,k2_relat_1(sK1)) != iProver_top
% 7.66/1.49      | v1_funct_1(sK2) != iProver_top
% 7.66/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.66/1.49      inference(light_normalisation,[status(thm)],[c_2438,c_499]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2721,plain,
% 7.66/1.49      ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,k1_funct_1(sK2,X0_42))) = k1_funct_1(sK2,X0_42)
% 7.66/1.49      | r2_hidden(X0_42,k2_relat_1(sK1)) != iProver_top ),
% 7.66/1.49      inference(global_propositional_subsumption,
% 7.66/1.49                [status(thm)],
% 7.66/1.49                [c_2465,c_30,c_31]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_24146,plain,
% 7.66/1.49      ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1))))) = k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1))) ),
% 7.66/1.49      inference(superposition,[status(thm)],[c_24035,c_2721]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_19,negated_conjecture,
% 7.66/1.49      ( ~ r2_hidden(X0,k1_relat_1(sK2))
% 7.66/1.49      | ~ r2_hidden(k1_funct_1(sK2,X0),k1_relat_1(sK1))
% 7.66/1.49      | k1_funct_1(sK1,k1_funct_1(sK2,X0)) = X0 ),
% 7.66/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_501,negated_conjecture,
% 7.66/1.49      ( ~ r2_hidden(X0_42,k1_relat_1(sK2))
% 7.66/1.49      | ~ r2_hidden(k1_funct_1(sK2,X0_42),k1_relat_1(sK1))
% 7.66/1.49      | k1_funct_1(sK1,k1_funct_1(sK2,X0_42)) = X0_42 ),
% 7.66/1.49      inference(subtyping,[status(esa)],[c_19]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_935,plain,
% 7.66/1.49      ( k1_funct_1(sK1,k1_funct_1(sK2,X0_42)) = X0_42
% 7.66/1.49      | r2_hidden(X0_42,k1_relat_1(sK2)) != iProver_top
% 7.66/1.49      | r2_hidden(k1_funct_1(sK2,X0_42),k1_relat_1(sK1)) != iProver_top ),
% 7.66/1.49      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1011,plain,
% 7.66/1.49      ( k1_funct_1(sK1,k1_funct_1(sK2,X0_42)) = X0_42
% 7.66/1.49      | r2_hidden(X0_42,k2_relat_1(sK1)) != iProver_top
% 7.66/1.49      | r2_hidden(k1_funct_1(sK2,X0_42),k2_relat_1(sK2)) != iProver_top ),
% 7.66/1.49      inference(light_normalisation,[status(thm)],[c_935,c_498,c_499]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2439,plain,
% 7.66/1.49      ( k1_funct_1(sK1,k1_funct_1(sK2,X0_42)) = X0_42
% 7.66/1.49      | r2_hidden(X0_42,k1_relat_1(sK2)) != iProver_top
% 7.66/1.49      | r2_hidden(X0_42,k2_relat_1(sK1)) != iProver_top
% 7.66/1.49      | v1_funct_1(sK2) != iProver_top
% 7.66/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.66/1.49      inference(superposition,[status(thm)],[c_932,c_1011]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2456,plain,
% 7.66/1.49      ( k1_funct_1(sK1,k1_funct_1(sK2,X0_42)) = X0_42
% 7.66/1.49      | r2_hidden(X0_42,k2_relat_1(sK1)) != iProver_top
% 7.66/1.49      | v1_funct_1(sK2) != iProver_top
% 7.66/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.66/1.49      inference(light_normalisation,[status(thm)],[c_2439,c_499]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2611,plain,
% 7.66/1.49      ( k1_funct_1(sK1,k1_funct_1(sK2,X0_42)) = X0_42
% 7.66/1.49      | r2_hidden(X0_42,k2_relat_1(sK1)) != iProver_top ),
% 7.66/1.49      inference(global_propositional_subsumption,
% 7.66/1.49                [status(thm)],
% 7.66/1.49                [c_2456,c_30,c_31]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_24148,plain,
% 7.66/1.49      ( k1_funct_1(sK1,k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1)))) = sK0(sK2,k4_relat_1(sK1)) ),
% 7.66/1.49      inference(superposition,[status(thm)],[c_24035,c_2611]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_24152,plain,
% 7.66/1.49      ( k1_funct_1(k4_relat_1(sK1),sK0(sK2,k4_relat_1(sK1))) = k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1))) ),
% 7.66/1.49      inference(light_normalisation,[status(thm)],[c_24146,c_24148]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_16,plain,
% 7.66/1.49      ( ~ v1_funct_1(X0)
% 7.66/1.49      | ~ v1_funct_1(X1)
% 7.66/1.49      | ~ v1_relat_1(X0)
% 7.66/1.49      | ~ v1_relat_1(X1)
% 7.66/1.49      | X1 = X0
% 7.66/1.49      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
% 7.66/1.49      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 7.66/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_504,plain,
% 7.66/1.49      ( ~ v1_funct_1(X0_44)
% 7.66/1.49      | ~ v1_funct_1(X1_44)
% 7.66/1.49      | ~ v1_relat_1(X0_44)
% 7.66/1.49      | ~ v1_relat_1(X1_44)
% 7.66/1.49      | X1_44 = X0_44
% 7.66/1.49      | k1_relat_1(X1_44) != k1_relat_1(X0_44)
% 7.66/1.49      | k1_funct_1(X1_44,sK0(X0_44,X1_44)) != k1_funct_1(X0_44,sK0(X0_44,X1_44)) ),
% 7.66/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1239,plain,
% 7.66/1.49      ( ~ v1_funct_1(X0_44)
% 7.66/1.49      | ~ v1_funct_1(sK2)
% 7.66/1.49      | ~ v1_relat_1(X0_44)
% 7.66/1.49      | ~ v1_relat_1(sK2)
% 7.66/1.49      | X0_44 = sK2
% 7.66/1.49      | k1_relat_1(X0_44) != k1_relat_1(sK2)
% 7.66/1.49      | k1_funct_1(X0_44,sK0(sK2,X0_44)) != k1_funct_1(sK2,sK0(sK2,X0_44)) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_504]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_5409,plain,
% 7.66/1.49      ( ~ v1_funct_1(k4_relat_1(sK1))
% 7.66/1.49      | ~ v1_funct_1(sK2)
% 7.66/1.49      | ~ v1_relat_1(k4_relat_1(sK1))
% 7.66/1.49      | ~ v1_relat_1(sK2)
% 7.66/1.49      | k4_relat_1(sK1) = sK2
% 7.66/1.49      | k1_relat_1(k4_relat_1(sK1)) != k1_relat_1(sK2)
% 7.66/1.49      | k1_funct_1(k4_relat_1(sK1),sK0(sK2,k4_relat_1(sK1))) != k1_funct_1(sK2,sK0(sK2,k4_relat_1(sK1))) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_1239]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_521,plain,
% 7.66/1.49      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 7.66/1.49      theory(equality) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2113,plain,
% 7.66/1.49      ( X0_43 != X1_43
% 7.66/1.49      | k1_relat_1(X0_44) != X1_43
% 7.66/1.49      | k1_relat_1(X0_44) = X0_43 ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_521]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2703,plain,
% 7.66/1.49      ( X0_43 != k2_relat_1(X0_44)
% 7.66/1.49      | k1_relat_1(k4_relat_1(X0_44)) = X0_43
% 7.66/1.49      | k1_relat_1(k4_relat_1(X0_44)) != k2_relat_1(X0_44) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_2113]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_4988,plain,
% 7.66/1.49      ( k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(sK2)
% 7.66/1.49      | k1_relat_1(k4_relat_1(sK1)) != k2_relat_1(sK1)
% 7.66/1.49      | k1_relat_1(sK2) != k2_relat_1(sK1) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_2703]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1308,plain,
% 7.66/1.49      ( X0_43 != X1_43
% 7.66/1.49      | k1_relat_1(sK2) != X1_43
% 7.66/1.49      | k1_relat_1(sK2) = X0_43 ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_521]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1498,plain,
% 7.66/1.49      ( X0_43 != k1_relat_1(sK2)
% 7.66/1.49      | k1_relat_1(sK2) = X0_43
% 7.66/1.49      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_1308]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2242,plain,
% 7.66/1.49      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 7.66/1.49      | k1_relat_1(sK2) = k2_relat_1(sK1)
% 7.66/1.49      | k2_relat_1(sK1) != k1_relat_1(sK2) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_1498]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_526,plain,
% 7.66/1.49      ( X0_44 != X1_44 | k1_relat_1(X0_44) = k1_relat_1(X1_44) ),
% 7.66/1.49      theory(equality) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1219,plain,
% 7.66/1.49      ( sK2 != X0_44 | k1_relat_1(sK2) = k1_relat_1(X0_44) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_526]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1270,plain,
% 7.66/1.49      ( sK2 != sK2 | k1_relat_1(sK2) = k1_relat_1(sK2) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_1219]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_519,plain,( X0_44 = X0_44 ),theory(equality) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1190,plain,
% 7.66/1.49      ( sK2 = sK2 ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_519]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_555,plain,
% 7.66/1.49      ( ~ v1_relat_1(sK1)
% 7.66/1.49      | k1_relat_1(k4_relat_1(sK1)) = k2_relat_1(sK1) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_512]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_58,plain,
% 7.66/1.49      ( v1_funct_1(k4_relat_1(sK1))
% 7.66/1.49      | ~ v1_funct_1(sK1)
% 7.66/1.49      | ~ v2_funct_1(sK1)
% 7.66/1.49      | ~ v1_relat_1(sK1) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_55,plain,
% 7.66/1.49      ( ~ v1_funct_1(sK1)
% 7.66/1.49      | ~ v2_funct_1(sK1)
% 7.66/1.49      | v1_relat_1(k4_relat_1(sK1))
% 7.66/1.49      | ~ v1_relat_1(sK1) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(contradiction,plain,
% 7.66/1.49      ( $false ),
% 7.66/1.49      inference(minisat,
% 7.66/1.49                [status(thm)],
% 7.66/1.49                [c_24152,c_5409,c_4988,c_2242,c_1270,c_1190,c_965,c_499,
% 7.66/1.49                 c_555,c_58,c_55,c_23,c_24,c_25,c_26,c_27]) ).
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.66/1.49  
% 7.66/1.49  ------                               Statistics
% 7.66/1.49  
% 7.66/1.49  ------ General
% 7.66/1.49  
% 7.66/1.49  abstr_ref_over_cycles:                  0
% 7.66/1.49  abstr_ref_under_cycles:                 0
% 7.66/1.49  gc_basic_clause_elim:                   0
% 7.66/1.49  forced_gc_time:                         0
% 7.66/1.49  parsing_time:                           0.012
% 7.66/1.49  unif_index_cands_time:                  0.
% 7.66/1.49  unif_index_add_time:                    0.
% 7.66/1.49  orderings_time:                         0.
% 7.66/1.49  out_proof_time:                         0.01
% 7.66/1.49  total_time:                             0.947
% 7.66/1.49  num_of_symbols:                         48
% 7.66/1.49  num_of_terms:                           14742
% 7.66/1.49  
% 7.66/1.49  ------ Preprocessing
% 7.66/1.49  
% 7.66/1.49  num_of_splits:                          0
% 7.66/1.49  num_of_split_atoms:                     0
% 7.66/1.49  num_of_reused_defs:                     0
% 7.66/1.49  num_eq_ax_congr_red:                    6
% 7.66/1.49  num_of_sem_filtered_clauses:            1
% 7.66/1.49  num_of_subtypes:                        3
% 7.66/1.49  monotx_restored_types:                  0
% 7.66/1.49  sat_num_of_epr_types:                   0
% 7.66/1.49  sat_num_of_non_cyclic_types:            0
% 7.66/1.49  sat_guarded_non_collapsed_types:        2
% 7.66/1.49  num_pure_diseq_elim:                    0
% 7.66/1.49  simp_replaced_by:                       0
% 7.66/1.49  res_preprocessed:                       138
% 7.66/1.49  prep_upred:                             0
% 7.66/1.49  prep_unflattend:                        4
% 7.66/1.49  smt_new_axioms:                         0
% 7.66/1.49  pred_elim_cands:                        3
% 7.66/1.49  pred_elim:                              1
% 7.66/1.49  pred_elim_cl:                           1
% 7.66/1.49  pred_elim_cycles:                       3
% 7.66/1.49  merged_defs:                            0
% 7.66/1.49  merged_defs_ncl:                        0
% 7.66/1.49  bin_hyper_res:                          0
% 7.66/1.49  prep_cycles:                            4
% 7.66/1.49  pred_elim_time:                         0.002
% 7.66/1.49  splitting_time:                         0.
% 7.66/1.49  sem_filter_time:                        0.
% 7.66/1.49  monotx_time:                            0.
% 7.66/1.49  subtype_inf_time:                       0.
% 7.66/1.49  
% 7.66/1.49  ------ Problem properties
% 7.66/1.49  
% 7.66/1.49  clauses:                                26
% 7.66/1.49  conjectures:                            9
% 7.66/1.49  epr:                                    4
% 7.66/1.49  horn:                                   25
% 7.66/1.49  ground:                                 9
% 7.66/1.49  unary:                                  12
% 7.66/1.49  binary:                                 8
% 7.66/1.49  lits:                                   55
% 7.66/1.49  lits_eq:                                20
% 7.66/1.49  fd_pure:                                0
% 7.66/1.49  fd_pseudo:                              0
% 7.66/1.49  fd_cond:                                0
% 7.66/1.49  fd_pseudo_cond:                         2
% 7.66/1.49  ac_symbols:                             0
% 7.66/1.49  
% 7.66/1.49  ------ Propositional Solver
% 7.66/1.49  
% 7.66/1.49  prop_solver_calls:                      33
% 7.66/1.49  prop_fast_solver_calls:                 2138
% 7.66/1.49  smt_solver_calls:                       0
% 7.66/1.49  smt_fast_solver_calls:                  0
% 7.66/1.49  prop_num_of_clauses:                    8007
% 7.66/1.49  prop_preprocess_simplified:             16625
% 7.66/1.49  prop_fo_subsumed:                       464
% 7.66/1.49  prop_solver_time:                       0.
% 7.66/1.49  smt_solver_time:                        0.
% 7.66/1.49  smt_fast_solver_time:                   0.
% 7.66/1.49  prop_fast_solver_time:                  0.
% 7.66/1.49  prop_unsat_core_time:                   0.001
% 7.66/1.49  
% 7.66/1.49  ------ QBF
% 7.66/1.49  
% 7.66/1.49  qbf_q_res:                              0
% 7.66/1.49  qbf_num_tautologies:                    0
% 7.66/1.49  qbf_prep_cycles:                        0
% 7.66/1.49  
% 7.66/1.49  ------ BMC1
% 7.66/1.49  
% 7.66/1.49  bmc1_current_bound:                     -1
% 7.66/1.49  bmc1_last_solved_bound:                 -1
% 7.66/1.49  bmc1_unsat_core_size:                   -1
% 7.66/1.49  bmc1_unsat_core_parents_size:           -1
% 7.66/1.49  bmc1_merge_next_fun:                    0
% 7.66/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.66/1.49  
% 7.66/1.49  ------ Instantiation
% 7.66/1.49  
% 7.66/1.49  inst_num_of_clauses:                    3465
% 7.66/1.49  inst_num_in_passive:                    1536
% 7.66/1.49  inst_num_in_active:                     1333
% 7.66/1.49  inst_num_in_unprocessed:                596
% 7.66/1.49  inst_num_of_loops:                      1410
% 7.66/1.49  inst_num_of_learning_restarts:          0
% 7.66/1.49  inst_num_moves_active_passive:          71
% 7.66/1.49  inst_lit_activity:                      0
% 7.66/1.49  inst_lit_activity_moves:                0
% 7.66/1.49  inst_num_tautologies:                   0
% 7.66/1.49  inst_num_prop_implied:                  0
% 7.66/1.49  inst_num_existing_simplified:           0
% 7.66/1.49  inst_num_eq_res_simplified:             0
% 7.66/1.49  inst_num_child_elim:                    0
% 7.66/1.49  inst_num_of_dismatching_blockings:      2623
% 7.66/1.49  inst_num_of_non_proper_insts:           4786
% 7.66/1.49  inst_num_of_duplicates:                 0
% 7.66/1.49  inst_inst_num_from_inst_to_res:         0
% 7.66/1.49  inst_dismatching_checking_time:         0.
% 7.66/1.49  
% 7.66/1.49  ------ Resolution
% 7.66/1.49  
% 7.66/1.49  res_num_of_clauses:                     0
% 7.66/1.49  res_num_in_passive:                     0
% 7.66/1.49  res_num_in_active:                      0
% 7.66/1.49  res_num_of_loops:                       142
% 7.66/1.49  res_forward_subset_subsumed:            884
% 7.66/1.49  res_backward_subset_subsumed:           2
% 7.66/1.49  res_forward_subsumed:                   0
% 7.66/1.49  res_backward_subsumed:                  0
% 7.66/1.49  res_forward_subsumption_resolution:     0
% 7.66/1.49  res_backward_subsumption_resolution:    0
% 7.66/1.49  res_clause_to_clause_subsumption:       9522
% 7.66/1.49  res_orphan_elimination:                 0
% 7.66/1.49  res_tautology_del:                      529
% 7.66/1.49  res_num_eq_res_simplified:              0
% 7.66/1.49  res_num_sel_changes:                    0
% 7.66/1.49  res_moves_from_active_to_pass:          0
% 7.66/1.49  
% 7.66/1.49  ------ Superposition
% 7.66/1.49  
% 7.66/1.49  sup_time_total:                         0.
% 7.66/1.49  sup_time_generating:                    0.
% 7.66/1.49  sup_time_sim_full:                      0.
% 7.66/1.49  sup_time_sim_immed:                     0.
% 7.66/1.49  
% 7.66/1.49  sup_num_of_clauses:                     548
% 7.66/1.49  sup_num_in_active:                      280
% 7.66/1.49  sup_num_in_passive:                     268
% 7.66/1.49  sup_num_of_loops:                       281
% 7.66/1.49  sup_fw_superposition:                   351
% 7.66/1.49  sup_bw_superposition:                   307
% 7.66/1.49  sup_immediate_simplified:               389
% 7.66/1.49  sup_given_eliminated:                   0
% 7.66/1.49  comparisons_done:                       0
% 7.66/1.49  comparisons_avoided:                    0
% 7.66/1.49  
% 7.66/1.49  ------ Simplifications
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  sim_fw_subset_subsumed:                 5
% 7.66/1.49  sim_bw_subset_subsumed:                 2
% 7.66/1.49  sim_fw_subsumed:                        0
% 7.66/1.49  sim_bw_subsumed:                        0
% 7.66/1.49  sim_fw_subsumption_res:                 0
% 7.66/1.49  sim_bw_subsumption_res:                 0
% 7.66/1.49  sim_tautology_del:                      2
% 7.66/1.49  sim_eq_tautology_del:                   126
% 7.66/1.49  sim_eq_res_simp:                        0
% 7.66/1.49  sim_fw_demodulated:                     0
% 7.66/1.49  sim_bw_demodulated:                     1
% 7.66/1.49  sim_light_normalised:                   388
% 7.66/1.49  sim_joinable_taut:                      0
% 7.66/1.49  sim_joinable_simp:                      0
% 7.66/1.49  sim_ac_normalised:                      0
% 7.66/1.49  sim_smt_subsumption:                    0
% 7.66/1.49  
%------------------------------------------------------------------------------
