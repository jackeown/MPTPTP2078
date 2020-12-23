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
% DateTime   : Thu Dec  3 11:50:22 EST 2020

% Result     : Theorem 51.63s
% Output     : CNFRefutation 51.63s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 724 expanded)
%              Number of clauses        :   65 ( 181 expanded)
%              Number of leaves         :   14 ( 162 expanded)
%              Depth                    :   19
%              Number of atoms          :  444 (3868 expanded)
%              Number of equality atoms :  192 (1352 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f62,plain,
    ( ? [X0,X1] :
        ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
          | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
        & r2_hidden(X0,k2_relat_1(X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( k1_funct_1(k5_relat_1(k2_funct_1(sK6),sK6),sK5) != sK5
        | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK5)) != sK5 )
      & r2_hidden(sK5,k2_relat_1(sK6))
      & v2_funct_1(sK6)
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ( k1_funct_1(k5_relat_1(k2_funct_1(sK6),sK6),sK5) != sK5
      | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK5)) != sK5 )
    & r2_hidden(sK5,k2_relat_1(sK6))
    & v2_funct_1(sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f44,f62])).

fof(f100,plain,(
    r2_hidden(sK5,k2_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f63])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f103,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f97,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f73,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f98,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f84,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f99,plain,(
    v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f86,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f55,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f52,f55,f54,f53])).

fof(f79,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f106,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f78,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f107,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f101,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK6),sK6),sK5) != sK5
    | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK5)) != sK5 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_34,negated_conjecture,
    ( r2_hidden(sK5,k2_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1191,plain,
    ( r2_hidden(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1214,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_37,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1189,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1211,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2132,plain,
    ( k2_relat_1(k4_relat_1(sK6)) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1189,c_1211])).

cnf(c_11,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1208,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4517,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(sK6),X0)) = k1_relat_1(k4_relat_1(sK6))
    | r1_tarski(k1_relat_1(sK6),k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2132,c_1208])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1210,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1824,plain,
    ( k1_relat_1(k4_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1189,c_1210])).

cnf(c_4521,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(sK6),X0)) = k2_relat_1(sK6)
    | r1_tarski(k1_relat_1(sK6),k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4517,c_1824])).

cnf(c_38,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_118,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_120,plain,
    ( v1_relat_1(k4_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_5283,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(sK6),k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(k4_relat_1(sK6),X0)) = k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4521,c_38,c_120])).

cnf(c_5284,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(sK6),X0)) = k2_relat_1(sK6)
    | r1_tarski(k1_relat_1(sK6),k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5283])).

cnf(c_5289,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(sK6),sK6)) = k2_relat_1(sK6)
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_5284])).

cnf(c_6950,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(sK6),sK6)) = k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5289,c_38])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1195,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6957,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),X0) = k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),X0))
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_funct_1(k4_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(k4_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6950,c_1195])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_39,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_35,negated_conjecture,
    ( v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_404,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_35])).

cnf(c_405,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k2_funct_1(sK6) = k4_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_79,plain,
    ( ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k2_funct_1(sK6) = k4_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_407,plain,
    ( k2_funct_1(sK6) = k4_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_37,c_36,c_35,c_79])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1199,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2862,plain,
    ( v1_funct_1(k4_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_407,c_1199])).

cnf(c_143578,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),X0) = k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),X0))
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6957,c_38,c_39,c_120,c_2862])).

cnf(c_143590,plain,
    ( k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),sK5)) = k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5) ),
    inference(superposition,[status(thm)],[c_1191,c_143578])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1201,plain,
    ( k1_funct_1(X0,sK3(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3789,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK5)) = sK5
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_1201])).

cnf(c_3587,plain,
    ( ~ r2_hidden(sK5,k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK3(X0,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3589,plain,
    ( ~ r2_hidden(sK5,k2_relat_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK3(sK6,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_3587])).

cnf(c_4119,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3789,c_37,c_36,c_34,c_3589])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1200,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_412,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_35])).

cnf(c_413,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_417,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_37,c_36])).

cnf(c_1188,plain,
    ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_1220,plain,
    ( k1_funct_1(k4_relat_1(sK6),k1_funct_1(sK6,X0)) = X0
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1188,c_407])).

cnf(c_3881,plain,
    ( k1_funct_1(k4_relat_1(sK6),k1_funct_1(sK6,sK3(sK6,X0))) = sK3(sK6,X0)
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_1220])).

cnf(c_6581,plain,
    ( k1_funct_1(k4_relat_1(sK6),k1_funct_1(sK6,sK3(sK6,X0))) = sK3(sK6,X0)
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3881,c_38,c_39])).

cnf(c_6591,plain,
    ( k1_funct_1(k4_relat_1(sK6),k1_funct_1(sK6,sK3(sK6,sK5))) = sK3(sK6,sK5) ),
    inference(superposition,[status(thm)],[c_1191,c_6581])).

cnf(c_6594,plain,
    ( k1_funct_1(k4_relat_1(sK6),sK5) = sK3(sK6,sK5) ),
    inference(light_normalisation,[status(thm)],[c_6591,c_4119])).

cnf(c_143677,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_143590,c_4119,c_6594])).

cnf(c_33,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK6),sK6),sK5) != sK5
    | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK5)) != sK5 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1221,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5) != sK5
    | k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),sK5)) != sK5 ),
    inference(light_normalisation,[status(thm)],[c_33,c_407])).

cnf(c_6614,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5) != sK5
    | k1_funct_1(sK6,sK3(sK6,sK5)) != sK5 ),
    inference(demodulation,[status(thm)],[c_6594,c_1221])).

cnf(c_6615,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5) != sK5
    | sK5 != sK5 ),
    inference(light_normalisation,[status(thm)],[c_6614,c_4119])).

cnf(c_6616,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5) != sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_6615])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_143677,c_6616])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:33:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 51.63/6.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.63/6.98  
% 51.63/6.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.63/6.98  
% 51.63/6.98  ------  iProver source info
% 51.63/6.98  
% 51.63/6.98  git: date: 2020-06-30 10:37:57 +0100
% 51.63/6.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.63/6.98  git: non_committed_changes: false
% 51.63/6.98  git: last_make_outside_of_git: false
% 51.63/6.98  
% 51.63/6.98  ------ 
% 51.63/6.98  
% 51.63/6.98  ------ Input Options
% 51.63/6.98  
% 51.63/6.98  --out_options                           all
% 51.63/6.98  --tptp_safe_out                         true
% 51.63/6.98  --problem_path                          ""
% 51.63/6.98  --include_path                          ""
% 51.63/6.98  --clausifier                            res/vclausify_rel
% 51.63/6.98  --clausifier_options                    ""
% 51.63/6.98  --stdin                                 false
% 51.63/6.98  --stats_out                             all
% 51.63/6.98  
% 51.63/6.98  ------ General Options
% 51.63/6.98  
% 51.63/6.98  --fof                                   false
% 51.63/6.98  --time_out_real                         305.
% 51.63/6.98  --time_out_virtual                      -1.
% 51.63/6.98  --symbol_type_check                     false
% 51.63/6.98  --clausify_out                          false
% 51.63/6.98  --sig_cnt_out                           false
% 51.63/6.98  --trig_cnt_out                          false
% 51.63/6.98  --trig_cnt_out_tolerance                1.
% 51.63/6.98  --trig_cnt_out_sk_spl                   false
% 51.63/6.98  --abstr_cl_out                          false
% 51.63/6.98  
% 51.63/6.98  ------ Global Options
% 51.63/6.98  
% 51.63/6.98  --schedule                              default
% 51.63/6.98  --add_important_lit                     false
% 51.63/6.98  --prop_solver_per_cl                    1000
% 51.63/6.98  --min_unsat_core                        false
% 51.63/6.98  --soft_assumptions                      false
% 51.63/6.98  --soft_lemma_size                       3
% 51.63/6.98  --prop_impl_unit_size                   0
% 51.63/6.98  --prop_impl_unit                        []
% 51.63/6.98  --share_sel_clauses                     true
% 51.63/6.98  --reset_solvers                         false
% 51.63/6.98  --bc_imp_inh                            [conj_cone]
% 51.63/6.98  --conj_cone_tolerance                   3.
% 51.63/6.98  --extra_neg_conj                        none
% 51.63/6.98  --large_theory_mode                     true
% 51.63/6.98  --prolific_symb_bound                   200
% 51.63/6.98  --lt_threshold                          2000
% 51.63/6.98  --clause_weak_htbl                      true
% 51.63/6.98  --gc_record_bc_elim                     false
% 51.63/6.98  
% 51.63/6.98  ------ Preprocessing Options
% 51.63/6.98  
% 51.63/6.98  --preprocessing_flag                    true
% 51.63/6.98  --time_out_prep_mult                    0.1
% 51.63/6.98  --splitting_mode                        input
% 51.63/6.98  --splitting_grd                         true
% 51.63/6.98  --splitting_cvd                         false
% 51.63/6.98  --splitting_cvd_svl                     false
% 51.63/6.98  --splitting_nvd                         32
% 51.63/6.98  --sub_typing                            true
% 51.63/6.98  --prep_gs_sim                           true
% 51.63/6.98  --prep_unflatten                        true
% 51.63/6.98  --prep_res_sim                          true
% 51.63/6.98  --prep_upred                            true
% 51.63/6.98  --prep_sem_filter                       exhaustive
% 51.63/6.98  --prep_sem_filter_out                   false
% 51.63/6.98  --pred_elim                             true
% 51.63/6.98  --res_sim_input                         true
% 51.63/6.98  --eq_ax_congr_red                       true
% 51.63/6.98  --pure_diseq_elim                       true
% 51.63/6.98  --brand_transform                       false
% 51.63/6.98  --non_eq_to_eq                          false
% 51.63/6.98  --prep_def_merge                        true
% 51.63/6.98  --prep_def_merge_prop_impl              false
% 51.63/6.98  --prep_def_merge_mbd                    true
% 51.63/6.98  --prep_def_merge_tr_red                 false
% 51.63/6.98  --prep_def_merge_tr_cl                  false
% 51.63/6.98  --smt_preprocessing                     true
% 51.63/6.98  --smt_ac_axioms                         fast
% 51.63/6.98  --preprocessed_out                      false
% 51.63/6.98  --preprocessed_stats                    false
% 51.63/6.98  
% 51.63/6.98  ------ Abstraction refinement Options
% 51.63/6.98  
% 51.63/6.98  --abstr_ref                             []
% 51.63/6.98  --abstr_ref_prep                        false
% 51.63/6.98  --abstr_ref_until_sat                   false
% 51.63/6.98  --abstr_ref_sig_restrict                funpre
% 51.63/6.98  --abstr_ref_af_restrict_to_split_sk     false
% 51.63/6.98  --abstr_ref_under                       []
% 51.63/6.98  
% 51.63/6.98  ------ SAT Options
% 51.63/6.98  
% 51.63/6.98  --sat_mode                              false
% 51.63/6.98  --sat_fm_restart_options                ""
% 51.63/6.98  --sat_gr_def                            false
% 51.63/6.98  --sat_epr_types                         true
% 51.63/6.98  --sat_non_cyclic_types                  false
% 51.63/6.98  --sat_finite_models                     false
% 51.63/6.98  --sat_fm_lemmas                         false
% 51.63/6.98  --sat_fm_prep                           false
% 51.63/6.98  --sat_fm_uc_incr                        true
% 51.63/6.98  --sat_out_model                         small
% 51.63/6.98  --sat_out_clauses                       false
% 51.63/6.98  
% 51.63/6.98  ------ QBF Options
% 51.63/6.98  
% 51.63/6.98  --qbf_mode                              false
% 51.63/6.98  --qbf_elim_univ                         false
% 51.63/6.98  --qbf_dom_inst                          none
% 51.63/6.98  --qbf_dom_pre_inst                      false
% 51.63/6.98  --qbf_sk_in                             false
% 51.63/6.98  --qbf_pred_elim                         true
% 51.63/6.98  --qbf_split                             512
% 51.63/6.98  
% 51.63/6.98  ------ BMC1 Options
% 51.63/6.98  
% 51.63/6.98  --bmc1_incremental                      false
% 51.63/6.98  --bmc1_axioms                           reachable_all
% 51.63/6.98  --bmc1_min_bound                        0
% 51.63/6.98  --bmc1_max_bound                        -1
% 51.63/6.98  --bmc1_max_bound_default                -1
% 51.63/6.98  --bmc1_symbol_reachability              true
% 51.63/6.98  --bmc1_property_lemmas                  false
% 51.63/6.98  --bmc1_k_induction                      false
% 51.63/6.98  --bmc1_non_equiv_states                 false
% 51.63/6.98  --bmc1_deadlock                         false
% 51.63/6.98  --bmc1_ucm                              false
% 51.63/6.98  --bmc1_add_unsat_core                   none
% 51.63/6.98  --bmc1_unsat_core_children              false
% 51.63/6.98  --bmc1_unsat_core_extrapolate_axioms    false
% 51.63/6.98  --bmc1_out_stat                         full
% 51.63/6.98  --bmc1_ground_init                      false
% 51.63/6.98  --bmc1_pre_inst_next_state              false
% 51.63/6.98  --bmc1_pre_inst_state                   false
% 51.63/6.98  --bmc1_pre_inst_reach_state             false
% 51.63/6.98  --bmc1_out_unsat_core                   false
% 51.63/6.98  --bmc1_aig_witness_out                  false
% 51.63/6.98  --bmc1_verbose                          false
% 51.63/6.98  --bmc1_dump_clauses_tptp                false
% 51.63/6.98  --bmc1_dump_unsat_core_tptp             false
% 51.63/6.98  --bmc1_dump_file                        -
% 51.63/6.98  --bmc1_ucm_expand_uc_limit              128
% 51.63/6.98  --bmc1_ucm_n_expand_iterations          6
% 51.63/6.98  --bmc1_ucm_extend_mode                  1
% 51.63/6.98  --bmc1_ucm_init_mode                    2
% 51.63/6.98  --bmc1_ucm_cone_mode                    none
% 51.63/6.98  --bmc1_ucm_reduced_relation_type        0
% 51.63/6.98  --bmc1_ucm_relax_model                  4
% 51.63/6.98  --bmc1_ucm_full_tr_after_sat            true
% 51.63/6.98  --bmc1_ucm_expand_neg_assumptions       false
% 51.63/6.98  --bmc1_ucm_layered_model                none
% 51.63/6.98  --bmc1_ucm_max_lemma_size               10
% 51.63/6.98  
% 51.63/6.98  ------ AIG Options
% 51.63/6.98  
% 51.63/6.98  --aig_mode                              false
% 51.63/6.98  
% 51.63/6.98  ------ Instantiation Options
% 51.63/6.98  
% 51.63/6.98  --instantiation_flag                    true
% 51.63/6.98  --inst_sos_flag                         true
% 51.63/6.98  --inst_sos_phase                        true
% 51.63/6.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.63/6.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.63/6.98  --inst_lit_sel_side                     num_symb
% 51.63/6.98  --inst_solver_per_active                1400
% 51.63/6.98  --inst_solver_calls_frac                1.
% 51.63/6.98  --inst_passive_queue_type               priority_queues
% 51.63/6.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.63/6.98  --inst_passive_queues_freq              [25;2]
% 51.63/6.98  --inst_dismatching                      true
% 51.63/6.98  --inst_eager_unprocessed_to_passive     true
% 51.63/6.98  --inst_prop_sim_given                   true
% 51.63/6.98  --inst_prop_sim_new                     false
% 51.63/6.98  --inst_subs_new                         false
% 51.63/6.98  --inst_eq_res_simp                      false
% 51.63/6.98  --inst_subs_given                       false
% 51.63/6.98  --inst_orphan_elimination               true
% 51.63/6.98  --inst_learning_loop_flag               true
% 51.63/6.98  --inst_learning_start                   3000
% 51.63/6.98  --inst_learning_factor                  2
% 51.63/6.98  --inst_start_prop_sim_after_learn       3
% 51.63/6.98  --inst_sel_renew                        solver
% 51.63/6.98  --inst_lit_activity_flag                true
% 51.63/6.98  --inst_restr_to_given                   false
% 51.63/6.98  --inst_activity_threshold               500
% 51.63/6.98  --inst_out_proof                        true
% 51.63/6.98  
% 51.63/6.98  ------ Resolution Options
% 51.63/6.98  
% 51.63/6.98  --resolution_flag                       true
% 51.63/6.98  --res_lit_sel                           adaptive
% 51.63/6.98  --res_lit_sel_side                      none
% 51.63/6.98  --res_ordering                          kbo
% 51.63/6.98  --res_to_prop_solver                    active
% 51.63/6.98  --res_prop_simpl_new                    false
% 51.63/6.98  --res_prop_simpl_given                  true
% 51.63/6.98  --res_passive_queue_type                priority_queues
% 51.63/6.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.63/6.98  --res_passive_queues_freq               [15;5]
% 51.63/6.98  --res_forward_subs                      full
% 51.63/6.98  --res_backward_subs                     full
% 51.63/6.98  --res_forward_subs_resolution           true
% 51.63/6.98  --res_backward_subs_resolution          true
% 51.63/6.98  --res_orphan_elimination                true
% 51.63/6.98  --res_time_limit                        2.
% 51.63/6.98  --res_out_proof                         true
% 51.63/6.98  
% 51.63/6.98  ------ Superposition Options
% 51.63/6.98  
% 51.63/6.98  --superposition_flag                    true
% 51.63/6.98  --sup_passive_queue_type                priority_queues
% 51.63/6.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.63/6.98  --sup_passive_queues_freq               [8;1;4]
% 51.63/6.98  --demod_completeness_check              fast
% 51.63/6.98  --demod_use_ground                      true
% 51.63/6.98  --sup_to_prop_solver                    passive
% 51.63/6.98  --sup_prop_simpl_new                    true
% 51.63/6.98  --sup_prop_simpl_given                  true
% 51.63/6.98  --sup_fun_splitting                     true
% 51.63/6.98  --sup_smt_interval                      50000
% 51.63/6.98  
% 51.63/6.98  ------ Superposition Simplification Setup
% 51.63/6.98  
% 51.63/6.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.63/6.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.63/6.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.63/6.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.63/6.98  --sup_full_triv                         [TrivRules;PropSubs]
% 51.63/6.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.63/6.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.63/6.98  --sup_immed_triv                        [TrivRules]
% 51.63/6.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.63/6.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.63/6.98  --sup_immed_bw_main                     []
% 51.63/6.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.63/6.98  --sup_input_triv                        [Unflattening;TrivRules]
% 51.63/6.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.63/6.98  --sup_input_bw                          []
% 51.63/6.98  
% 51.63/6.98  ------ Combination Options
% 51.63/6.98  
% 51.63/6.98  --comb_res_mult                         3
% 51.63/6.98  --comb_sup_mult                         2
% 51.63/6.98  --comb_inst_mult                        10
% 51.63/6.98  
% 51.63/6.98  ------ Debug Options
% 51.63/6.98  
% 51.63/6.98  --dbg_backtrace                         false
% 51.63/6.98  --dbg_dump_prop_clauses                 false
% 51.63/6.98  --dbg_dump_prop_clauses_file            -
% 51.63/6.98  --dbg_out_stat                          false
% 51.63/6.98  ------ Parsing...
% 51.63/6.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.63/6.98  
% 51.63/6.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 51.63/6.98  
% 51.63/6.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.63/6.98  
% 51.63/6.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.63/6.98  ------ Proving...
% 51.63/6.98  ------ Problem Properties 
% 51.63/6.98  
% 51.63/6.98  
% 51.63/6.98  clauses                                 35
% 51.63/6.98  conjectures                             4
% 51.63/6.98  EPR                                     5
% 51.63/6.98  Horn                                    31
% 51.63/6.98  unary                                   8
% 51.63/6.98  binary                                  10
% 51.63/6.98  lits                                    96
% 51.63/6.98  lits eq                                 24
% 51.63/6.98  fd_pure                                 0
% 51.63/6.98  fd_pseudo                               0
% 51.63/6.98  fd_cond                                 0
% 51.63/6.98  fd_pseudo_cond                          4
% 51.63/6.98  AC symbols                              0
% 51.63/6.98  
% 51.63/6.98  ------ Schedule dynamic 5 is on 
% 51.63/6.98  
% 51.63/6.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.63/6.98  
% 51.63/6.98  
% 51.63/6.98  ------ 
% 51.63/6.98  Current options:
% 51.63/6.98  ------ 
% 51.63/6.98  
% 51.63/6.98  ------ Input Options
% 51.63/6.98  
% 51.63/6.98  --out_options                           all
% 51.63/6.98  --tptp_safe_out                         true
% 51.63/6.98  --problem_path                          ""
% 51.63/6.98  --include_path                          ""
% 51.63/6.98  --clausifier                            res/vclausify_rel
% 51.63/6.98  --clausifier_options                    ""
% 51.63/6.98  --stdin                                 false
% 51.63/6.98  --stats_out                             all
% 51.63/6.98  
% 51.63/6.98  ------ General Options
% 51.63/6.98  
% 51.63/6.98  --fof                                   false
% 51.63/6.98  --time_out_real                         305.
% 51.63/6.98  --time_out_virtual                      -1.
% 51.63/6.98  --symbol_type_check                     false
% 51.63/6.98  --clausify_out                          false
% 51.63/6.98  --sig_cnt_out                           false
% 51.63/6.98  --trig_cnt_out                          false
% 51.63/6.98  --trig_cnt_out_tolerance                1.
% 51.63/6.98  --trig_cnt_out_sk_spl                   false
% 51.63/6.98  --abstr_cl_out                          false
% 51.63/6.98  
% 51.63/6.98  ------ Global Options
% 51.63/6.98  
% 51.63/6.98  --schedule                              default
% 51.63/6.98  --add_important_lit                     false
% 51.63/6.98  --prop_solver_per_cl                    1000
% 51.63/6.98  --min_unsat_core                        false
% 51.63/6.98  --soft_assumptions                      false
% 51.63/6.98  --soft_lemma_size                       3
% 51.63/6.98  --prop_impl_unit_size                   0
% 51.63/6.98  --prop_impl_unit                        []
% 51.63/6.98  --share_sel_clauses                     true
% 51.63/6.98  --reset_solvers                         false
% 51.63/6.98  --bc_imp_inh                            [conj_cone]
% 51.63/6.98  --conj_cone_tolerance                   3.
% 51.63/6.98  --extra_neg_conj                        none
% 51.63/6.98  --large_theory_mode                     true
% 51.63/6.98  --prolific_symb_bound                   200
% 51.63/6.98  --lt_threshold                          2000
% 51.63/6.98  --clause_weak_htbl                      true
% 51.63/6.98  --gc_record_bc_elim                     false
% 51.63/6.98  
% 51.63/6.98  ------ Preprocessing Options
% 51.63/6.98  
% 51.63/6.98  --preprocessing_flag                    true
% 51.63/6.98  --time_out_prep_mult                    0.1
% 51.63/6.98  --splitting_mode                        input
% 51.63/6.98  --splitting_grd                         true
% 51.63/6.98  --splitting_cvd                         false
% 51.63/6.98  --splitting_cvd_svl                     false
% 51.63/6.98  --splitting_nvd                         32
% 51.63/6.98  --sub_typing                            true
% 51.63/6.98  --prep_gs_sim                           true
% 51.63/6.98  --prep_unflatten                        true
% 51.63/6.98  --prep_res_sim                          true
% 51.63/6.98  --prep_upred                            true
% 51.63/6.98  --prep_sem_filter                       exhaustive
% 51.63/6.98  --prep_sem_filter_out                   false
% 51.63/6.98  --pred_elim                             true
% 51.63/6.98  --res_sim_input                         true
% 51.63/6.98  --eq_ax_congr_red                       true
% 51.63/6.98  --pure_diseq_elim                       true
% 51.63/6.98  --brand_transform                       false
% 51.63/6.98  --non_eq_to_eq                          false
% 51.63/6.98  --prep_def_merge                        true
% 51.63/6.98  --prep_def_merge_prop_impl              false
% 51.63/6.98  --prep_def_merge_mbd                    true
% 51.63/6.98  --prep_def_merge_tr_red                 false
% 51.63/6.98  --prep_def_merge_tr_cl                  false
% 51.63/6.98  --smt_preprocessing                     true
% 51.63/6.98  --smt_ac_axioms                         fast
% 51.63/6.98  --preprocessed_out                      false
% 51.63/6.98  --preprocessed_stats                    false
% 51.63/6.98  
% 51.63/6.98  ------ Abstraction refinement Options
% 51.63/6.98  
% 51.63/6.98  --abstr_ref                             []
% 51.63/6.98  --abstr_ref_prep                        false
% 51.63/6.98  --abstr_ref_until_sat                   false
% 51.63/6.98  --abstr_ref_sig_restrict                funpre
% 51.63/6.98  --abstr_ref_af_restrict_to_split_sk     false
% 51.63/6.98  --abstr_ref_under                       []
% 51.63/6.98  
% 51.63/6.98  ------ SAT Options
% 51.63/6.98  
% 51.63/6.98  --sat_mode                              false
% 51.63/6.98  --sat_fm_restart_options                ""
% 51.63/6.98  --sat_gr_def                            false
% 51.63/6.98  --sat_epr_types                         true
% 51.63/6.98  --sat_non_cyclic_types                  false
% 51.63/6.98  --sat_finite_models                     false
% 51.63/6.98  --sat_fm_lemmas                         false
% 51.63/6.98  --sat_fm_prep                           false
% 51.63/6.98  --sat_fm_uc_incr                        true
% 51.63/6.98  --sat_out_model                         small
% 51.63/6.98  --sat_out_clauses                       false
% 51.63/6.98  
% 51.63/6.98  ------ QBF Options
% 51.63/6.98  
% 51.63/6.98  --qbf_mode                              false
% 51.63/6.98  --qbf_elim_univ                         false
% 51.63/6.98  --qbf_dom_inst                          none
% 51.63/6.98  --qbf_dom_pre_inst                      false
% 51.63/6.98  --qbf_sk_in                             false
% 51.63/6.98  --qbf_pred_elim                         true
% 51.63/6.98  --qbf_split                             512
% 51.63/6.98  
% 51.63/6.98  ------ BMC1 Options
% 51.63/6.98  
% 51.63/6.98  --bmc1_incremental                      false
% 51.63/6.98  --bmc1_axioms                           reachable_all
% 51.63/6.98  --bmc1_min_bound                        0
% 51.63/6.98  --bmc1_max_bound                        -1
% 51.63/6.98  --bmc1_max_bound_default                -1
% 51.63/6.98  --bmc1_symbol_reachability              true
% 51.63/6.98  --bmc1_property_lemmas                  false
% 51.63/6.98  --bmc1_k_induction                      false
% 51.63/6.98  --bmc1_non_equiv_states                 false
% 51.63/6.98  --bmc1_deadlock                         false
% 51.63/6.98  --bmc1_ucm                              false
% 51.63/6.98  --bmc1_add_unsat_core                   none
% 51.63/6.98  --bmc1_unsat_core_children              false
% 51.63/6.98  --bmc1_unsat_core_extrapolate_axioms    false
% 51.63/6.98  --bmc1_out_stat                         full
% 51.63/6.98  --bmc1_ground_init                      false
% 51.63/6.98  --bmc1_pre_inst_next_state              false
% 51.63/6.98  --bmc1_pre_inst_state                   false
% 51.63/6.98  --bmc1_pre_inst_reach_state             false
% 51.63/6.98  --bmc1_out_unsat_core                   false
% 51.63/6.98  --bmc1_aig_witness_out                  false
% 51.63/6.98  --bmc1_verbose                          false
% 51.63/6.98  --bmc1_dump_clauses_tptp                false
% 51.63/6.98  --bmc1_dump_unsat_core_tptp             false
% 51.63/6.98  --bmc1_dump_file                        -
% 51.63/6.98  --bmc1_ucm_expand_uc_limit              128
% 51.63/6.98  --bmc1_ucm_n_expand_iterations          6
% 51.63/6.98  --bmc1_ucm_extend_mode                  1
% 51.63/6.98  --bmc1_ucm_init_mode                    2
% 51.63/6.98  --bmc1_ucm_cone_mode                    none
% 51.63/6.98  --bmc1_ucm_reduced_relation_type        0
% 51.63/6.98  --bmc1_ucm_relax_model                  4
% 51.63/6.98  --bmc1_ucm_full_tr_after_sat            true
% 51.63/6.98  --bmc1_ucm_expand_neg_assumptions       false
% 51.63/6.98  --bmc1_ucm_layered_model                none
% 51.63/6.98  --bmc1_ucm_max_lemma_size               10
% 51.63/6.98  
% 51.63/6.98  ------ AIG Options
% 51.63/6.98  
% 51.63/6.98  --aig_mode                              false
% 51.63/6.98  
% 51.63/6.98  ------ Instantiation Options
% 51.63/6.98  
% 51.63/6.98  --instantiation_flag                    true
% 51.63/6.98  --inst_sos_flag                         true
% 51.63/6.98  --inst_sos_phase                        true
% 51.63/6.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.63/6.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.63/6.98  --inst_lit_sel_side                     none
% 51.63/6.98  --inst_solver_per_active                1400
% 51.63/6.98  --inst_solver_calls_frac                1.
% 51.63/6.98  --inst_passive_queue_type               priority_queues
% 51.63/6.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.63/6.98  --inst_passive_queues_freq              [25;2]
% 51.63/6.98  --inst_dismatching                      true
% 51.63/6.98  --inst_eager_unprocessed_to_passive     true
% 51.63/6.98  --inst_prop_sim_given                   true
% 51.63/6.98  --inst_prop_sim_new                     false
% 51.63/6.98  --inst_subs_new                         false
% 51.63/6.98  --inst_eq_res_simp                      false
% 51.63/6.98  --inst_subs_given                       false
% 51.63/6.98  --inst_orphan_elimination               true
% 51.63/6.98  --inst_learning_loop_flag               true
% 51.63/6.98  --inst_learning_start                   3000
% 51.63/6.98  --inst_learning_factor                  2
% 51.63/6.98  --inst_start_prop_sim_after_learn       3
% 51.63/6.98  --inst_sel_renew                        solver
% 51.63/6.98  --inst_lit_activity_flag                true
% 51.63/6.98  --inst_restr_to_given                   false
% 51.63/6.98  --inst_activity_threshold               500
% 51.63/6.98  --inst_out_proof                        true
% 51.63/6.98  
% 51.63/6.98  ------ Resolution Options
% 51.63/6.98  
% 51.63/6.98  --resolution_flag                       false
% 51.63/6.98  --res_lit_sel                           adaptive
% 51.63/6.98  --res_lit_sel_side                      none
% 51.63/6.98  --res_ordering                          kbo
% 51.63/6.98  --res_to_prop_solver                    active
% 51.63/6.98  --res_prop_simpl_new                    false
% 51.63/6.98  --res_prop_simpl_given                  true
% 51.63/6.98  --res_passive_queue_type                priority_queues
% 51.63/6.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.63/6.98  --res_passive_queues_freq               [15;5]
% 51.63/6.98  --res_forward_subs                      full
% 51.63/6.98  --res_backward_subs                     full
% 51.63/6.98  --res_forward_subs_resolution           true
% 51.63/6.98  --res_backward_subs_resolution          true
% 51.63/6.98  --res_orphan_elimination                true
% 51.63/6.98  --res_time_limit                        2.
% 51.63/6.98  --res_out_proof                         true
% 51.63/6.98  
% 51.63/6.98  ------ Superposition Options
% 51.63/6.98  
% 51.63/6.98  --superposition_flag                    true
% 51.63/6.98  --sup_passive_queue_type                priority_queues
% 51.63/6.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.63/6.98  --sup_passive_queues_freq               [8;1;4]
% 51.63/6.98  --demod_completeness_check              fast
% 51.63/6.98  --demod_use_ground                      true
% 51.63/6.98  --sup_to_prop_solver                    passive
% 51.63/6.98  --sup_prop_simpl_new                    true
% 51.63/6.98  --sup_prop_simpl_given                  true
% 51.63/6.98  --sup_fun_splitting                     true
% 51.63/6.98  --sup_smt_interval                      50000
% 51.63/6.98  
% 51.63/6.98  ------ Superposition Simplification Setup
% 51.63/6.98  
% 51.63/6.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.63/6.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.63/6.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.63/6.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.63/6.98  --sup_full_triv                         [TrivRules;PropSubs]
% 51.63/6.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.63/6.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.63/6.98  --sup_immed_triv                        [TrivRules]
% 51.63/6.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.63/6.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.63/6.98  --sup_immed_bw_main                     []
% 51.63/6.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.63/6.98  --sup_input_triv                        [Unflattening;TrivRules]
% 51.63/6.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.63/6.98  --sup_input_bw                          []
% 51.63/6.98  
% 51.63/6.98  ------ Combination Options
% 51.63/6.98  
% 51.63/6.98  --comb_res_mult                         3
% 51.63/6.98  --comb_sup_mult                         2
% 51.63/6.98  --comb_inst_mult                        10
% 51.63/6.98  
% 51.63/6.98  ------ Debug Options
% 51.63/6.98  
% 51.63/6.98  --dbg_backtrace                         false
% 51.63/6.98  --dbg_dump_prop_clauses                 false
% 51.63/6.98  --dbg_dump_prop_clauses_file            -
% 51.63/6.98  --dbg_out_stat                          false
% 51.63/6.98  
% 51.63/6.98  
% 51.63/6.98  
% 51.63/6.98  
% 51.63/6.98  ------ Proving...
% 51.63/6.98  
% 51.63/6.98  
% 51.63/6.98  % SZS status Theorem for theBenchmark.p
% 51.63/6.98  
% 51.63/6.98  % SZS output start CNFRefutation for theBenchmark.p
% 51.63/6.98  
% 51.63/6.98  fof(f18,conjecture,(
% 51.63/6.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 51.63/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.63/6.98  
% 51.63/6.98  fof(f19,negated_conjecture,(
% 51.63/6.98    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 51.63/6.98    inference(negated_conjecture,[],[f18])).
% 51.63/6.98  
% 51.63/6.98  fof(f43,plain,(
% 51.63/6.98    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 51.63/6.98    inference(ennf_transformation,[],[f19])).
% 51.63/6.98  
% 51.63/6.98  fof(f44,plain,(
% 51.63/6.98    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 51.63/6.98    inference(flattening,[],[f43])).
% 51.63/6.98  
% 51.63/6.98  fof(f62,plain,(
% 51.63/6.98    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_funct_1(k5_relat_1(k2_funct_1(sK6),sK6),sK5) != sK5 | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK5)) != sK5) & r2_hidden(sK5,k2_relat_1(sK6)) & v2_funct_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 51.63/6.98    introduced(choice_axiom,[])).
% 51.63/6.98  
% 51.63/6.98  fof(f63,plain,(
% 51.63/6.98    (k1_funct_1(k5_relat_1(k2_funct_1(sK6),sK6),sK5) != sK5 | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK5)) != sK5) & r2_hidden(sK5,k2_relat_1(sK6)) & v2_funct_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 51.63/6.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f44,f62])).
% 51.63/6.98  
% 51.63/6.98  fof(f100,plain,(
% 51.63/6.98    r2_hidden(sK5,k2_relat_1(sK6))),
% 51.63/6.98    inference(cnf_transformation,[],[f63])).
% 51.63/6.98  
% 51.63/6.98  fof(f2,axiom,(
% 51.63/6.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 51.63/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.63/6.98  
% 51.63/6.98  fof(f49,plain,(
% 51.63/6.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.63/6.98    inference(nnf_transformation,[],[f2])).
% 51.63/6.98  
% 51.63/6.98  fof(f50,plain,(
% 51.63/6.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.63/6.98    inference(flattening,[],[f49])).
% 51.63/6.98  
% 51.63/6.98  fof(f67,plain,(
% 51.63/6.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 51.63/6.98    inference(cnf_transformation,[],[f50])).
% 51.63/6.98  
% 51.63/6.98  fof(f103,plain,(
% 51.63/6.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 51.63/6.98    inference(equality_resolution,[],[f67])).
% 51.63/6.98  
% 51.63/6.98  fof(f97,plain,(
% 51.63/6.98    v1_relat_1(sK6)),
% 51.63/6.98    inference(cnf_transformation,[],[f63])).
% 51.63/6.98  
% 51.63/6.98  fof(f5,axiom,(
% 51.63/6.98    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 51.63/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.63/6.98  
% 51.63/6.98  fof(f23,plain,(
% 51.63/6.98    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 51.63/6.98    inference(ennf_transformation,[],[f5])).
% 51.63/6.98  
% 51.63/6.98  fof(f73,plain,(
% 51.63/6.98    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 51.63/6.98    inference(cnf_transformation,[],[f23])).
% 51.63/6.98  
% 51.63/6.98  fof(f7,axiom,(
% 51.63/6.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 51.63/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.63/6.98  
% 51.63/6.98  fof(f25,plain,(
% 51.63/6.98    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 51.63/6.98    inference(ennf_transformation,[],[f7])).
% 51.63/6.98  
% 51.63/6.98  fof(f26,plain,(
% 51.63/6.98    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 51.63/6.98    inference(flattening,[],[f25])).
% 51.63/6.98  
% 51.63/6.98  fof(f75,plain,(
% 51.63/6.98    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 51.63/6.98    inference(cnf_transformation,[],[f26])).
% 51.63/6.98  
% 51.63/6.98  fof(f72,plain,(
% 51.63/6.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 51.63/6.98    inference(cnf_transformation,[],[f23])).
% 51.63/6.98  
% 51.63/6.98  fof(f3,axiom,(
% 51.63/6.98    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 51.63/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.63/6.98  
% 51.63/6.98  fof(f21,plain,(
% 51.63/6.98    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 51.63/6.98    inference(ennf_transformation,[],[f3])).
% 51.63/6.98  
% 51.63/6.98  fof(f70,plain,(
% 51.63/6.98    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 51.63/6.98    inference(cnf_transformation,[],[f21])).
% 51.63/6.98  
% 51.63/6.98  fof(f15,axiom,(
% 51.63/6.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0))))),
% 51.63/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.63/6.98  
% 51.63/6.98  fof(f37,plain,(
% 51.63/6.98    ! [X0,X1] : (! [X2] : ((k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 51.63/6.98    inference(ennf_transformation,[],[f15])).
% 51.63/6.98  
% 51.63/6.98  fof(f38,plain,(
% 51.63/6.98    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 51.63/6.99    inference(flattening,[],[f37])).
% 51.63/6.99  
% 51.63/6.99  fof(f90,plain,(
% 51.63/6.99    ( ! [X2,X0,X1] : (k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 51.63/6.99    inference(cnf_transformation,[],[f38])).
% 51.63/6.99  
% 51.63/6.99  fof(f98,plain,(
% 51.63/6.99    v1_funct_1(sK6)),
% 51.63/6.99    inference(cnf_transformation,[],[f63])).
% 51.63/6.99  
% 51.63/6.99  fof(f11,axiom,(
% 51.63/6.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 51.63/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.63/6.99  
% 51.63/6.99  fof(f31,plain,(
% 51.63/6.99    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 51.63/6.99    inference(ennf_transformation,[],[f11])).
% 51.63/6.99  
% 51.63/6.99  fof(f32,plain,(
% 51.63/6.99    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.63/6.99    inference(flattening,[],[f31])).
% 51.63/6.99  
% 51.63/6.99  fof(f84,plain,(
% 51.63/6.99    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.63/6.99    inference(cnf_transformation,[],[f32])).
% 51.63/6.99  
% 51.63/6.99  fof(f99,plain,(
% 51.63/6.99    v2_funct_1(sK6)),
% 51.63/6.99    inference(cnf_transformation,[],[f63])).
% 51.63/6.99  
% 51.63/6.99  fof(f12,axiom,(
% 51.63/6.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 51.63/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.63/6.99  
% 51.63/6.99  fof(f33,plain,(
% 51.63/6.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 51.63/6.99    inference(ennf_transformation,[],[f12])).
% 51.63/6.99  
% 51.63/6.99  fof(f34,plain,(
% 51.63/6.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.63/6.99    inference(flattening,[],[f33])).
% 51.63/6.99  
% 51.63/6.99  fof(f86,plain,(
% 51.63/6.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.63/6.99    inference(cnf_transformation,[],[f34])).
% 51.63/6.99  
% 51.63/6.99  fof(f10,axiom,(
% 51.63/6.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 51.63/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.63/6.99  
% 51.63/6.99  fof(f29,plain,(
% 51.63/6.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 51.63/6.99    inference(ennf_transformation,[],[f10])).
% 51.63/6.99  
% 51.63/6.99  fof(f30,plain,(
% 51.63/6.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.63/6.99    inference(flattening,[],[f29])).
% 51.63/6.99  
% 51.63/6.99  fof(f51,plain,(
% 51.63/6.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.63/6.99    inference(nnf_transformation,[],[f30])).
% 51.63/6.99  
% 51.63/6.99  fof(f52,plain,(
% 51.63/6.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.63/6.99    inference(rectify,[],[f51])).
% 51.63/6.99  
% 51.63/6.99  fof(f55,plain,(
% 51.63/6.99    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 51.63/6.99    introduced(choice_axiom,[])).
% 51.63/6.99  
% 51.63/6.99  fof(f54,plain,(
% 51.63/6.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 51.63/6.99    introduced(choice_axiom,[])).
% 51.63/6.99  
% 51.63/6.99  fof(f53,plain,(
% 51.63/6.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 51.63/6.99    introduced(choice_axiom,[])).
% 51.63/6.99  
% 51.63/6.99  fof(f56,plain,(
% 51.63/6.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.63/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f52,f55,f54,f53])).
% 51.63/6.99  
% 51.63/6.99  fof(f79,plain,(
% 51.63/6.99    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.63/6.99    inference(cnf_transformation,[],[f56])).
% 51.63/6.99  
% 51.63/6.99  fof(f106,plain,(
% 51.63/6.99    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.63/6.99    inference(equality_resolution,[],[f79])).
% 51.63/6.99  
% 51.63/6.99  fof(f78,plain,(
% 51.63/6.99    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.63/6.99    inference(cnf_transformation,[],[f56])).
% 51.63/6.99  
% 51.63/6.99  fof(f107,plain,(
% 51.63/6.99    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.63/6.99    inference(equality_resolution,[],[f78])).
% 51.63/6.99  
% 51.63/6.99  fof(f17,axiom,(
% 51.63/6.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 51.63/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.63/6.99  
% 51.63/6.99  fof(f41,plain,(
% 51.63/6.99    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 51.63/6.99    inference(ennf_transformation,[],[f17])).
% 51.63/6.99  
% 51.63/6.99  fof(f42,plain,(
% 51.63/6.99    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 51.63/6.99    inference(flattening,[],[f41])).
% 51.63/6.99  
% 51.63/6.99  fof(f95,plain,(
% 51.63/6.99    ( ! [X0,X1] : (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 51.63/6.99    inference(cnf_transformation,[],[f42])).
% 51.63/6.99  
% 51.63/6.99  fof(f101,plain,(
% 51.63/6.99    k1_funct_1(k5_relat_1(k2_funct_1(sK6),sK6),sK5) != sK5 | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK5)) != sK5),
% 51.63/6.99    inference(cnf_transformation,[],[f63])).
% 51.63/6.99  
% 51.63/6.99  cnf(c_34,negated_conjecture,
% 51.63/6.99      ( r2_hidden(sK5,k2_relat_1(sK6)) ),
% 51.63/6.99      inference(cnf_transformation,[],[f100]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_1191,plain,
% 51.63/6.99      ( r2_hidden(sK5,k2_relat_1(sK6)) = iProver_top ),
% 51.63/6.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_5,plain,
% 51.63/6.99      ( r1_tarski(X0,X0) ),
% 51.63/6.99      inference(cnf_transformation,[],[f103]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_1214,plain,
% 51.63/6.99      ( r1_tarski(X0,X0) = iProver_top ),
% 51.63/6.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_37,negated_conjecture,
% 51.63/6.99      ( v1_relat_1(sK6) ),
% 51.63/6.99      inference(cnf_transformation,[],[f97]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_1189,plain,
% 51.63/6.99      ( v1_relat_1(sK6) = iProver_top ),
% 51.63/6.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_8,plain,
% 51.63/6.99      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 51.63/6.99      inference(cnf_transformation,[],[f73]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_1211,plain,
% 51.63/6.99      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 51.63/6.99      | v1_relat_1(X0) != iProver_top ),
% 51.63/6.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_2132,plain,
% 51.63/6.99      ( k2_relat_1(k4_relat_1(sK6)) = k1_relat_1(sK6) ),
% 51.63/6.99      inference(superposition,[status(thm)],[c_1189,c_1211]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_11,plain,
% 51.63/6.99      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 51.63/6.99      | ~ v1_relat_1(X0)
% 51.63/6.99      | ~ v1_relat_1(X1)
% 51.63/6.99      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 51.63/6.99      inference(cnf_transformation,[],[f75]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_1208,plain,
% 51.63/6.99      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 51.63/6.99      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 51.63/6.99      | v1_relat_1(X1) != iProver_top
% 51.63/6.99      | v1_relat_1(X0) != iProver_top ),
% 51.63/6.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_4517,plain,
% 51.63/6.99      ( k1_relat_1(k5_relat_1(k4_relat_1(sK6),X0)) = k1_relat_1(k4_relat_1(sK6))
% 51.63/6.99      | r1_tarski(k1_relat_1(sK6),k1_relat_1(X0)) != iProver_top
% 51.63/6.99      | v1_relat_1(X0) != iProver_top
% 51.63/6.99      | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
% 51.63/6.99      inference(superposition,[status(thm)],[c_2132,c_1208]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_9,plain,
% 51.63/6.99      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 51.63/6.99      inference(cnf_transformation,[],[f72]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_1210,plain,
% 51.63/6.99      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 51.63/6.99      | v1_relat_1(X0) != iProver_top ),
% 51.63/6.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_1824,plain,
% 51.63/6.99      ( k1_relat_1(k4_relat_1(sK6)) = k2_relat_1(sK6) ),
% 51.63/6.99      inference(superposition,[status(thm)],[c_1189,c_1210]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_4521,plain,
% 51.63/6.99      ( k1_relat_1(k5_relat_1(k4_relat_1(sK6),X0)) = k2_relat_1(sK6)
% 51.63/6.99      | r1_tarski(k1_relat_1(sK6),k1_relat_1(X0)) != iProver_top
% 51.63/6.99      | v1_relat_1(X0) != iProver_top
% 51.63/6.99      | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
% 51.63/6.99      inference(light_normalisation,[status(thm)],[c_4517,c_1824]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_38,plain,
% 51.63/6.99      ( v1_relat_1(sK6) = iProver_top ),
% 51.63/6.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_6,plain,
% 51.63/6.99      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 51.63/6.99      inference(cnf_transformation,[],[f70]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_118,plain,
% 51.63/6.99      ( v1_relat_1(X0) != iProver_top
% 51.63/6.99      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 51.63/6.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_120,plain,
% 51.63/6.99      ( v1_relat_1(k4_relat_1(sK6)) = iProver_top
% 51.63/6.99      | v1_relat_1(sK6) != iProver_top ),
% 51.63/6.99      inference(instantiation,[status(thm)],[c_118]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_5283,plain,
% 51.63/6.99      ( v1_relat_1(X0) != iProver_top
% 51.63/6.99      | r1_tarski(k1_relat_1(sK6),k1_relat_1(X0)) != iProver_top
% 51.63/6.99      | k1_relat_1(k5_relat_1(k4_relat_1(sK6),X0)) = k2_relat_1(sK6) ),
% 51.63/6.99      inference(global_propositional_subsumption,
% 51.63/6.99                [status(thm)],
% 51.63/6.99                [c_4521,c_38,c_120]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_5284,plain,
% 51.63/6.99      ( k1_relat_1(k5_relat_1(k4_relat_1(sK6),X0)) = k2_relat_1(sK6)
% 51.63/6.99      | r1_tarski(k1_relat_1(sK6),k1_relat_1(X0)) != iProver_top
% 51.63/6.99      | v1_relat_1(X0) != iProver_top ),
% 51.63/6.99      inference(renaming,[status(thm)],[c_5283]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_5289,plain,
% 51.63/6.99      ( k1_relat_1(k5_relat_1(k4_relat_1(sK6),sK6)) = k2_relat_1(sK6)
% 51.63/6.99      | v1_relat_1(sK6) != iProver_top ),
% 51.63/6.99      inference(superposition,[status(thm)],[c_1214,c_5284]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_6950,plain,
% 51.63/6.99      ( k1_relat_1(k5_relat_1(k4_relat_1(sK6),sK6)) = k2_relat_1(sK6) ),
% 51.63/6.99      inference(global_propositional_subsumption,
% 51.63/6.99                [status(thm)],
% 51.63/6.99                [c_5289,c_38]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_26,plain,
% 51.63/6.99      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,X2)))
% 51.63/6.99      | ~ v1_funct_1(X2)
% 51.63/6.99      | ~ v1_funct_1(X1)
% 51.63/6.99      | ~ v1_relat_1(X2)
% 51.63/6.99      | ~ v1_relat_1(X1)
% 51.63/6.99      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 51.63/6.99      inference(cnf_transformation,[],[f90]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_1195,plain,
% 51.63/6.99      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 51.63/6.99      | r2_hidden(X2,k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
% 51.63/6.99      | v1_funct_1(X0) != iProver_top
% 51.63/6.99      | v1_funct_1(X1) != iProver_top
% 51.63/6.99      | v1_relat_1(X0) != iProver_top
% 51.63/6.99      | v1_relat_1(X1) != iProver_top ),
% 51.63/6.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_6957,plain,
% 51.63/6.99      ( k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),X0) = k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),X0))
% 51.63/6.99      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 51.63/6.99      | v1_funct_1(k4_relat_1(sK6)) != iProver_top
% 51.63/6.99      | v1_funct_1(sK6) != iProver_top
% 51.63/6.99      | v1_relat_1(k4_relat_1(sK6)) != iProver_top
% 51.63/6.99      | v1_relat_1(sK6) != iProver_top ),
% 51.63/6.99      inference(superposition,[status(thm)],[c_6950,c_1195]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_36,negated_conjecture,
% 51.63/6.99      ( v1_funct_1(sK6) ),
% 51.63/6.99      inference(cnf_transformation,[],[f98]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_39,plain,
% 51.63/6.99      ( v1_funct_1(sK6) = iProver_top ),
% 51.63/6.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_20,plain,
% 51.63/6.99      ( ~ v2_funct_1(X0)
% 51.63/6.99      | ~ v1_funct_1(X0)
% 51.63/6.99      | ~ v1_relat_1(X0)
% 51.63/6.99      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 51.63/6.99      inference(cnf_transformation,[],[f84]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_35,negated_conjecture,
% 51.63/6.99      ( v2_funct_1(sK6) ),
% 51.63/6.99      inference(cnf_transformation,[],[f99]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_404,plain,
% 51.63/6.99      ( ~ v1_funct_1(X0)
% 51.63/6.99      | ~ v1_relat_1(X0)
% 51.63/6.99      | k2_funct_1(X0) = k4_relat_1(X0)
% 51.63/6.99      | sK6 != X0 ),
% 51.63/6.99      inference(resolution_lifted,[status(thm)],[c_20,c_35]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_405,plain,
% 51.63/6.99      ( ~ v1_funct_1(sK6)
% 51.63/6.99      | ~ v1_relat_1(sK6)
% 51.63/6.99      | k2_funct_1(sK6) = k4_relat_1(sK6) ),
% 51.63/6.99      inference(unflattening,[status(thm)],[c_404]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_79,plain,
% 51.63/6.99      ( ~ v2_funct_1(sK6)
% 51.63/6.99      | ~ v1_funct_1(sK6)
% 51.63/6.99      | ~ v1_relat_1(sK6)
% 51.63/6.99      | k2_funct_1(sK6) = k4_relat_1(sK6) ),
% 51.63/6.99      inference(instantiation,[status(thm)],[c_20]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_407,plain,
% 51.63/6.99      ( k2_funct_1(sK6) = k4_relat_1(sK6) ),
% 51.63/6.99      inference(global_propositional_subsumption,
% 51.63/6.99                [status(thm)],
% 51.63/6.99                [c_405,c_37,c_36,c_35,c_79]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_21,plain,
% 51.63/6.99      ( ~ v1_funct_1(X0)
% 51.63/6.99      | v1_funct_1(k2_funct_1(X0))
% 51.63/6.99      | ~ v1_relat_1(X0) ),
% 51.63/6.99      inference(cnf_transformation,[],[f86]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_1199,plain,
% 51.63/6.99      ( v1_funct_1(X0) != iProver_top
% 51.63/6.99      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 51.63/6.99      | v1_relat_1(X0) != iProver_top ),
% 51.63/6.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_2862,plain,
% 51.63/6.99      ( v1_funct_1(k4_relat_1(sK6)) = iProver_top
% 51.63/6.99      | v1_funct_1(sK6) != iProver_top
% 51.63/6.99      | v1_relat_1(sK6) != iProver_top ),
% 51.63/6.99      inference(superposition,[status(thm)],[c_407,c_1199]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_143578,plain,
% 51.63/6.99      ( k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),X0) = k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),X0))
% 51.63/6.99      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 51.63/6.99      inference(global_propositional_subsumption,
% 51.63/6.99                [status(thm)],
% 51.63/6.99                [c_6957,c_38,c_39,c_120,c_2862]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_143590,plain,
% 51.63/6.99      ( k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),sK5)) = k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5) ),
% 51.63/6.99      inference(superposition,[status(thm)],[c_1191,c_143578]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_18,plain,
% 51.63/6.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 51.63/6.99      | ~ v1_funct_1(X1)
% 51.63/6.99      | ~ v1_relat_1(X1)
% 51.63/6.99      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 51.63/6.99      inference(cnf_transformation,[],[f106]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_1201,plain,
% 51.63/6.99      ( k1_funct_1(X0,sK3(X0,X1)) = X1
% 51.63/6.99      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 51.63/6.99      | v1_funct_1(X0) != iProver_top
% 51.63/6.99      | v1_relat_1(X0) != iProver_top ),
% 51.63/6.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_3789,plain,
% 51.63/6.99      ( k1_funct_1(sK6,sK3(sK6,sK5)) = sK5
% 51.63/6.99      | v1_funct_1(sK6) != iProver_top
% 51.63/6.99      | v1_relat_1(sK6) != iProver_top ),
% 51.63/6.99      inference(superposition,[status(thm)],[c_1191,c_1201]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_3587,plain,
% 51.63/6.99      ( ~ r2_hidden(sK5,k2_relat_1(X0))
% 51.63/6.99      | ~ v1_funct_1(X0)
% 51.63/6.99      | ~ v1_relat_1(X0)
% 51.63/6.99      | k1_funct_1(X0,sK3(X0,sK5)) = sK5 ),
% 51.63/6.99      inference(instantiation,[status(thm)],[c_18]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_3589,plain,
% 51.63/6.99      ( ~ r2_hidden(sK5,k2_relat_1(sK6))
% 51.63/6.99      | ~ v1_funct_1(sK6)
% 51.63/6.99      | ~ v1_relat_1(sK6)
% 51.63/6.99      | k1_funct_1(sK6,sK3(sK6,sK5)) = sK5 ),
% 51.63/6.99      inference(instantiation,[status(thm)],[c_3587]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_4119,plain,
% 51.63/6.99      ( k1_funct_1(sK6,sK3(sK6,sK5)) = sK5 ),
% 51.63/6.99      inference(global_propositional_subsumption,
% 51.63/6.99                [status(thm)],
% 51.63/6.99                [c_3789,c_37,c_36,c_34,c_3589]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_19,plain,
% 51.63/6.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 51.63/6.99      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 51.63/6.99      | ~ v1_funct_1(X1)
% 51.63/6.99      | ~ v1_relat_1(X1) ),
% 51.63/6.99      inference(cnf_transformation,[],[f107]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_1200,plain,
% 51.63/6.99      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 51.63/6.99      | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
% 51.63/6.99      | v1_funct_1(X1) != iProver_top
% 51.63/6.99      | v1_relat_1(X1) != iProver_top ),
% 51.63/6.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_32,plain,
% 51.63/6.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 51.63/6.99      | ~ v2_funct_1(X1)
% 51.63/6.99      | ~ v1_funct_1(X1)
% 51.63/6.99      | ~ v1_relat_1(X1)
% 51.63/6.99      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
% 51.63/6.99      inference(cnf_transformation,[],[f95]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_412,plain,
% 51.63/6.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 51.63/6.99      | ~ v1_funct_1(X1)
% 51.63/6.99      | ~ v1_relat_1(X1)
% 51.63/6.99      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
% 51.63/6.99      | sK6 != X1 ),
% 51.63/6.99      inference(resolution_lifted,[status(thm)],[c_32,c_35]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_413,plain,
% 51.63/6.99      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 51.63/6.99      | ~ v1_funct_1(sK6)
% 51.63/6.99      | ~ v1_relat_1(sK6)
% 51.63/6.99      | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 ),
% 51.63/6.99      inference(unflattening,[status(thm)],[c_412]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_417,plain,
% 51.63/6.99      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 51.63/6.99      | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 ),
% 51.63/6.99      inference(global_propositional_subsumption,
% 51.63/6.99                [status(thm)],
% 51.63/6.99                [c_413,c_37,c_36]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_1188,plain,
% 51.63/6.99      ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0
% 51.63/6.99      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 51.63/6.99      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_1220,plain,
% 51.63/6.99      ( k1_funct_1(k4_relat_1(sK6),k1_funct_1(sK6,X0)) = X0
% 51.63/6.99      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 51.63/6.99      inference(light_normalisation,[status(thm)],[c_1188,c_407]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_3881,plain,
% 51.63/6.99      ( k1_funct_1(k4_relat_1(sK6),k1_funct_1(sK6,sK3(sK6,X0))) = sK3(sK6,X0)
% 51.63/6.99      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 51.63/6.99      | v1_funct_1(sK6) != iProver_top
% 51.63/6.99      | v1_relat_1(sK6) != iProver_top ),
% 51.63/6.99      inference(superposition,[status(thm)],[c_1200,c_1220]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_6581,plain,
% 51.63/6.99      ( k1_funct_1(k4_relat_1(sK6),k1_funct_1(sK6,sK3(sK6,X0))) = sK3(sK6,X0)
% 51.63/6.99      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 51.63/6.99      inference(global_propositional_subsumption,
% 51.63/6.99                [status(thm)],
% 51.63/6.99                [c_3881,c_38,c_39]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_6591,plain,
% 51.63/6.99      ( k1_funct_1(k4_relat_1(sK6),k1_funct_1(sK6,sK3(sK6,sK5))) = sK3(sK6,sK5) ),
% 51.63/6.99      inference(superposition,[status(thm)],[c_1191,c_6581]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_6594,plain,
% 51.63/6.99      ( k1_funct_1(k4_relat_1(sK6),sK5) = sK3(sK6,sK5) ),
% 51.63/6.99      inference(light_normalisation,[status(thm)],[c_6591,c_4119]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_143677,plain,
% 51.63/6.99      ( k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5) = sK5 ),
% 51.63/6.99      inference(light_normalisation,
% 51.63/6.99                [status(thm)],
% 51.63/6.99                [c_143590,c_4119,c_6594]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_33,negated_conjecture,
% 51.63/6.99      ( k1_funct_1(k5_relat_1(k2_funct_1(sK6),sK6),sK5) != sK5
% 51.63/6.99      | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK5)) != sK5 ),
% 51.63/6.99      inference(cnf_transformation,[],[f101]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_1221,plain,
% 51.63/6.99      ( k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5) != sK5
% 51.63/6.99      | k1_funct_1(sK6,k1_funct_1(k4_relat_1(sK6),sK5)) != sK5 ),
% 51.63/6.99      inference(light_normalisation,[status(thm)],[c_33,c_407]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_6614,plain,
% 51.63/6.99      ( k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5) != sK5
% 51.63/6.99      | k1_funct_1(sK6,sK3(sK6,sK5)) != sK5 ),
% 51.63/6.99      inference(demodulation,[status(thm)],[c_6594,c_1221]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_6615,plain,
% 51.63/6.99      ( k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5) != sK5
% 51.63/6.99      | sK5 != sK5 ),
% 51.63/6.99      inference(light_normalisation,[status(thm)],[c_6614,c_4119]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(c_6616,plain,
% 51.63/6.99      ( k1_funct_1(k5_relat_1(k4_relat_1(sK6),sK6),sK5) != sK5 ),
% 51.63/6.99      inference(equality_resolution_simp,[status(thm)],[c_6615]) ).
% 51.63/6.99  
% 51.63/6.99  cnf(contradiction,plain,
% 51.63/6.99      ( $false ),
% 51.63/6.99      inference(minisat,[status(thm)],[c_143677,c_6616]) ).
% 51.63/6.99  
% 51.63/6.99  
% 51.63/6.99  % SZS output end CNFRefutation for theBenchmark.p
% 51.63/6.99  
% 51.63/6.99  ------                               Statistics
% 51.63/6.99  
% 51.63/6.99  ------ General
% 51.63/6.99  
% 51.63/6.99  abstr_ref_over_cycles:                  0
% 51.63/6.99  abstr_ref_under_cycles:                 0
% 51.63/6.99  gc_basic_clause_elim:                   0
% 51.63/6.99  forced_gc_time:                         0
% 51.63/6.99  parsing_time:                           0.009
% 51.63/6.99  unif_index_cands_time:                  0.
% 51.63/6.99  unif_index_add_time:                    0.
% 51.63/6.99  orderings_time:                         0.
% 51.63/6.99  out_proof_time:                         0.024
% 51.63/6.99  total_time:                             6.112
% 51.63/6.99  num_of_symbols:                         50
% 51.63/6.99  num_of_terms:                           120988
% 51.63/6.99  
% 51.63/6.99  ------ Preprocessing
% 51.63/6.99  
% 51.63/6.99  num_of_splits:                          0
% 51.63/6.99  num_of_split_atoms:                     0
% 51.63/6.99  num_of_reused_defs:                     0
% 51.63/6.99  num_eq_ax_congr_red:                    27
% 51.63/6.99  num_of_sem_filtered_clauses:            1
% 51.63/6.99  num_of_subtypes:                        0
% 51.63/6.99  monotx_restored_types:                  0
% 51.63/6.99  sat_num_of_epr_types:                   0
% 51.63/6.99  sat_num_of_non_cyclic_types:            0
% 51.63/6.99  sat_guarded_non_collapsed_types:        0
% 51.63/6.99  num_pure_diseq_elim:                    0
% 51.63/6.99  simp_replaced_by:                       0
% 51.63/6.99  res_preprocessed:                       170
% 51.63/6.99  prep_upred:                             0
% 51.63/6.99  prep_unflattend:                        3
% 51.63/6.99  smt_new_axioms:                         0
% 51.63/6.99  pred_elim_cands:                        4
% 51.63/6.99  pred_elim:                              1
% 51.63/6.99  pred_elim_cl:                           1
% 51.63/6.99  pred_elim_cycles:                       3
% 51.63/6.99  merged_defs:                            0
% 51.63/6.99  merged_defs_ncl:                        0
% 51.63/6.99  bin_hyper_res:                          0
% 51.63/6.99  prep_cycles:                            4
% 51.63/6.99  pred_elim_time:                         0.003
% 51.63/6.99  splitting_time:                         0.
% 51.63/6.99  sem_filter_time:                        0.
% 51.63/6.99  monotx_time:                            0.001
% 51.63/6.99  subtype_inf_time:                       0.
% 51.63/6.99  
% 51.63/6.99  ------ Problem properties
% 51.63/6.99  
% 51.63/6.99  clauses:                                35
% 51.63/6.99  conjectures:                            4
% 51.63/6.99  epr:                                    5
% 51.63/6.99  horn:                                   31
% 51.63/6.99  ground:                                 5
% 51.63/6.99  unary:                                  8
% 51.63/6.99  binary:                                 10
% 51.63/6.99  lits:                                   96
% 51.63/6.99  lits_eq:                                24
% 51.63/6.99  fd_pure:                                0
% 51.63/6.99  fd_pseudo:                              0
% 51.63/6.99  fd_cond:                                0
% 51.63/6.99  fd_pseudo_cond:                         4
% 51.63/6.99  ac_symbols:                             0
% 51.63/6.99  
% 51.63/6.99  ------ Propositional Solver
% 51.63/6.99  
% 51.63/6.99  prop_solver_calls:                      76
% 51.63/6.99  prop_fast_solver_calls:                 5533
% 51.63/6.99  smt_solver_calls:                       0
% 51.63/6.99  smt_fast_solver_calls:                  0
% 51.63/6.99  prop_num_of_clauses:                    74648
% 51.63/6.99  prop_preprocess_simplified:             88578
% 51.63/6.99  prop_fo_subsumed:                       426
% 51.63/6.99  prop_solver_time:                       0.
% 51.63/6.99  smt_solver_time:                        0.
% 51.63/6.99  smt_fast_solver_time:                   0.
% 51.63/6.99  prop_fast_solver_time:                  0.
% 51.63/6.99  prop_unsat_core_time:                   0.005
% 51.63/6.99  
% 51.63/6.99  ------ QBF
% 51.63/6.99  
% 51.63/6.99  qbf_q_res:                              0
% 51.63/6.99  qbf_num_tautologies:                    0
% 51.63/6.99  qbf_prep_cycles:                        0
% 51.63/6.99  
% 51.63/6.99  ------ BMC1
% 51.63/6.99  
% 51.63/6.99  bmc1_current_bound:                     -1
% 51.63/6.99  bmc1_last_solved_bound:                 -1
% 51.63/6.99  bmc1_unsat_core_size:                   -1
% 51.63/6.99  bmc1_unsat_core_parents_size:           -1
% 51.63/6.99  bmc1_merge_next_fun:                    0
% 51.63/6.99  bmc1_unsat_core_clauses_time:           0.
% 51.63/6.99  
% 51.63/6.99  ------ Instantiation
% 51.63/6.99  
% 51.63/6.99  inst_num_of_clauses:                    5429
% 51.63/6.99  inst_num_in_passive:                    3478
% 51.63/6.99  inst_num_in_active:                     3700
% 51.63/6.99  inst_num_in_unprocessed:                0
% 51.63/6.99  inst_num_of_loops:                      5119
% 51.63/6.99  inst_num_of_learning_restarts:          1
% 51.63/6.99  inst_num_moves_active_passive:          1413
% 51.63/6.99  inst_lit_activity:                      0
% 51.63/6.99  inst_lit_activity_moves:                1
% 51.63/6.99  inst_num_tautologies:                   0
% 51.63/6.99  inst_num_prop_implied:                  0
% 51.63/6.99  inst_num_existing_simplified:           0
% 51.63/6.99  inst_num_eq_res_simplified:             0
% 51.63/6.99  inst_num_child_elim:                    0
% 51.63/6.99  inst_num_of_dismatching_blockings:      11195
% 51.63/6.99  inst_num_of_non_proper_insts:           13557
% 51.63/6.99  inst_num_of_duplicates:                 0
% 51.63/6.99  inst_inst_num_from_inst_to_res:         0
% 51.63/6.99  inst_dismatching_checking_time:         0.
% 51.63/6.99  
% 51.63/6.99  ------ Resolution
% 51.63/6.99  
% 51.63/6.99  res_num_of_clauses:                     49
% 51.63/6.99  res_num_in_passive:                     49
% 51.63/6.99  res_num_in_active:                      0
% 51.63/6.99  res_num_of_loops:                       174
% 51.63/6.99  res_forward_subset_subsumed:            360
% 51.63/6.99  res_backward_subset_subsumed:           0
% 51.63/6.99  res_forward_subsumed:                   0
% 51.63/6.99  res_backward_subsumed:                  0
% 51.63/6.99  res_forward_subsumption_resolution:     0
% 51.63/6.99  res_backward_subsumption_resolution:    0
% 51.63/6.99  res_clause_to_clause_subsumption:       55472
% 51.63/6.99  res_orphan_elimination:                 0
% 51.63/6.99  res_tautology_del:                      1564
% 51.63/6.99  res_num_eq_res_simplified:              0
% 51.63/6.99  res_num_sel_changes:                    0
% 51.63/6.99  res_moves_from_active_to_pass:          0
% 51.63/6.99  
% 51.63/6.99  ------ Superposition
% 51.63/6.99  
% 51.63/6.99  sup_time_total:                         0.
% 51.63/6.99  sup_time_generating:                    0.
% 51.63/6.99  sup_time_sim_full:                      0.
% 51.63/6.99  sup_time_sim_immed:                     0.
% 51.63/6.99  
% 51.63/6.99  sup_num_of_clauses:                     14334
% 51.63/6.99  sup_num_in_active:                      939
% 51.63/6.99  sup_num_in_passive:                     13395
% 51.63/6.99  sup_num_of_loops:                       1023
% 51.63/6.99  sup_fw_superposition:                   11269
% 51.63/6.99  sup_bw_superposition:                   6863
% 51.63/6.99  sup_immediate_simplified:               4427
% 51.63/6.99  sup_given_eliminated:                   0
% 51.63/6.99  comparisons_done:                       0
% 51.63/6.99  comparisons_avoided:                    753
% 51.63/6.99  
% 51.63/6.99  ------ Simplifications
% 51.63/6.99  
% 51.63/6.99  
% 51.63/6.99  sim_fw_subset_subsumed:                 534
% 51.63/6.99  sim_bw_subset_subsumed:                 442
% 51.63/6.99  sim_fw_subsumed:                        348
% 51.63/6.99  sim_bw_subsumed:                        60
% 51.63/6.99  sim_fw_subsumption_res:                 0
% 51.63/6.99  sim_bw_subsumption_res:                 0
% 51.63/6.99  sim_tautology_del:                      38
% 51.63/6.99  sim_eq_tautology_del:                   1980
% 51.63/6.99  sim_eq_res_simp:                        1
% 51.63/6.99  sim_fw_demodulated:                     799
% 51.63/6.99  sim_bw_demodulated:                     39
% 51.63/6.99  sim_light_normalised:                   2703
% 51.63/6.99  sim_joinable_taut:                      0
% 51.63/6.99  sim_joinable_simp:                      0
% 51.63/6.99  sim_ac_normalised:                      0
% 51.63/6.99  sim_smt_subsumption:                    0
% 51.63/6.99  
%------------------------------------------------------------------------------
