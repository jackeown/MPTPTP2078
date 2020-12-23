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
% DateTime   : Thu Dec  3 11:52:43 EST 2020

% Result     : Theorem 7.43s
% Output     : CNFRefutation 7.43s
% Verified   : 
% Statistics : Number of formulae       :  147 (1803 expanded)
%              Number of clauses        :   99 ( 599 expanded)
%              Number of leaves         :   15 ( 487 expanded)
%              Depth                    :   25
%              Number of atoms          :  481 (8673 expanded)
%              Number of equality atoms :  273 (3913 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK0(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK0(X0,X1)) = X0
        & v1_funct_1(sK0(X0,X1))
        & v1_relat_1(sK0(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK0(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK0(X0,X1)) = X0
      & v1_funct_1(sK0(X0,X1))
      & v1_relat_1(sK0(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f26])).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X0,X1] : k1_relat_1(sK0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                & k1_relat_1(X0) = k1_relat_1(X1) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                  & k1_relat_1(X0) = k1_relat_1(X1) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
          & ! [X3] :
              ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
              | ~ r2_hidden(X3,X2) )
          & k1_relat_1(X0) = k1_relat_1(X1) )
     => ( k7_relat_1(X0,sK4) != k7_relat_1(X1,sK4)
        & ! [X3] :
            ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,sK4) )
        & k1_relat_1(X0) = k1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( k7_relat_1(sK3,X2) != k7_relat_1(X0,X2)
            & ! [X3] :
                ( k1_funct_1(sK3,X3) = k1_funct_1(X0,X3)
                | ~ r2_hidden(X3,X2) )
            & k1_relat_1(sK3) = k1_relat_1(X0) )
        & v1_funct_1(sK3)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                & k1_relat_1(X0) = k1_relat_1(X1) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(sK2,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(sK2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(sK2) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4)
    & ! [X3] :
        ( k1_funct_1(sK2,X3) = k1_funct_1(sK3,X3)
        | ~ r2_hidden(X3,sK4) )
    & k1_relat_1(sK2) = k1_relat_1(sK3)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f34,f33,f32])).

fof(f55,plain,(
    k1_relat_1(sK2) = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( r1_tarski(X2,k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) )
             => ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) ) )
                & ( ! [X3] :
                      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                      | ~ r2_hidden(X3,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) ) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK1(X0,X1,X2)) != k1_funct_1(X1,sK1(X0,X1,X2))
        & r2_hidden(sK1(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ( k1_funct_1(X0,sK1(X0,X1,X2)) != k1_funct_1(X1,sK1(X0,X1,X2))
                    & r2_hidden(sK1(X0,X1,X2),X2) ) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,X3) = k1_funct_1(sK3,X3)
      | ~ r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | k1_funct_1(X0,sK1(X0,X1,X2)) != k1_funct_1(X1,sK1(X0,X1,X2))
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_11,plain,
    ( v1_relat_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_554,plain,
    ( v1_relat_1(sK0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_560,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9,plain,
    ( k1_relat_1(sK0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_558,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1185,plain,
    ( k1_relat_1(k7_relat_1(sK0(X0,X1),X2)) = X2
    | r1_tarski(X2,X0) != iProver_top
    | v1_relat_1(sK0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_558])).

cnf(c_38,plain,
    ( v1_relat_1(sK0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1477,plain,
    ( r1_tarski(X2,X0) != iProver_top
    | k1_relat_1(k7_relat_1(sK0(X0,X1),X2)) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1185,c_38])).

cnf(c_1478,plain,
    ( k1_relat_1(k7_relat_1(sK0(X0,X1),X2)) = X2
    | r1_tarski(X2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1477])).

cnf(c_1483,plain,
    ( k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(k7_relat_1(X2,X0)))) = k1_relat_1(k7_relat_1(X2,X0))
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_560,c_1478])).

cnf(c_8777,plain,
    ( k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(k7_relat_1(sK0(X2,X3),X0)))) = k1_relat_1(k7_relat_1(sK0(X2,X3),X0)) ),
    inference(superposition,[status(thm)],[c_554,c_1483])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,k1_relat_1(k7_relat_1(X0,k1_relat_1(X1)))) = k7_relat_1(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_564,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1496,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(sK0(X1,X2),k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(sK0(X1,X2)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_564])).

cnf(c_1500,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(sK0(X1,X2),k1_relat_1(X0)))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1496,c_9])).

cnf(c_2064,plain,
    ( k7_relat_1(sK0(X0,X1),k1_relat_1(k7_relat_1(sK0(X2,X3),k1_relat_1(sK0(X0,X1))))) = k7_relat_1(sK0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_554,c_1500])).

cnf(c_2068,plain,
    ( k7_relat_1(sK0(X0,X1),k1_relat_1(k7_relat_1(sK0(X2,X3),X0))) = k7_relat_1(sK0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_2064,c_9])).

cnf(c_8781,plain,
    ( k1_relat_1(k7_relat_1(sK0(X0,X1),X2)) = k1_relat_1(k7_relat_1(sK0(X2,X3),X0)) ),
    inference(light_normalisation,[status(thm)],[c_8777,c_2068])).

cnf(c_8782,plain,
    ( k1_relat_1(k7_relat_1(sK0(X0,X1),X2)) = sP0_iProver_split(X0,X2) ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_8781])).

cnf(c_9041,plain,
    ( k1_relat_1(k7_relat_1(sK0(X0,X1),X2)) = sP0_iProver_split(X2,X0) ),
    inference(light_normalisation,[status(thm)],[c_8777,c_2068,c_8782])).

cnf(c_15702,plain,
    ( r1_tarski(sP0_iProver_split(X0,X1),X0) = iProver_top
    | v1_relat_1(sK0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9041,c_560])).

cnf(c_18898,plain,
    ( r1_tarski(sP0_iProver_split(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_15702])).

cnf(c_5,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_559,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_17,negated_conjecture,
    ( k1_relat_1(sK2) = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1186,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_558])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1255,plain,
    ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1186,c_24])).

cnf(c_1256,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1255])).

cnf(c_1262,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_559,c_1256])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2364,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1262,c_22])).

cnf(c_928,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_559])).

cnf(c_999,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_928,c_24])).

cnf(c_2379,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_999])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | r2_hidden(sK1(X2,X1,X0),X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_552,plain,
    ( k7_relat_1(X0,X1) = k7_relat_1(X2,X1)
    | r1_tarski(X1,k1_relat_1(X2)) != iProver_top
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X1) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_561,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1364,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X3,k1_relat_1(k7_relat_1(X1,X2)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X3)) != iProver_top
    | r2_hidden(sK1(X3,X0,k1_relat_1(k7_relat_1(X1,X2))),X2) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_552,c_561])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_550,plain,
    ( k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9858,plain,
    ( k1_funct_1(sK3,sK1(X0,X1,k1_relat_1(k7_relat_1(X2,sK4)))) = k1_funct_1(sK2,sK1(X0,X1,k1_relat_1(k7_relat_1(X2,sK4))))
    | k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,sK4))) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X2,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(X2,sK4)),k1_relat_1(X1)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X2,sK4)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1364,c_550])).

cnf(c_10491,plain,
    ( k1_funct_1(sK2,sK1(X0,sK3,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK1(X0,sK3,k1_relat_1(k7_relat_1(X1,sK4))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_9858])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10538,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK2,sK1(X0,sK3,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK1(X0,sK3,k1_relat_1(k7_relat_1(X1,sK4))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10491,c_24,c_25])).

cnf(c_10539,plain,
    ( k1_funct_1(sK2,sK1(X0,sK3,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK1(X0,sK3,k1_relat_1(k7_relat_1(X1,sK4))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10538])).

cnf(c_10546,plain,
    ( k1_funct_1(sK3,sK1(sK2,sK3,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK1(sK2,sK3,k1_relat_1(k7_relat_1(sK2,sK4))))
    | k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,sK4))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2379,c_10539])).

cnf(c_1261,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK2))))) = k1_relat_1(k7_relat_1(X0,k1_relat_1(sK2)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_560,c_1256])).

cnf(c_3592,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(sK2))))) = k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_554,c_1261])).

cnf(c_548,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2065,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(sK3)))) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_548,c_1500])).

cnf(c_2067,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(sK2)))) = k7_relat_1(sK3,X0) ),
    inference(light_normalisation,[status(thm)],[c_2065,c_17])).

cnf(c_3595,plain,
    ( k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(sK2))) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_3592,c_2067])).

cnf(c_546,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2066,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(sK2)))) = k7_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_546,c_1500])).

cnf(c_3711,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,X0))) = k7_relat_1(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_3595,c_2066])).

cnf(c_1184,plain,
    ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,X0)))) = k1_relat_1(k7_relat_1(sK3,X0))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_999,c_558])).

cnf(c_1848,plain,
    ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,X0)))) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1184,c_22])).

cnf(c_5562,plain,
    ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_3711,c_1848])).

cnf(c_5707,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) = k7_relat_1(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_5562,c_3711])).

cnf(c_3712,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0))) = k7_relat_1(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_3595,c_2067])).

cnf(c_5710,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,X0))) = k7_relat_1(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_5562,c_3712])).

cnf(c_10561,plain,
    ( k1_funct_1(sK3,sK1(sK2,sK3,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK1(sK2,sK3,k1_relat_1(k7_relat_1(sK2,sK4))))
    | k7_relat_1(sK3,sK4) = k7_relat_1(sK2,sK4)
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10546,c_5707,c_5710])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_23,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_15,negated_conjecture,
    ( k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_221,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_595,plain,
    ( k7_relat_1(sK3,sK4) != X0
    | k7_relat_1(sK2,sK4) != X0
    | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_221])).

cnf(c_617,plain,
    ( k7_relat_1(sK3,sK4) != k7_relat_1(X0,sK4)
    | k7_relat_1(sK2,sK4) != k7_relat_1(X0,sK4)
    | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_595])).

cnf(c_618,plain,
    ( k7_relat_1(sK3,sK4) != k7_relat_1(sK2,sK4)
    | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4)
    | k7_relat_1(sK2,sK4) != k7_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_220,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1798,plain,
    ( k7_relat_1(X0,sK4) = k7_relat_1(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_1799,plain,
    ( k7_relat_1(sK2,sK4) = k7_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1798])).

cnf(c_3911,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK4)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3912,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK4)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3911])).

cnf(c_3914,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3912])).

cnf(c_19240,plain,
    ( k1_funct_1(sK3,sK1(sK2,sK3,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK1(sK2,sK3,k1_relat_1(k7_relat_1(sK2,sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10561,c_22,c_23,c_15,c_618,c_1799,c_3914])).

cnf(c_5712,plain,
    ( k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(sK2))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_5562,c_3595])).

cnf(c_15639,plain,
    ( sP0_iProver_split(k1_relat_1(sK2),X0) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_9041,c_5712])).

cnf(c_19242,plain,
    ( k1_funct_1(sK2,sK1(sK2,sK3,sP0_iProver_split(k1_relat_1(sK2),sK4))) = k1_funct_1(sK3,sK1(sK2,sK3,sP0_iProver_split(k1_relat_1(sK2),sK4))) ),
    inference(demodulation,[status(thm)],[c_19240,c_15639])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X1,sK1(X2,X1,X0)) != k1_funct_1(X2,sK1(X2,X1,X0))
    | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_553,plain,
    ( k1_funct_1(X0,sK1(X1,X0,X2)) != k1_funct_1(X1,sK1(X1,X0,X2))
    | k7_relat_1(X1,X2) = k7_relat_1(X0,X2)
    | r1_tarski(X2,k1_relat_1(X0)) != iProver_top
    | r1_tarski(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_19243,plain,
    ( k7_relat_1(sK3,sP0_iProver_split(k1_relat_1(sK2),sK4)) = k7_relat_1(sK2,sP0_iProver_split(k1_relat_1(sK2),sK4))
    | r1_tarski(sP0_iProver_split(k1_relat_1(sK2),sK4),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(sP0_iProver_split(k1_relat_1(sK2),sK4),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_19242,c_553])).

cnf(c_19244,plain,
    ( k7_relat_1(sK3,sP0_iProver_split(k1_relat_1(sK2),sK4)) = k7_relat_1(sK2,sP0_iProver_split(k1_relat_1(sK2),sK4))
    | r1_tarski(sP0_iProver_split(k1_relat_1(sK2),sK4),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19243,c_17])).

cnf(c_19247,plain,
    ( k7_relat_1(sK3,sP0_iProver_split(k1_relat_1(sK2),sK4)) = k7_relat_1(sK2,sP0_iProver_split(k1_relat_1(sK2),sK4))
    | r1_tarski(sP0_iProver_split(k1_relat_1(sK2),sK4),k1_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19244,c_22,c_23,c_24,c_25])).

cnf(c_19833,plain,
    ( k7_relat_1(sK3,sP0_iProver_split(k1_relat_1(sK2),sK4)) = k7_relat_1(sK2,sP0_iProver_split(k1_relat_1(sK2),sK4)) ),
    inference(superposition,[status(thm)],[c_18898,c_19247])).

cnf(c_15638,plain,
    ( k7_relat_1(X0,sP0_iProver_split(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9041,c_1500])).

cnf(c_20115,plain,
    ( k7_relat_1(sK2,sP0_iProver_split(k1_relat_1(sK2),X0)) = k7_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_546,c_15638])).

cnf(c_20876,plain,
    ( k7_relat_1(sK3,sP0_iProver_split(k1_relat_1(sK2),sK4)) = k7_relat_1(sK2,sK4) ),
    inference(demodulation,[status(thm)],[c_19833,c_20115])).

cnf(c_20114,plain,
    ( k7_relat_1(sK3,sP0_iProver_split(k1_relat_1(sK3),X0)) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_548,c_15638])).

cnf(c_20116,plain,
    ( k7_relat_1(sK3,sP0_iProver_split(k1_relat_1(sK2),X0)) = k7_relat_1(sK3,X0) ),
    inference(light_normalisation,[status(thm)],[c_20114,c_17])).

cnf(c_20895,plain,
    ( k7_relat_1(sK3,sK4) = k7_relat_1(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_20876,c_20116])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20895,c_1799,c_618,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:40:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 7.43/1.43  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.43/1.43  
% 7.43/1.43  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.43/1.43  
% 7.43/1.43  ------  iProver source info
% 7.43/1.43  
% 7.43/1.43  git: date: 2020-06-30 10:37:57 +0100
% 7.43/1.43  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.43/1.43  git: non_committed_changes: false
% 7.43/1.43  git: last_make_outside_of_git: false
% 7.43/1.43  
% 7.43/1.43  ------ 
% 7.43/1.43  
% 7.43/1.43  ------ Input Options
% 7.43/1.43  
% 7.43/1.43  --out_options                           all
% 7.43/1.43  --tptp_safe_out                         true
% 7.43/1.43  --problem_path                          ""
% 7.43/1.43  --include_path                          ""
% 7.43/1.43  --clausifier                            res/vclausify_rel
% 7.43/1.43  --clausifier_options                    ""
% 7.43/1.43  --stdin                                 false
% 7.43/1.43  --stats_out                             all
% 7.43/1.43  
% 7.43/1.43  ------ General Options
% 7.43/1.43  
% 7.43/1.43  --fof                                   false
% 7.43/1.43  --time_out_real                         305.
% 7.43/1.43  --time_out_virtual                      -1.
% 7.43/1.43  --symbol_type_check                     false
% 7.43/1.43  --clausify_out                          false
% 7.43/1.43  --sig_cnt_out                           false
% 7.43/1.43  --trig_cnt_out                          false
% 7.43/1.43  --trig_cnt_out_tolerance                1.
% 7.43/1.43  --trig_cnt_out_sk_spl                   false
% 7.43/1.43  --abstr_cl_out                          false
% 7.43/1.43  
% 7.43/1.43  ------ Global Options
% 7.43/1.43  
% 7.43/1.43  --schedule                              default
% 7.43/1.43  --add_important_lit                     false
% 7.43/1.43  --prop_solver_per_cl                    1000
% 7.43/1.43  --min_unsat_core                        false
% 7.43/1.43  --soft_assumptions                      false
% 7.43/1.43  --soft_lemma_size                       3
% 7.43/1.43  --prop_impl_unit_size                   0
% 7.43/1.43  --prop_impl_unit                        []
% 7.43/1.43  --share_sel_clauses                     true
% 7.43/1.43  --reset_solvers                         false
% 7.43/1.43  --bc_imp_inh                            [conj_cone]
% 7.43/1.43  --conj_cone_tolerance                   3.
% 7.43/1.43  --extra_neg_conj                        none
% 7.43/1.43  --large_theory_mode                     true
% 7.43/1.43  --prolific_symb_bound                   200
% 7.43/1.43  --lt_threshold                          2000
% 7.43/1.43  --clause_weak_htbl                      true
% 7.43/1.43  --gc_record_bc_elim                     false
% 7.43/1.43  
% 7.43/1.43  ------ Preprocessing Options
% 7.43/1.43  
% 7.43/1.43  --preprocessing_flag                    true
% 7.43/1.43  --time_out_prep_mult                    0.1
% 7.43/1.43  --splitting_mode                        input
% 7.43/1.43  --splitting_grd                         true
% 7.43/1.43  --splitting_cvd                         false
% 7.43/1.43  --splitting_cvd_svl                     false
% 7.43/1.43  --splitting_nvd                         32
% 7.43/1.43  --sub_typing                            true
% 7.43/1.43  --prep_gs_sim                           true
% 7.43/1.43  --prep_unflatten                        true
% 7.43/1.43  --prep_res_sim                          true
% 7.43/1.43  --prep_upred                            true
% 7.43/1.43  --prep_sem_filter                       exhaustive
% 7.43/1.43  --prep_sem_filter_out                   false
% 7.43/1.43  --pred_elim                             true
% 7.43/1.43  --res_sim_input                         true
% 7.43/1.43  --eq_ax_congr_red                       true
% 7.43/1.43  --pure_diseq_elim                       true
% 7.43/1.43  --brand_transform                       false
% 7.43/1.43  --non_eq_to_eq                          false
% 7.43/1.43  --prep_def_merge                        true
% 7.43/1.43  --prep_def_merge_prop_impl              false
% 7.43/1.43  --prep_def_merge_mbd                    true
% 7.43/1.43  --prep_def_merge_tr_red                 false
% 7.43/1.43  --prep_def_merge_tr_cl                  false
% 7.43/1.43  --smt_preprocessing                     true
% 7.43/1.43  --smt_ac_axioms                         fast
% 7.43/1.43  --preprocessed_out                      false
% 7.43/1.43  --preprocessed_stats                    false
% 7.43/1.43  
% 7.43/1.43  ------ Abstraction refinement Options
% 7.43/1.43  
% 7.43/1.43  --abstr_ref                             []
% 7.43/1.43  --abstr_ref_prep                        false
% 7.43/1.43  --abstr_ref_until_sat                   false
% 7.43/1.43  --abstr_ref_sig_restrict                funpre
% 7.43/1.43  --abstr_ref_af_restrict_to_split_sk     false
% 7.43/1.43  --abstr_ref_under                       []
% 7.43/1.43  
% 7.43/1.43  ------ SAT Options
% 7.43/1.43  
% 7.43/1.43  --sat_mode                              false
% 7.43/1.43  --sat_fm_restart_options                ""
% 7.43/1.43  --sat_gr_def                            false
% 7.43/1.43  --sat_epr_types                         true
% 7.43/1.43  --sat_non_cyclic_types                  false
% 7.43/1.43  --sat_finite_models                     false
% 7.43/1.43  --sat_fm_lemmas                         false
% 7.43/1.43  --sat_fm_prep                           false
% 7.43/1.43  --sat_fm_uc_incr                        true
% 7.43/1.43  --sat_out_model                         small
% 7.43/1.43  --sat_out_clauses                       false
% 7.43/1.43  
% 7.43/1.43  ------ QBF Options
% 7.43/1.43  
% 7.43/1.43  --qbf_mode                              false
% 7.43/1.43  --qbf_elim_univ                         false
% 7.43/1.43  --qbf_dom_inst                          none
% 7.43/1.43  --qbf_dom_pre_inst                      false
% 7.43/1.43  --qbf_sk_in                             false
% 7.43/1.43  --qbf_pred_elim                         true
% 7.43/1.43  --qbf_split                             512
% 7.43/1.43  
% 7.43/1.43  ------ BMC1 Options
% 7.43/1.43  
% 7.43/1.43  --bmc1_incremental                      false
% 7.43/1.43  --bmc1_axioms                           reachable_all
% 7.43/1.43  --bmc1_min_bound                        0
% 7.43/1.43  --bmc1_max_bound                        -1
% 7.43/1.43  --bmc1_max_bound_default                -1
% 7.43/1.43  --bmc1_symbol_reachability              true
% 7.43/1.43  --bmc1_property_lemmas                  false
% 7.43/1.43  --bmc1_k_induction                      false
% 7.43/1.43  --bmc1_non_equiv_states                 false
% 7.43/1.43  --bmc1_deadlock                         false
% 7.43/1.43  --bmc1_ucm                              false
% 7.43/1.43  --bmc1_add_unsat_core                   none
% 7.43/1.43  --bmc1_unsat_core_children              false
% 7.43/1.43  --bmc1_unsat_core_extrapolate_axioms    false
% 7.43/1.43  --bmc1_out_stat                         full
% 7.43/1.43  --bmc1_ground_init                      false
% 7.43/1.43  --bmc1_pre_inst_next_state              false
% 7.43/1.43  --bmc1_pre_inst_state                   false
% 7.43/1.43  --bmc1_pre_inst_reach_state             false
% 7.43/1.43  --bmc1_out_unsat_core                   false
% 7.43/1.43  --bmc1_aig_witness_out                  false
% 7.43/1.43  --bmc1_verbose                          false
% 7.43/1.43  --bmc1_dump_clauses_tptp                false
% 7.43/1.43  --bmc1_dump_unsat_core_tptp             false
% 7.43/1.43  --bmc1_dump_file                        -
% 7.43/1.43  --bmc1_ucm_expand_uc_limit              128
% 7.43/1.43  --bmc1_ucm_n_expand_iterations          6
% 7.43/1.43  --bmc1_ucm_extend_mode                  1
% 7.43/1.43  --bmc1_ucm_init_mode                    2
% 7.43/1.43  --bmc1_ucm_cone_mode                    none
% 7.43/1.43  --bmc1_ucm_reduced_relation_type        0
% 7.43/1.43  --bmc1_ucm_relax_model                  4
% 7.43/1.43  --bmc1_ucm_full_tr_after_sat            true
% 7.43/1.43  --bmc1_ucm_expand_neg_assumptions       false
% 7.43/1.43  --bmc1_ucm_layered_model                none
% 7.43/1.43  --bmc1_ucm_max_lemma_size               10
% 7.43/1.43  
% 7.43/1.43  ------ AIG Options
% 7.43/1.43  
% 7.43/1.43  --aig_mode                              false
% 7.43/1.43  
% 7.43/1.43  ------ Instantiation Options
% 7.43/1.43  
% 7.43/1.43  --instantiation_flag                    true
% 7.43/1.43  --inst_sos_flag                         true
% 7.43/1.43  --inst_sos_phase                        true
% 7.43/1.43  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.43/1.43  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.43/1.43  --inst_lit_sel_side                     num_symb
% 7.43/1.43  --inst_solver_per_active                1400
% 7.43/1.43  --inst_solver_calls_frac                1.
% 7.43/1.43  --inst_passive_queue_type               priority_queues
% 7.43/1.43  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.43/1.43  --inst_passive_queues_freq              [25;2]
% 7.43/1.43  --inst_dismatching                      true
% 7.43/1.43  --inst_eager_unprocessed_to_passive     true
% 7.43/1.43  --inst_prop_sim_given                   true
% 7.43/1.43  --inst_prop_sim_new                     false
% 7.43/1.43  --inst_subs_new                         false
% 7.43/1.43  --inst_eq_res_simp                      false
% 7.43/1.43  --inst_subs_given                       false
% 7.43/1.43  --inst_orphan_elimination               true
% 7.43/1.43  --inst_learning_loop_flag               true
% 7.43/1.43  --inst_learning_start                   3000
% 7.43/1.43  --inst_learning_factor                  2
% 7.43/1.43  --inst_start_prop_sim_after_learn       3
% 7.43/1.43  --inst_sel_renew                        solver
% 7.43/1.43  --inst_lit_activity_flag                true
% 7.43/1.43  --inst_restr_to_given                   false
% 7.43/1.43  --inst_activity_threshold               500
% 7.43/1.43  --inst_out_proof                        true
% 7.43/1.43  
% 7.43/1.43  ------ Resolution Options
% 7.43/1.43  
% 7.43/1.43  --resolution_flag                       true
% 7.43/1.43  --res_lit_sel                           adaptive
% 7.43/1.43  --res_lit_sel_side                      none
% 7.43/1.43  --res_ordering                          kbo
% 7.43/1.43  --res_to_prop_solver                    active
% 7.43/1.43  --res_prop_simpl_new                    false
% 7.43/1.43  --res_prop_simpl_given                  true
% 7.43/1.43  --res_passive_queue_type                priority_queues
% 7.43/1.43  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.43/1.43  --res_passive_queues_freq               [15;5]
% 7.43/1.43  --res_forward_subs                      full
% 7.43/1.43  --res_backward_subs                     full
% 7.43/1.43  --res_forward_subs_resolution           true
% 7.43/1.43  --res_backward_subs_resolution          true
% 7.43/1.43  --res_orphan_elimination                true
% 7.43/1.43  --res_time_limit                        2.
% 7.43/1.43  --res_out_proof                         true
% 7.43/1.43  
% 7.43/1.43  ------ Superposition Options
% 7.43/1.43  
% 7.43/1.43  --superposition_flag                    true
% 7.43/1.43  --sup_passive_queue_type                priority_queues
% 7.43/1.43  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.43/1.43  --sup_passive_queues_freq               [8;1;4]
% 7.43/1.43  --demod_completeness_check              fast
% 7.43/1.43  --demod_use_ground                      true
% 7.43/1.43  --sup_to_prop_solver                    passive
% 7.43/1.43  --sup_prop_simpl_new                    true
% 7.43/1.43  --sup_prop_simpl_given                  true
% 7.43/1.43  --sup_fun_splitting                     true
% 7.43/1.43  --sup_smt_interval                      50000
% 7.43/1.43  
% 7.43/1.43  ------ Superposition Simplification Setup
% 7.43/1.43  
% 7.43/1.43  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.43/1.43  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.43/1.43  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.43/1.43  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.43/1.43  --sup_full_triv                         [TrivRules;PropSubs]
% 7.43/1.43  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.43/1.43  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.43/1.43  --sup_immed_triv                        [TrivRules]
% 7.43/1.43  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.43/1.43  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.43/1.43  --sup_immed_bw_main                     []
% 7.43/1.43  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.43/1.43  --sup_input_triv                        [Unflattening;TrivRules]
% 7.43/1.43  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.43/1.43  --sup_input_bw                          []
% 7.43/1.43  
% 7.43/1.43  ------ Combination Options
% 7.43/1.43  
% 7.43/1.43  --comb_res_mult                         3
% 7.43/1.43  --comb_sup_mult                         2
% 7.43/1.43  --comb_inst_mult                        10
% 7.43/1.43  
% 7.43/1.43  ------ Debug Options
% 7.43/1.43  
% 7.43/1.43  --dbg_backtrace                         false
% 7.43/1.43  --dbg_dump_prop_clauses                 false
% 7.43/1.43  --dbg_dump_prop_clauses_file            -
% 7.43/1.43  --dbg_out_stat                          false
% 7.43/1.43  ------ Parsing...
% 7.43/1.43  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.43/1.43  
% 7.43/1.43  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.43/1.43  
% 7.43/1.43  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.43/1.43  
% 7.43/1.43  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.43/1.43  ------ Proving...
% 7.43/1.43  ------ Problem Properties 
% 7.43/1.43  
% 7.43/1.43  
% 7.43/1.43  clauses                                 22
% 7.43/1.43  conjectures                             7
% 7.43/1.43  EPR                                     4
% 7.43/1.43  Horn                                    21
% 7.43/1.43  unary                                   9
% 7.43/1.43  binary                                  4
% 7.43/1.43  lits                                    61
% 7.43/1.43  lits eq                                 13
% 7.43/1.43  fd_pure                                 0
% 7.43/1.43  fd_pseudo                               0
% 7.43/1.43  fd_cond                                 0
% 7.43/1.43  fd_pseudo_cond                          0
% 7.43/1.43  AC symbols                              0
% 7.43/1.43  
% 7.43/1.43  ------ Schedule dynamic 5 is on 
% 7.43/1.43  
% 7.43/1.43  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.43/1.43  
% 7.43/1.43  
% 7.43/1.43  ------ 
% 7.43/1.43  Current options:
% 7.43/1.43  ------ 
% 7.43/1.43  
% 7.43/1.43  ------ Input Options
% 7.43/1.43  
% 7.43/1.43  --out_options                           all
% 7.43/1.43  --tptp_safe_out                         true
% 7.43/1.43  --problem_path                          ""
% 7.43/1.43  --include_path                          ""
% 7.43/1.43  --clausifier                            res/vclausify_rel
% 7.43/1.43  --clausifier_options                    ""
% 7.43/1.43  --stdin                                 false
% 7.43/1.43  --stats_out                             all
% 7.43/1.43  
% 7.43/1.43  ------ General Options
% 7.43/1.43  
% 7.43/1.43  --fof                                   false
% 7.43/1.43  --time_out_real                         305.
% 7.43/1.43  --time_out_virtual                      -1.
% 7.43/1.43  --symbol_type_check                     false
% 7.43/1.43  --clausify_out                          false
% 7.43/1.43  --sig_cnt_out                           false
% 7.43/1.43  --trig_cnt_out                          false
% 7.43/1.43  --trig_cnt_out_tolerance                1.
% 7.43/1.43  --trig_cnt_out_sk_spl                   false
% 7.43/1.43  --abstr_cl_out                          false
% 7.43/1.43  
% 7.43/1.43  ------ Global Options
% 7.43/1.43  
% 7.43/1.43  --schedule                              default
% 7.43/1.43  --add_important_lit                     false
% 7.43/1.43  --prop_solver_per_cl                    1000
% 7.43/1.43  --min_unsat_core                        false
% 7.43/1.43  --soft_assumptions                      false
% 7.43/1.43  --soft_lemma_size                       3
% 7.43/1.43  --prop_impl_unit_size                   0
% 7.43/1.43  --prop_impl_unit                        []
% 7.43/1.43  --share_sel_clauses                     true
% 7.43/1.43  --reset_solvers                         false
% 7.43/1.43  --bc_imp_inh                            [conj_cone]
% 7.43/1.43  --conj_cone_tolerance                   3.
% 7.43/1.43  --extra_neg_conj                        none
% 7.43/1.43  --large_theory_mode                     true
% 7.43/1.43  --prolific_symb_bound                   200
% 7.43/1.43  --lt_threshold                          2000
% 7.43/1.43  --clause_weak_htbl                      true
% 7.43/1.43  --gc_record_bc_elim                     false
% 7.43/1.43  
% 7.43/1.43  ------ Preprocessing Options
% 7.43/1.43  
% 7.43/1.43  --preprocessing_flag                    true
% 7.43/1.43  --time_out_prep_mult                    0.1
% 7.43/1.43  --splitting_mode                        input
% 7.43/1.43  --splitting_grd                         true
% 7.43/1.43  --splitting_cvd                         false
% 7.43/1.43  --splitting_cvd_svl                     false
% 7.43/1.43  --splitting_nvd                         32
% 7.43/1.43  --sub_typing                            true
% 7.43/1.43  --prep_gs_sim                           true
% 7.43/1.43  --prep_unflatten                        true
% 7.43/1.43  --prep_res_sim                          true
% 7.43/1.43  --prep_upred                            true
% 7.43/1.43  --prep_sem_filter                       exhaustive
% 7.43/1.43  --prep_sem_filter_out                   false
% 7.43/1.43  --pred_elim                             true
% 7.43/1.43  --res_sim_input                         true
% 7.43/1.43  --eq_ax_congr_red                       true
% 7.43/1.43  --pure_diseq_elim                       true
% 7.43/1.43  --brand_transform                       false
% 7.43/1.43  --non_eq_to_eq                          false
% 7.43/1.43  --prep_def_merge                        true
% 7.43/1.43  --prep_def_merge_prop_impl              false
% 7.43/1.43  --prep_def_merge_mbd                    true
% 7.43/1.43  --prep_def_merge_tr_red                 false
% 7.43/1.43  --prep_def_merge_tr_cl                  false
% 7.43/1.43  --smt_preprocessing                     true
% 7.43/1.43  --smt_ac_axioms                         fast
% 7.43/1.43  --preprocessed_out                      false
% 7.43/1.43  --preprocessed_stats                    false
% 7.43/1.43  
% 7.43/1.43  ------ Abstraction refinement Options
% 7.43/1.43  
% 7.43/1.43  --abstr_ref                             []
% 7.43/1.43  --abstr_ref_prep                        false
% 7.43/1.43  --abstr_ref_until_sat                   false
% 7.43/1.43  --abstr_ref_sig_restrict                funpre
% 7.43/1.43  --abstr_ref_af_restrict_to_split_sk     false
% 7.43/1.43  --abstr_ref_under                       []
% 7.43/1.43  
% 7.43/1.43  ------ SAT Options
% 7.43/1.43  
% 7.43/1.43  --sat_mode                              false
% 7.43/1.43  --sat_fm_restart_options                ""
% 7.43/1.43  --sat_gr_def                            false
% 7.43/1.43  --sat_epr_types                         true
% 7.43/1.43  --sat_non_cyclic_types                  false
% 7.43/1.43  --sat_finite_models                     false
% 7.43/1.43  --sat_fm_lemmas                         false
% 7.43/1.43  --sat_fm_prep                           false
% 7.43/1.43  --sat_fm_uc_incr                        true
% 7.43/1.43  --sat_out_model                         small
% 7.43/1.43  --sat_out_clauses                       false
% 7.43/1.43  
% 7.43/1.43  ------ QBF Options
% 7.43/1.43  
% 7.43/1.43  --qbf_mode                              false
% 7.43/1.43  --qbf_elim_univ                         false
% 7.43/1.43  --qbf_dom_inst                          none
% 7.43/1.43  --qbf_dom_pre_inst                      false
% 7.43/1.43  --qbf_sk_in                             false
% 7.43/1.43  --qbf_pred_elim                         true
% 7.43/1.43  --qbf_split                             512
% 7.43/1.43  
% 7.43/1.43  ------ BMC1 Options
% 7.43/1.43  
% 7.43/1.43  --bmc1_incremental                      false
% 7.43/1.43  --bmc1_axioms                           reachable_all
% 7.43/1.43  --bmc1_min_bound                        0
% 7.43/1.43  --bmc1_max_bound                        -1
% 7.43/1.43  --bmc1_max_bound_default                -1
% 7.43/1.43  --bmc1_symbol_reachability              true
% 7.43/1.43  --bmc1_property_lemmas                  false
% 7.43/1.43  --bmc1_k_induction                      false
% 7.43/1.43  --bmc1_non_equiv_states                 false
% 7.43/1.43  --bmc1_deadlock                         false
% 7.43/1.43  --bmc1_ucm                              false
% 7.43/1.43  --bmc1_add_unsat_core                   none
% 7.43/1.43  --bmc1_unsat_core_children              false
% 7.43/1.43  --bmc1_unsat_core_extrapolate_axioms    false
% 7.43/1.43  --bmc1_out_stat                         full
% 7.43/1.43  --bmc1_ground_init                      false
% 7.43/1.43  --bmc1_pre_inst_next_state              false
% 7.43/1.43  --bmc1_pre_inst_state                   false
% 7.43/1.43  --bmc1_pre_inst_reach_state             false
% 7.43/1.43  --bmc1_out_unsat_core                   false
% 7.43/1.43  --bmc1_aig_witness_out                  false
% 7.43/1.43  --bmc1_verbose                          false
% 7.43/1.43  --bmc1_dump_clauses_tptp                false
% 7.43/1.43  --bmc1_dump_unsat_core_tptp             false
% 7.43/1.43  --bmc1_dump_file                        -
% 7.43/1.43  --bmc1_ucm_expand_uc_limit              128
% 7.43/1.43  --bmc1_ucm_n_expand_iterations          6
% 7.43/1.43  --bmc1_ucm_extend_mode                  1
% 7.43/1.43  --bmc1_ucm_init_mode                    2
% 7.43/1.43  --bmc1_ucm_cone_mode                    none
% 7.43/1.43  --bmc1_ucm_reduced_relation_type        0
% 7.43/1.43  --bmc1_ucm_relax_model                  4
% 7.43/1.43  --bmc1_ucm_full_tr_after_sat            true
% 7.43/1.43  --bmc1_ucm_expand_neg_assumptions       false
% 7.43/1.43  --bmc1_ucm_layered_model                none
% 7.43/1.43  --bmc1_ucm_max_lemma_size               10
% 7.43/1.43  
% 7.43/1.43  ------ AIG Options
% 7.43/1.43  
% 7.43/1.43  --aig_mode                              false
% 7.43/1.43  
% 7.43/1.43  ------ Instantiation Options
% 7.43/1.43  
% 7.43/1.43  --instantiation_flag                    true
% 7.43/1.43  --inst_sos_flag                         true
% 7.43/1.43  --inst_sos_phase                        true
% 7.43/1.43  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.43/1.43  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.43/1.43  --inst_lit_sel_side                     none
% 7.43/1.43  --inst_solver_per_active                1400
% 7.43/1.43  --inst_solver_calls_frac                1.
% 7.43/1.43  --inst_passive_queue_type               priority_queues
% 7.43/1.43  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.43/1.43  --inst_passive_queues_freq              [25;2]
% 7.43/1.43  --inst_dismatching                      true
% 7.43/1.43  --inst_eager_unprocessed_to_passive     true
% 7.43/1.43  --inst_prop_sim_given                   true
% 7.43/1.43  --inst_prop_sim_new                     false
% 7.43/1.43  --inst_subs_new                         false
% 7.43/1.43  --inst_eq_res_simp                      false
% 7.43/1.43  --inst_subs_given                       false
% 7.43/1.43  --inst_orphan_elimination               true
% 7.43/1.43  --inst_learning_loop_flag               true
% 7.43/1.43  --inst_learning_start                   3000
% 7.43/1.43  --inst_learning_factor                  2
% 7.43/1.43  --inst_start_prop_sim_after_learn       3
% 7.43/1.43  --inst_sel_renew                        solver
% 7.43/1.43  --inst_lit_activity_flag                true
% 7.43/1.43  --inst_restr_to_given                   false
% 7.43/1.43  --inst_activity_threshold               500
% 7.43/1.43  --inst_out_proof                        true
% 7.43/1.43  
% 7.43/1.43  ------ Resolution Options
% 7.43/1.43  
% 7.43/1.43  --resolution_flag                       false
% 7.43/1.43  --res_lit_sel                           adaptive
% 7.43/1.43  --res_lit_sel_side                      none
% 7.43/1.43  --res_ordering                          kbo
% 7.43/1.43  --res_to_prop_solver                    active
% 7.43/1.43  --res_prop_simpl_new                    false
% 7.43/1.43  --res_prop_simpl_given                  true
% 7.43/1.43  --res_passive_queue_type                priority_queues
% 7.43/1.43  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.43/1.43  --res_passive_queues_freq               [15;5]
% 7.43/1.43  --res_forward_subs                      full
% 7.43/1.43  --res_backward_subs                     full
% 7.43/1.43  --res_forward_subs_resolution           true
% 7.43/1.43  --res_backward_subs_resolution          true
% 7.43/1.43  --res_orphan_elimination                true
% 7.43/1.43  --res_time_limit                        2.
% 7.43/1.43  --res_out_proof                         true
% 7.43/1.43  
% 7.43/1.43  ------ Superposition Options
% 7.43/1.43  
% 7.43/1.43  --superposition_flag                    true
% 7.43/1.43  --sup_passive_queue_type                priority_queues
% 7.43/1.43  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.43/1.43  --sup_passive_queues_freq               [8;1;4]
% 7.43/1.43  --demod_completeness_check              fast
% 7.43/1.43  --demod_use_ground                      true
% 7.43/1.43  --sup_to_prop_solver                    passive
% 7.43/1.43  --sup_prop_simpl_new                    true
% 7.43/1.43  --sup_prop_simpl_given                  true
% 7.43/1.43  --sup_fun_splitting                     true
% 7.43/1.43  --sup_smt_interval                      50000
% 7.43/1.43  
% 7.43/1.43  ------ Superposition Simplification Setup
% 7.43/1.43  
% 7.43/1.43  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.43/1.43  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.43/1.43  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.43/1.43  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.43/1.43  --sup_full_triv                         [TrivRules;PropSubs]
% 7.43/1.43  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.43/1.43  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.43/1.43  --sup_immed_triv                        [TrivRules]
% 7.43/1.43  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.43/1.43  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.43/1.43  --sup_immed_bw_main                     []
% 7.43/1.43  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.43/1.43  --sup_input_triv                        [Unflattening;TrivRules]
% 7.43/1.43  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.43/1.43  --sup_input_bw                          []
% 7.43/1.43  
% 7.43/1.43  ------ Combination Options
% 7.43/1.43  
% 7.43/1.43  --comb_res_mult                         3
% 7.43/1.43  --comb_sup_mult                         2
% 7.43/1.43  --comb_inst_mult                        10
% 7.43/1.43  
% 7.43/1.43  ------ Debug Options
% 7.43/1.43  
% 7.43/1.43  --dbg_backtrace                         false
% 7.43/1.43  --dbg_dump_prop_clauses                 false
% 7.43/1.43  --dbg_dump_prop_clauses_file            -
% 7.43/1.43  --dbg_out_stat                          false
% 7.43/1.43  
% 7.43/1.43  
% 7.43/1.43  
% 7.43/1.43  
% 7.43/1.43  ------ Proving...
% 7.43/1.43  
% 7.43/1.43  
% 7.43/1.43  % SZS status Theorem for theBenchmark.p
% 7.43/1.43  
% 7.43/1.43  % SZS output start CNFRefutation for theBenchmark.p
% 7.43/1.43  
% 7.43/1.43  fof(f7,axiom,(
% 7.43/1.43    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.43/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.43  
% 7.43/1.43  fof(f19,plain,(
% 7.43/1.43    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.43/1.43    inference(ennf_transformation,[],[f7])).
% 7.43/1.43  
% 7.43/1.43  fof(f26,plain,(
% 7.43/1.43    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK0(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK0(X0,X1)) = X0 & v1_funct_1(sK0(X0,X1)) & v1_relat_1(sK0(X0,X1))))),
% 7.43/1.43    introduced(choice_axiom,[])).
% 7.43/1.43  
% 7.43/1.43  fof(f27,plain,(
% 7.43/1.43    ! [X0,X1] : (! [X3] : (k1_funct_1(sK0(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK0(X0,X1)) = X0 & v1_funct_1(sK0(X0,X1)) & v1_relat_1(sK0(X0,X1)))),
% 7.43/1.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f26])).
% 7.43/1.43  
% 7.43/1.43  fof(f44,plain,(
% 7.43/1.43    ( ! [X0,X1] : (v1_relat_1(sK0(X0,X1))) )),
% 7.43/1.43    inference(cnf_transformation,[],[f27])).
% 7.43/1.43  
% 7.43/1.43  fof(f3,axiom,(
% 7.43/1.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 7.43/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.43  
% 7.43/1.43  fof(f13,plain,(
% 7.43/1.43    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 7.43/1.43    inference(ennf_transformation,[],[f3])).
% 7.43/1.43  
% 7.43/1.43  fof(f40,plain,(
% 7.43/1.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 7.43/1.43    inference(cnf_transformation,[],[f13])).
% 7.43/1.43  
% 7.43/1.43  fof(f46,plain,(
% 7.43/1.43    ( ! [X0,X1] : (k1_relat_1(sK0(X0,X1)) = X0) )),
% 7.43/1.43    inference(cnf_transformation,[],[f27])).
% 7.43/1.43  
% 7.43/1.43  fof(f5,axiom,(
% 7.43/1.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.43/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.43  
% 7.43/1.43  fof(f15,plain,(
% 7.43/1.43    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.43/1.43    inference(ennf_transformation,[],[f5])).
% 7.43/1.43  
% 7.43/1.43  fof(f16,plain,(
% 7.43/1.43    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.43/1.43    inference(flattening,[],[f15])).
% 7.43/1.43  
% 7.43/1.43  fof(f42,plain,(
% 7.43/1.43    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.43/1.43    inference(cnf_transformation,[],[f16])).
% 7.43/1.43  
% 7.43/1.43  fof(f1,axiom,(
% 7.43/1.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 7.43/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.43  
% 7.43/1.43  fof(f11,plain,(
% 7.43/1.43    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.43/1.43    inference(ennf_transformation,[],[f1])).
% 7.43/1.43  
% 7.43/1.43  fof(f36,plain,(
% 7.43/1.43    ( ! [X0,X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.43/1.43    inference(cnf_transformation,[],[f11])).
% 7.43/1.43  
% 7.43/1.43  fof(f4,axiom,(
% 7.43/1.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 7.43/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.43  
% 7.43/1.43  fof(f14,plain,(
% 7.43/1.43    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.43/1.43    inference(ennf_transformation,[],[f4])).
% 7.43/1.43  
% 7.43/1.43  fof(f41,plain,(
% 7.43/1.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.43/1.43    inference(cnf_transformation,[],[f14])).
% 7.43/1.43  
% 7.43/1.43  fof(f9,conjecture,(
% 7.43/1.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X0) = k1_relat_1(X1)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 7.43/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.43  
% 7.43/1.43  fof(f10,negated_conjecture,(
% 7.43/1.43    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X0) = k1_relat_1(X1)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 7.43/1.43    inference(negated_conjecture,[],[f9])).
% 7.43/1.43  
% 7.43/1.43  fof(f22,plain,(
% 7.43/1.43    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 7.43/1.43    inference(ennf_transformation,[],[f10])).
% 7.43/1.43  
% 7.43/1.43  fof(f23,plain,(
% 7.43/1.43    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.43/1.43    inference(flattening,[],[f22])).
% 7.43/1.43  
% 7.43/1.43  fof(f34,plain,(
% 7.43/1.43    ( ! [X0,X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => (k7_relat_1(X0,sK4) != k7_relat_1(X1,sK4) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,sK4)) & k1_relat_1(X0) = k1_relat_1(X1))) )),
% 7.43/1.43    introduced(choice_axiom,[])).
% 7.43/1.43  
% 7.43/1.43  fof(f33,plain,(
% 7.43/1.43    ( ! [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK3,X2) != k7_relat_1(X0,X2) & ! [X3] : (k1_funct_1(sK3,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK3) = k1_relat_1(X0)) & v1_funct_1(sK3) & v1_relat_1(sK3))) )),
% 7.43/1.43    introduced(choice_axiom,[])).
% 7.43/1.43  
% 7.43/1.43  fof(f32,plain,(
% 7.43/1.43    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(sK2,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(sK2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK2) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 7.43/1.43    introduced(choice_axiom,[])).
% 7.43/1.43  
% 7.43/1.43  fof(f35,plain,(
% 7.43/1.43    ((k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4) & ! [X3] : (k1_funct_1(sK2,X3) = k1_funct_1(sK3,X3) | ~r2_hidden(X3,sK4)) & k1_relat_1(sK2) = k1_relat_1(sK3)) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 7.43/1.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f34,f33,f32])).
% 7.43/1.43  
% 7.43/1.43  fof(f55,plain,(
% 7.43/1.43    k1_relat_1(sK2) = k1_relat_1(sK3)),
% 7.43/1.43    inference(cnf_transformation,[],[f35])).
% 7.43/1.43  
% 7.43/1.43  fof(f53,plain,(
% 7.43/1.43    v1_relat_1(sK3)),
% 7.43/1.43    inference(cnf_transformation,[],[f35])).
% 7.43/1.43  
% 7.43/1.43  fof(f51,plain,(
% 7.43/1.43    v1_relat_1(sK2)),
% 7.43/1.43    inference(cnf_transformation,[],[f35])).
% 7.43/1.43  
% 7.43/1.43  fof(f8,axiom,(
% 7.43/1.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 7.43/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.43  
% 7.43/1.43  fof(f20,plain,(
% 7.43/1.43    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | (~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.43/1.43    inference(ennf_transformation,[],[f8])).
% 7.43/1.43  
% 7.43/1.43  fof(f21,plain,(
% 7.43/1.43    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.43/1.43    inference(flattening,[],[f20])).
% 7.43/1.43  
% 7.43/1.43  fof(f28,plain,(
% 7.43/1.43    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.43/1.43    inference(nnf_transformation,[],[f21])).
% 7.43/1.43  
% 7.43/1.43  fof(f29,plain,(
% 7.43/1.43    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.43/1.43    inference(rectify,[],[f28])).
% 7.43/1.43  
% 7.43/1.43  fof(f30,plain,(
% 7.43/1.43    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK1(X0,X1,X2)) != k1_funct_1(X1,sK1(X0,X1,X2)) & r2_hidden(sK1(X0,X1,X2),X2)))),
% 7.43/1.43    introduced(choice_axiom,[])).
% 7.43/1.43  
% 7.43/1.43  fof(f31,plain,(
% 7.43/1.43    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | (k1_funct_1(X0,sK1(X0,X1,X2)) != k1_funct_1(X1,sK1(X0,X1,X2)) & r2_hidden(sK1(X0,X1,X2),X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.43/1.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 7.43/1.43  
% 7.43/1.43  fof(f49,plain,(
% 7.43/1.43    ( ! [X2,X0,X1] : (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.43/1.43    inference(cnf_transformation,[],[f31])).
% 7.43/1.43  
% 7.43/1.43  fof(f2,axiom,(
% 7.43/1.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 7.43/1.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.43/1.43  
% 7.43/1.43  fof(f12,plain,(
% 7.43/1.43    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 7.43/1.43    inference(ennf_transformation,[],[f2])).
% 7.43/1.43  
% 7.43/1.43  fof(f24,plain,(
% 7.43/1.43    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 7.43/1.43    inference(nnf_transformation,[],[f12])).
% 7.43/1.43  
% 7.43/1.43  fof(f25,plain,(
% 7.43/1.43    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 7.43/1.43    inference(flattening,[],[f24])).
% 7.43/1.43  
% 7.43/1.43  fof(f37,plain,(
% 7.43/1.43    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 7.43/1.43    inference(cnf_transformation,[],[f25])).
% 7.43/1.43  
% 7.43/1.43  fof(f56,plain,(
% 7.43/1.43    ( ! [X3] : (k1_funct_1(sK2,X3) = k1_funct_1(sK3,X3) | ~r2_hidden(X3,sK4)) )),
% 7.43/1.43    inference(cnf_transformation,[],[f35])).
% 7.43/1.43  
% 7.43/1.43  fof(f54,plain,(
% 7.43/1.43    v1_funct_1(sK3)),
% 7.43/1.43    inference(cnf_transformation,[],[f35])).
% 7.43/1.43  
% 7.43/1.43  fof(f52,plain,(
% 7.43/1.43    v1_funct_1(sK2)),
% 7.43/1.43    inference(cnf_transformation,[],[f35])).
% 7.43/1.43  
% 7.43/1.43  fof(f57,plain,(
% 7.43/1.43    k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4)),
% 7.43/1.43    inference(cnf_transformation,[],[f35])).
% 7.43/1.43  
% 7.43/1.43  fof(f50,plain,(
% 7.43/1.43    ( ! [X2,X0,X1] : (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | k1_funct_1(X0,sK1(X0,X1,X2)) != k1_funct_1(X1,sK1(X0,X1,X2)) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.43/1.43    inference(cnf_transformation,[],[f31])).
% 7.43/1.43  
% 7.43/1.43  cnf(c_11,plain,
% 7.43/1.43      ( v1_relat_1(sK0(X0,X1)) ),
% 7.43/1.43      inference(cnf_transformation,[],[f44]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_554,plain,
% 7.43/1.43      ( v1_relat_1(sK0(X0,X1)) = iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_4,plain,
% 7.43/1.43      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 7.43/1.43      inference(cnf_transformation,[],[f40]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_560,plain,
% 7.43/1.43      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 7.43/1.43      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_9,plain,
% 7.43/1.43      ( k1_relat_1(sK0(X0,X1)) = X0 ),
% 7.43/1.43      inference(cnf_transformation,[],[f46]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_6,plain,
% 7.43/1.43      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.43/1.43      | ~ v1_relat_1(X1)
% 7.43/1.43      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 7.43/1.43      inference(cnf_transformation,[],[f42]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_558,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 7.43/1.43      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.43/1.43      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_1185,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK0(X0,X1),X2)) = X2
% 7.43/1.43      | r1_tarski(X2,X0) != iProver_top
% 7.43/1.43      | v1_relat_1(sK0(X0,X1)) != iProver_top ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_9,c_558]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_38,plain,
% 7.43/1.43      ( v1_relat_1(sK0(X0,X1)) = iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_1477,plain,
% 7.43/1.43      ( r1_tarski(X2,X0) != iProver_top
% 7.43/1.43      | k1_relat_1(k7_relat_1(sK0(X0,X1),X2)) = X2 ),
% 7.43/1.43      inference(global_propositional_subsumption,
% 7.43/1.43                [status(thm)],
% 7.43/1.43                [c_1185,c_38]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_1478,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK0(X0,X1),X2)) = X2
% 7.43/1.43      | r1_tarski(X2,X0) != iProver_top ),
% 7.43/1.43      inference(renaming,[status(thm)],[c_1477]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_1483,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(k7_relat_1(X2,X0)))) = k1_relat_1(k7_relat_1(X2,X0))
% 7.43/1.43      | v1_relat_1(X2) != iProver_top ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_560,c_1478]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_8777,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(k7_relat_1(sK0(X2,X3),X0)))) = k1_relat_1(k7_relat_1(sK0(X2,X3),X0)) ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_554,c_1483]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_0,plain,
% 7.43/1.43      ( ~ v1_relat_1(X0)
% 7.43/1.43      | ~ v1_relat_1(X1)
% 7.43/1.43      | k7_relat_1(X1,k1_relat_1(k7_relat_1(X0,k1_relat_1(X1)))) = k7_relat_1(X1,k1_relat_1(X0)) ),
% 7.43/1.43      inference(cnf_transformation,[],[f36]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_564,plain,
% 7.43/1.43      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1))
% 7.43/1.43      | v1_relat_1(X0) != iProver_top
% 7.43/1.43      | v1_relat_1(X1) != iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_1496,plain,
% 7.43/1.43      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(sK0(X1,X2),k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(sK0(X1,X2)))
% 7.43/1.43      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_554,c_564]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_1500,plain,
% 7.43/1.43      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(sK0(X1,X2),k1_relat_1(X0)))) = k7_relat_1(X0,X1)
% 7.43/1.43      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.43      inference(demodulation,[status(thm)],[c_1496,c_9]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_2064,plain,
% 7.43/1.43      ( k7_relat_1(sK0(X0,X1),k1_relat_1(k7_relat_1(sK0(X2,X3),k1_relat_1(sK0(X0,X1))))) = k7_relat_1(sK0(X0,X1),X2) ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_554,c_1500]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_2068,plain,
% 7.43/1.43      ( k7_relat_1(sK0(X0,X1),k1_relat_1(k7_relat_1(sK0(X2,X3),X0))) = k7_relat_1(sK0(X0,X1),X2) ),
% 7.43/1.43      inference(light_normalisation,[status(thm)],[c_2064,c_9]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_8781,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK0(X0,X1),X2)) = k1_relat_1(k7_relat_1(sK0(X2,X3),X0)) ),
% 7.43/1.43      inference(light_normalisation,[status(thm)],[c_8777,c_2068]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_8782,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK0(X0,X1),X2)) = sP0_iProver_split(X0,X2) ),
% 7.43/1.43      inference(splitting,
% 7.43/1.43                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.43/1.43                [c_8781]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_9041,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK0(X0,X1),X2)) = sP0_iProver_split(X2,X0) ),
% 7.43/1.43      inference(light_normalisation,[status(thm)],[c_8777,c_2068,c_8782]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_15702,plain,
% 7.43/1.43      ( r1_tarski(sP0_iProver_split(X0,X1),X0) = iProver_top
% 7.43/1.43      | v1_relat_1(sK0(X1,X2)) != iProver_top ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_9041,c_560]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_18898,plain,
% 7.43/1.43      ( r1_tarski(sP0_iProver_split(X0,X1),X0) = iProver_top ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_554,c_15702]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_5,plain,
% 7.43/1.43      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
% 7.43/1.43      | ~ v1_relat_1(X0) ),
% 7.43/1.43      inference(cnf_transformation,[],[f41]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_559,plain,
% 7.43/1.43      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 7.43/1.43      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_17,negated_conjecture,
% 7.43/1.43      ( k1_relat_1(sK2) = k1_relat_1(sK3) ),
% 7.43/1.43      inference(cnf_transformation,[],[f55]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_1186,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.43/1.43      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 7.43/1.43      | v1_relat_1(sK3) != iProver_top ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_17,c_558]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_19,negated_conjecture,
% 7.43/1.43      ( v1_relat_1(sK3) ),
% 7.43/1.43      inference(cnf_transformation,[],[f53]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_24,plain,
% 7.43/1.43      ( v1_relat_1(sK3) = iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_1255,plain,
% 7.43/1.43      ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 7.43/1.43      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 7.43/1.43      inference(global_propositional_subsumption,
% 7.43/1.43                [status(thm)],
% 7.43/1.43                [c_1186,c_24]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_1256,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.43/1.43      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 7.43/1.43      inference(renaming,[status(thm)],[c_1255]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_1262,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
% 7.43/1.43      | v1_relat_1(sK2) != iProver_top ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_559,c_1256]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_21,negated_conjecture,
% 7.43/1.43      ( v1_relat_1(sK2) ),
% 7.43/1.43      inference(cnf_transformation,[],[f51]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_22,plain,
% 7.43/1.43      ( v1_relat_1(sK2) = iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_2364,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 7.43/1.43      inference(global_propositional_subsumption,
% 7.43/1.43                [status(thm)],
% 7.43/1.43                [c_1262,c_22]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_928,plain,
% 7.43/1.43      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK2)) = iProver_top
% 7.43/1.43      | v1_relat_1(sK3) != iProver_top ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_17,c_559]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_999,plain,
% 7.43/1.43      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK2)) = iProver_top ),
% 7.43/1.43      inference(global_propositional_subsumption,
% 7.43/1.43                [status(thm)],
% 7.43/1.43                [c_928,c_24]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_2379,plain,
% 7.43/1.43      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK2)) = iProver_top ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_2364,c_999]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_13,plain,
% 7.43/1.43      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.43/1.43      | ~ r1_tarski(X0,k1_relat_1(X2))
% 7.43/1.43      | r2_hidden(sK1(X2,X1,X0),X0)
% 7.43/1.43      | ~ v1_funct_1(X1)
% 7.43/1.43      | ~ v1_funct_1(X2)
% 7.43/1.43      | ~ v1_relat_1(X1)
% 7.43/1.43      | ~ v1_relat_1(X2)
% 7.43/1.43      | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
% 7.43/1.43      inference(cnf_transformation,[],[f49]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_552,plain,
% 7.43/1.43      ( k7_relat_1(X0,X1) = k7_relat_1(X2,X1)
% 7.43/1.43      | r1_tarski(X1,k1_relat_1(X2)) != iProver_top
% 7.43/1.43      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.43/1.43      | r2_hidden(sK1(X0,X2,X1),X1) = iProver_top
% 7.43/1.43      | v1_funct_1(X2) != iProver_top
% 7.43/1.43      | v1_funct_1(X0) != iProver_top
% 7.43/1.43      | v1_relat_1(X2) != iProver_top
% 7.43/1.43      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_3,plain,
% 7.43/1.43      ( r2_hidden(X0,X1)
% 7.43/1.43      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 7.43/1.43      | ~ v1_relat_1(X2) ),
% 7.43/1.43      inference(cnf_transformation,[],[f37]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_561,plain,
% 7.43/1.43      ( r2_hidden(X0,X1) = iProver_top
% 7.43/1.43      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
% 7.43/1.43      | v1_relat_1(X2) != iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_1364,plain,
% 7.43/1.43      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X3,k1_relat_1(k7_relat_1(X1,X2)))
% 7.43/1.43      | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X0)) != iProver_top
% 7.43/1.43      | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X3)) != iProver_top
% 7.43/1.43      | r2_hidden(sK1(X3,X0,k1_relat_1(k7_relat_1(X1,X2))),X2) = iProver_top
% 7.43/1.43      | v1_funct_1(X3) != iProver_top
% 7.43/1.43      | v1_funct_1(X0) != iProver_top
% 7.43/1.43      | v1_relat_1(X1) != iProver_top
% 7.43/1.43      | v1_relat_1(X3) != iProver_top
% 7.43/1.43      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_552,c_561]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_16,negated_conjecture,
% 7.43/1.43      ( ~ r2_hidden(X0,sK4) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
% 7.43/1.43      inference(cnf_transformation,[],[f56]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_550,plain,
% 7.43/1.43      ( k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
% 7.43/1.43      | r2_hidden(X0,sK4) != iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_9858,plain,
% 7.43/1.43      ( k1_funct_1(sK3,sK1(X0,X1,k1_relat_1(k7_relat_1(X2,sK4)))) = k1_funct_1(sK2,sK1(X0,X1,k1_relat_1(k7_relat_1(X2,sK4))))
% 7.43/1.43      | k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,sK4))) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X2,sK4)))
% 7.43/1.43      | r1_tarski(k1_relat_1(k7_relat_1(X2,sK4)),k1_relat_1(X1)) != iProver_top
% 7.43/1.43      | r1_tarski(k1_relat_1(k7_relat_1(X2,sK4)),k1_relat_1(X0)) != iProver_top
% 7.43/1.43      | v1_funct_1(X0) != iProver_top
% 7.43/1.43      | v1_funct_1(X1) != iProver_top
% 7.43/1.43      | v1_relat_1(X2) != iProver_top
% 7.43/1.43      | v1_relat_1(X0) != iProver_top
% 7.43/1.43      | v1_relat_1(X1) != iProver_top ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_1364,c_550]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_10491,plain,
% 7.43/1.43      ( k1_funct_1(sK2,sK1(X0,sK3,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK1(X0,sK3,k1_relat_1(k7_relat_1(X1,sK4))))
% 7.43/1.43      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
% 7.43/1.43      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
% 7.43/1.43      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.43/1.43      | v1_funct_1(X0) != iProver_top
% 7.43/1.43      | v1_funct_1(sK3) != iProver_top
% 7.43/1.43      | v1_relat_1(X0) != iProver_top
% 7.43/1.43      | v1_relat_1(X1) != iProver_top
% 7.43/1.43      | v1_relat_1(sK3) != iProver_top ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_17,c_9858]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_18,negated_conjecture,
% 7.43/1.43      ( v1_funct_1(sK3) ),
% 7.43/1.43      inference(cnf_transformation,[],[f54]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_25,plain,
% 7.43/1.43      ( v1_funct_1(sK3) = iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_10538,plain,
% 7.43/1.43      ( v1_relat_1(X1) != iProver_top
% 7.43/1.43      | v1_relat_1(X0) != iProver_top
% 7.43/1.43      | k1_funct_1(sK2,sK1(X0,sK3,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK1(X0,sK3,k1_relat_1(k7_relat_1(X1,sK4))))
% 7.43/1.43      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
% 7.43/1.43      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
% 7.43/1.43      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.43/1.43      | v1_funct_1(X0) != iProver_top ),
% 7.43/1.43      inference(global_propositional_subsumption,
% 7.43/1.43                [status(thm)],
% 7.43/1.43                [c_10491,c_24,c_25]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_10539,plain,
% 7.43/1.43      ( k1_funct_1(sK2,sK1(X0,sK3,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK1(X0,sK3,k1_relat_1(k7_relat_1(X1,sK4))))
% 7.43/1.43      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
% 7.43/1.43      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
% 7.43/1.43      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.43/1.43      | v1_funct_1(X0) != iProver_top
% 7.43/1.43      | v1_relat_1(X1) != iProver_top
% 7.43/1.43      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.43      inference(renaming,[status(thm)],[c_10538]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_10546,plain,
% 7.43/1.43      ( k1_funct_1(sK3,sK1(sK2,sK3,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK1(sK2,sK3,k1_relat_1(k7_relat_1(sK2,sK4))))
% 7.43/1.43      | k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,sK4))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK4)))
% 7.43/1.43      | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.43/1.43      | v1_funct_1(sK2) != iProver_top
% 7.43/1.43      | v1_relat_1(sK2) != iProver_top ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_2379,c_10539]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_1261,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK2))))) = k1_relat_1(k7_relat_1(X0,k1_relat_1(sK2)))
% 7.43/1.43      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_560,c_1256]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_3592,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(sK2))))) = k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(sK2))) ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_554,c_1261]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_548,plain,
% 7.43/1.43      ( v1_relat_1(sK3) = iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_2065,plain,
% 7.43/1.43      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(sK3)))) = k7_relat_1(sK3,X0) ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_548,c_1500]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_2067,plain,
% 7.43/1.43      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(sK2)))) = k7_relat_1(sK3,X0) ),
% 7.43/1.43      inference(light_normalisation,[status(thm)],[c_2065,c_17]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_3595,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(sK2))) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 7.43/1.43      inference(light_normalisation,[status(thm)],[c_3592,c_2067]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_546,plain,
% 7.43/1.43      ( v1_relat_1(sK2) = iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_2066,plain,
% 7.43/1.43      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(sK2)))) = k7_relat_1(sK2,X0) ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_546,c_1500]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_3711,plain,
% 7.43/1.43      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,X0))) = k7_relat_1(sK2,X0) ),
% 7.43/1.43      inference(demodulation,[status(thm)],[c_3595,c_2066]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_1184,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,X0)))) = k1_relat_1(k7_relat_1(sK3,X0))
% 7.43/1.43      | v1_relat_1(sK2) != iProver_top ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_999,c_558]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_1848,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,X0)))) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 7.43/1.43      inference(global_propositional_subsumption,
% 7.43/1.43                [status(thm)],
% 7.43/1.43                [c_1184,c_22]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_5562,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 7.43/1.43      inference(demodulation,[status(thm)],[c_3711,c_1848]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_5707,plain,
% 7.43/1.43      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) = k7_relat_1(sK2,X0) ),
% 7.43/1.43      inference(demodulation,[status(thm)],[c_5562,c_3711]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_3712,plain,
% 7.43/1.43      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0))) = k7_relat_1(sK3,X0) ),
% 7.43/1.43      inference(demodulation,[status(thm)],[c_3595,c_2067]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_5710,plain,
% 7.43/1.43      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,X0))) = k7_relat_1(sK3,X0) ),
% 7.43/1.43      inference(demodulation,[status(thm)],[c_5562,c_3712]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_10561,plain,
% 7.43/1.43      ( k1_funct_1(sK3,sK1(sK2,sK3,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK1(sK2,sK3,k1_relat_1(k7_relat_1(sK2,sK4))))
% 7.43/1.43      | k7_relat_1(sK3,sK4) = k7_relat_1(sK2,sK4)
% 7.43/1.43      | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.43/1.43      | v1_funct_1(sK2) != iProver_top
% 7.43/1.43      | v1_relat_1(sK2) != iProver_top ),
% 7.43/1.43      inference(demodulation,[status(thm)],[c_10546,c_5707,c_5710]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_20,negated_conjecture,
% 7.43/1.43      ( v1_funct_1(sK2) ),
% 7.43/1.43      inference(cnf_transformation,[],[f52]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_23,plain,
% 7.43/1.43      ( v1_funct_1(sK2) = iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_15,negated_conjecture,
% 7.43/1.43      ( k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4) ),
% 7.43/1.43      inference(cnf_transformation,[],[f57]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_221,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_595,plain,
% 7.43/1.43      ( k7_relat_1(sK3,sK4) != X0
% 7.43/1.43      | k7_relat_1(sK2,sK4) != X0
% 7.43/1.43      | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4) ),
% 7.43/1.43      inference(instantiation,[status(thm)],[c_221]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_617,plain,
% 7.43/1.43      ( k7_relat_1(sK3,sK4) != k7_relat_1(X0,sK4)
% 7.43/1.43      | k7_relat_1(sK2,sK4) != k7_relat_1(X0,sK4)
% 7.43/1.43      | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4) ),
% 7.43/1.43      inference(instantiation,[status(thm)],[c_595]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_618,plain,
% 7.43/1.43      ( k7_relat_1(sK3,sK4) != k7_relat_1(sK2,sK4)
% 7.43/1.43      | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4)
% 7.43/1.43      | k7_relat_1(sK2,sK4) != k7_relat_1(sK2,sK4) ),
% 7.43/1.43      inference(instantiation,[status(thm)],[c_617]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_220,plain,( X0 = X0 ),theory(equality) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_1798,plain,
% 7.43/1.43      ( k7_relat_1(X0,sK4) = k7_relat_1(X0,sK4) ),
% 7.43/1.43      inference(instantiation,[status(thm)],[c_220]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_1799,plain,
% 7.43/1.43      ( k7_relat_1(sK2,sK4) = k7_relat_1(sK2,sK4) ),
% 7.43/1.43      inference(instantiation,[status(thm)],[c_1798]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_3911,plain,
% 7.43/1.43      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK4)),k1_relat_1(X0))
% 7.43/1.43      | ~ v1_relat_1(X0) ),
% 7.43/1.43      inference(instantiation,[status(thm)],[c_5]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_3912,plain,
% 7.43/1.43      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK4)),k1_relat_1(X0)) = iProver_top
% 7.43/1.43      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_3911]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_3914,plain,
% 7.43/1.43      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) = iProver_top
% 7.43/1.43      | v1_relat_1(sK2) != iProver_top ),
% 7.43/1.43      inference(instantiation,[status(thm)],[c_3912]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_19240,plain,
% 7.43/1.43      ( k1_funct_1(sK3,sK1(sK2,sK3,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK1(sK2,sK3,k1_relat_1(k7_relat_1(sK2,sK4)))) ),
% 7.43/1.43      inference(global_propositional_subsumption,
% 7.43/1.43                [status(thm)],
% 7.43/1.43                [c_10561,c_22,c_23,c_15,c_618,c_1799,c_3914]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_5712,plain,
% 7.43/1.43      ( k1_relat_1(k7_relat_1(sK0(X0,X1),k1_relat_1(sK2))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 7.43/1.43      inference(demodulation,[status(thm)],[c_5562,c_3595]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_15639,plain,
% 7.43/1.43      ( sP0_iProver_split(k1_relat_1(sK2),X0) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 7.43/1.43      inference(demodulation,[status(thm)],[c_9041,c_5712]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_19242,plain,
% 7.43/1.43      ( k1_funct_1(sK2,sK1(sK2,sK3,sP0_iProver_split(k1_relat_1(sK2),sK4))) = k1_funct_1(sK3,sK1(sK2,sK3,sP0_iProver_split(k1_relat_1(sK2),sK4))) ),
% 7.43/1.43      inference(demodulation,[status(thm)],[c_19240,c_15639]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_12,plain,
% 7.43/1.43      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.43/1.43      | ~ r1_tarski(X0,k1_relat_1(X2))
% 7.43/1.43      | ~ v1_funct_1(X1)
% 7.43/1.43      | ~ v1_funct_1(X2)
% 7.43/1.43      | ~ v1_relat_1(X1)
% 7.43/1.43      | ~ v1_relat_1(X2)
% 7.43/1.43      | k1_funct_1(X1,sK1(X2,X1,X0)) != k1_funct_1(X2,sK1(X2,X1,X0))
% 7.43/1.43      | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
% 7.43/1.43      inference(cnf_transformation,[],[f50]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_553,plain,
% 7.43/1.43      ( k1_funct_1(X0,sK1(X1,X0,X2)) != k1_funct_1(X1,sK1(X1,X0,X2))
% 7.43/1.43      | k7_relat_1(X1,X2) = k7_relat_1(X0,X2)
% 7.43/1.43      | r1_tarski(X2,k1_relat_1(X0)) != iProver_top
% 7.43/1.43      | r1_tarski(X2,k1_relat_1(X1)) != iProver_top
% 7.43/1.43      | v1_funct_1(X0) != iProver_top
% 7.43/1.43      | v1_funct_1(X1) != iProver_top
% 7.43/1.43      | v1_relat_1(X0) != iProver_top
% 7.43/1.43      | v1_relat_1(X1) != iProver_top ),
% 7.43/1.43      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_19243,plain,
% 7.43/1.43      ( k7_relat_1(sK3,sP0_iProver_split(k1_relat_1(sK2),sK4)) = k7_relat_1(sK2,sP0_iProver_split(k1_relat_1(sK2),sK4))
% 7.43/1.43      | r1_tarski(sP0_iProver_split(k1_relat_1(sK2),sK4),k1_relat_1(sK3)) != iProver_top
% 7.43/1.43      | r1_tarski(sP0_iProver_split(k1_relat_1(sK2),sK4),k1_relat_1(sK2)) != iProver_top
% 7.43/1.43      | v1_funct_1(sK3) != iProver_top
% 7.43/1.43      | v1_funct_1(sK2) != iProver_top
% 7.43/1.43      | v1_relat_1(sK3) != iProver_top
% 7.43/1.43      | v1_relat_1(sK2) != iProver_top ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_19242,c_553]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_19244,plain,
% 7.43/1.43      ( k7_relat_1(sK3,sP0_iProver_split(k1_relat_1(sK2),sK4)) = k7_relat_1(sK2,sP0_iProver_split(k1_relat_1(sK2),sK4))
% 7.43/1.43      | r1_tarski(sP0_iProver_split(k1_relat_1(sK2),sK4),k1_relat_1(sK2)) != iProver_top
% 7.43/1.43      | v1_funct_1(sK3) != iProver_top
% 7.43/1.43      | v1_funct_1(sK2) != iProver_top
% 7.43/1.43      | v1_relat_1(sK3) != iProver_top
% 7.43/1.43      | v1_relat_1(sK2) != iProver_top ),
% 7.43/1.43      inference(light_normalisation,[status(thm)],[c_19243,c_17]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_19247,plain,
% 7.43/1.43      ( k7_relat_1(sK3,sP0_iProver_split(k1_relat_1(sK2),sK4)) = k7_relat_1(sK2,sP0_iProver_split(k1_relat_1(sK2),sK4))
% 7.43/1.43      | r1_tarski(sP0_iProver_split(k1_relat_1(sK2),sK4),k1_relat_1(sK2)) != iProver_top ),
% 7.43/1.43      inference(global_propositional_subsumption,
% 7.43/1.43                [status(thm)],
% 7.43/1.43                [c_19244,c_22,c_23,c_24,c_25]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_19833,plain,
% 7.43/1.43      ( k7_relat_1(sK3,sP0_iProver_split(k1_relat_1(sK2),sK4)) = k7_relat_1(sK2,sP0_iProver_split(k1_relat_1(sK2),sK4)) ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_18898,c_19247]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_15638,plain,
% 7.43/1.43      ( k7_relat_1(X0,sP0_iProver_split(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1)
% 7.43/1.43      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.43      inference(demodulation,[status(thm)],[c_9041,c_1500]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_20115,plain,
% 7.43/1.43      ( k7_relat_1(sK2,sP0_iProver_split(k1_relat_1(sK2),X0)) = k7_relat_1(sK2,X0) ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_546,c_15638]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_20876,plain,
% 7.43/1.43      ( k7_relat_1(sK3,sP0_iProver_split(k1_relat_1(sK2),sK4)) = k7_relat_1(sK2,sK4) ),
% 7.43/1.43      inference(demodulation,[status(thm)],[c_19833,c_20115]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_20114,plain,
% 7.43/1.43      ( k7_relat_1(sK3,sP0_iProver_split(k1_relat_1(sK3),X0)) = k7_relat_1(sK3,X0) ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_548,c_15638]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_20116,plain,
% 7.43/1.43      ( k7_relat_1(sK3,sP0_iProver_split(k1_relat_1(sK2),X0)) = k7_relat_1(sK3,X0) ),
% 7.43/1.43      inference(light_normalisation,[status(thm)],[c_20114,c_17]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(c_20895,plain,
% 7.43/1.43      ( k7_relat_1(sK3,sK4) = k7_relat_1(sK2,sK4) ),
% 7.43/1.43      inference(superposition,[status(thm)],[c_20876,c_20116]) ).
% 7.43/1.43  
% 7.43/1.43  cnf(contradiction,plain,
% 7.43/1.43      ( $false ),
% 7.43/1.43      inference(minisat,[status(thm)],[c_20895,c_1799,c_618,c_15]) ).
% 7.43/1.43  
% 7.43/1.43  
% 7.43/1.43  % SZS output end CNFRefutation for theBenchmark.p
% 7.43/1.43  
% 7.43/1.43  ------                               Statistics
% 7.43/1.43  
% 7.43/1.43  ------ General
% 7.43/1.43  
% 7.43/1.43  abstr_ref_over_cycles:                  0
% 7.43/1.43  abstr_ref_under_cycles:                 0
% 7.43/1.43  gc_basic_clause_elim:                   0
% 7.43/1.43  forced_gc_time:                         0
% 7.43/1.43  parsing_time:                           0.006
% 7.43/1.43  unif_index_cands_time:                  0.
% 7.43/1.43  unif_index_add_time:                    0.
% 7.43/1.43  orderings_time:                         0.
% 7.43/1.43  out_proof_time:                         0.012
% 7.43/1.43  total_time:                             0.691
% 7.43/1.43  num_of_symbols:                         44
% 7.43/1.43  num_of_terms:                           32305
% 7.43/1.43  
% 7.43/1.43  ------ Preprocessing
% 7.43/1.43  
% 7.43/1.43  num_of_splits:                          0
% 7.43/1.43  num_of_split_atoms:                     1
% 7.43/1.43  num_of_reused_defs:                     0
% 7.43/1.43  num_eq_ax_congr_red:                    10
% 7.43/1.43  num_of_sem_filtered_clauses:            1
% 7.43/1.43  num_of_subtypes:                        0
% 7.43/1.43  monotx_restored_types:                  0
% 7.43/1.43  sat_num_of_epr_types:                   0
% 7.43/1.43  sat_num_of_non_cyclic_types:            0
% 7.43/1.43  sat_guarded_non_collapsed_types:        0
% 7.43/1.43  num_pure_diseq_elim:                    0
% 7.43/1.43  simp_replaced_by:                       0
% 7.43/1.43  res_preprocessed:                       85
% 7.43/1.43  prep_upred:                             0
% 7.43/1.43  prep_unflattend:                        0
% 7.43/1.43  smt_new_axioms:                         0
% 7.43/1.43  pred_elim_cands:                        4
% 7.43/1.43  pred_elim:                              0
% 7.43/1.43  pred_elim_cl:                           0
% 7.43/1.43  pred_elim_cycles:                       1
% 7.43/1.43  merged_defs:                            0
% 7.43/1.43  merged_defs_ncl:                        0
% 7.43/1.43  bin_hyper_res:                          0
% 7.43/1.43  prep_cycles:                            3
% 7.43/1.43  pred_elim_time:                         0.
% 7.43/1.43  splitting_time:                         0.
% 7.43/1.43  sem_filter_time:                        0.
% 7.43/1.43  monotx_time:                            0.
% 7.43/1.43  subtype_inf_time:                       0.
% 7.43/1.43  
% 7.43/1.43  ------ Problem properties
% 7.43/1.43  
% 7.43/1.43  clauses:                                22
% 7.43/1.43  conjectures:                            7
% 7.43/1.43  epr:                                    4
% 7.43/1.43  horn:                                   21
% 7.43/1.43  ground:                                 6
% 7.43/1.43  unary:                                  9
% 7.43/1.43  binary:                                 4
% 7.43/1.43  lits:                                   61
% 7.43/1.43  lits_eq:                                13
% 7.43/1.43  fd_pure:                                0
% 7.43/1.43  fd_pseudo:                              0
% 7.43/1.43  fd_cond:                                0
% 7.43/1.43  fd_pseudo_cond:                         0
% 7.43/1.43  ac_symbols:                             0
% 7.43/1.43  
% 7.43/1.43  ------ Propositional Solver
% 7.43/1.43  
% 7.43/1.43  prop_solver_calls:                      30
% 7.43/1.43  prop_fast_solver_calls:                 1867
% 7.43/1.43  smt_solver_calls:                       0
% 7.43/1.43  smt_fast_solver_calls:                  0
% 7.43/1.43  prop_num_of_clauses:                    7368
% 7.43/1.43  prop_preprocess_simplified:             12121
% 7.43/1.43  prop_fo_subsumed:                       125
% 7.43/1.43  prop_solver_time:                       0.
% 7.43/1.43  smt_solver_time:                        0.
% 7.43/1.43  smt_fast_solver_time:                   0.
% 7.43/1.43  prop_fast_solver_time:                  0.
% 7.43/1.43  prop_unsat_core_time:                   0.001
% 7.43/1.43  
% 7.43/1.43  ------ QBF
% 7.43/1.43  
% 7.43/1.43  qbf_q_res:                              0
% 7.43/1.43  qbf_num_tautologies:                    0
% 7.43/1.43  qbf_prep_cycles:                        0
% 7.43/1.43  
% 7.43/1.43  ------ BMC1
% 7.43/1.43  
% 7.43/1.43  bmc1_current_bound:                     -1
% 7.43/1.43  bmc1_last_solved_bound:                 -1
% 7.43/1.43  bmc1_unsat_core_size:                   -1
% 7.43/1.43  bmc1_unsat_core_parents_size:           -1
% 7.43/1.43  bmc1_merge_next_fun:                    0
% 7.43/1.43  bmc1_unsat_core_clauses_time:           0.
% 7.43/1.43  
% 7.43/1.43  ------ Instantiation
% 7.43/1.43  
% 7.43/1.43  inst_num_of_clauses:                    2110
% 7.43/1.43  inst_num_in_passive:                    511
% 7.43/1.43  inst_num_in_active:                     939
% 7.43/1.43  inst_num_in_unprocessed:                660
% 7.43/1.43  inst_num_of_loops:                      990
% 7.43/1.43  inst_num_of_learning_restarts:          0
% 7.43/1.43  inst_num_moves_active_passive:          45
% 7.43/1.43  inst_lit_activity:                      0
% 7.43/1.43  inst_lit_activity_moves:                0
% 7.43/1.43  inst_num_tautologies:                   0
% 7.43/1.43  inst_num_prop_implied:                  0
% 7.43/1.43  inst_num_existing_simplified:           0
% 7.43/1.43  inst_num_eq_res_simplified:             0
% 7.43/1.43  inst_num_child_elim:                    0
% 7.43/1.43  inst_num_of_dismatching_blockings:      3693
% 7.43/1.43  inst_num_of_non_proper_insts:           4310
% 7.43/1.43  inst_num_of_duplicates:                 0
% 7.43/1.43  inst_inst_num_from_inst_to_res:         0
% 7.43/1.43  inst_dismatching_checking_time:         0.
% 7.43/1.43  
% 7.43/1.43  ------ Resolution
% 7.43/1.43  
% 7.43/1.43  res_num_of_clauses:                     0
% 7.43/1.43  res_num_in_passive:                     0
% 7.43/1.43  res_num_in_active:                      0
% 7.43/1.43  res_num_of_loops:                       88
% 7.43/1.43  res_forward_subset_subsumed:            364
% 7.43/1.43  res_backward_subset_subsumed:           2
% 7.43/1.43  res_forward_subsumed:                   0
% 7.43/1.43  res_backward_subsumed:                  0
% 7.43/1.43  res_forward_subsumption_resolution:     0
% 7.43/1.43  res_backward_subsumption_resolution:    0
% 7.43/1.43  res_clause_to_clause_subsumption:       3023
% 7.43/1.43  res_orphan_elimination:                 0
% 7.43/1.43  res_tautology_del:                      367
% 7.43/1.43  res_num_eq_res_simplified:              0
% 7.43/1.43  res_num_sel_changes:                    0
% 7.43/1.43  res_moves_from_active_to_pass:          0
% 7.43/1.43  
% 7.43/1.43  ------ Superposition
% 7.43/1.43  
% 7.43/1.43  sup_time_total:                         0.
% 7.43/1.43  sup_time_generating:                    0.
% 7.43/1.43  sup_time_sim_full:                      0.
% 7.43/1.43  sup_time_sim_immed:                     0.
% 7.43/1.43  
% 7.43/1.43  sup_num_of_clauses:                     586
% 7.43/1.43  sup_num_in_active:                      139
% 7.43/1.43  sup_num_in_passive:                     447
% 7.43/1.43  sup_num_of_loops:                       197
% 7.43/1.43  sup_fw_superposition:                   631
% 7.43/1.43  sup_bw_superposition:                   571
% 7.43/1.43  sup_immediate_simplified:               775
% 7.43/1.43  sup_given_eliminated:                   2
% 7.43/1.43  comparisons_done:                       0
% 7.43/1.43  comparisons_avoided:                    99
% 7.43/1.43  
% 7.43/1.43  ------ Simplifications
% 7.43/1.43  
% 7.43/1.43  
% 7.43/1.43  sim_fw_subset_subsumed:                 37
% 7.43/1.43  sim_bw_subset_subsumed:                 47
% 7.43/1.43  sim_fw_subsumed:                        120
% 7.43/1.43  sim_bw_subsumed:                        24
% 7.43/1.43  sim_fw_subsumption_res:                 0
% 7.43/1.43  sim_bw_subsumption_res:                 0
% 7.43/1.43  sim_tautology_del:                      74
% 7.43/1.43  sim_eq_tautology_del:                   88
% 7.43/1.43  sim_eq_res_simp:                        1
% 7.43/1.43  sim_fw_demodulated:                     552
% 7.43/1.43  sim_bw_demodulated:                     44
% 7.43/1.43  sim_light_normalised:                   322
% 7.43/1.43  sim_joinable_taut:                      0
% 7.43/1.43  sim_joinable_simp:                      0
% 7.43/1.43  sim_ac_normalised:                      0
% 7.43/1.43  sim_smt_subsumption:                    0
% 7.43/1.43  
%------------------------------------------------------------------------------
