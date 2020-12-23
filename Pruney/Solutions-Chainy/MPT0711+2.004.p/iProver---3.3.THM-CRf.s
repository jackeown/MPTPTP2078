%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:42 EST 2020

% Result     : Theorem 7.74s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 937 expanded)
%              Number of clauses        :   76 ( 259 expanded)
%              Number of leaves         :   18 ( 283 expanded)
%              Depth                    :   22
%              Number of atoms          :  457 (4540 expanded)
%              Number of equality atoms :  254 (2140 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f53,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f44,f60])).

fof(f55,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    k1_relat_1(sK2) = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

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

fof(f51,plain,(
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

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

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

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,X3) = k1_funct_1(sK3,X3)
      | ~ r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = k1_xboole_0 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k1_xboole_0
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = k1_xboole_0
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_funct_1(sK0(X0),X2) = k1_xboole_0
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK0(X0)) = X0
        & v1_funct_1(sK0(X0))
        & v1_relat_1(sK0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_funct_1(sK0(X0),X2) = k1_xboole_0
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK0(X0)) = X0
      & v1_funct_1(sK0(X0))
      & v1_relat_1(sK0(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f26])).

fof(f46,plain,(
    ! [X0] : v1_relat_1(sK0(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0] : k1_relat_1(sK0(X0)) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f61,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(definition_unfolding,[],[f36,f60,f60])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
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

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_547,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_559,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1356,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_547,c_559])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_549,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1355,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_549,c_559])).

cnf(c_17,negated_conjecture,
    ( k1_relat_1(sK2) = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1398,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1355,c_17])).

cnf(c_2265,plain,
    ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_1356,c_1398])).

cnf(c_5,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_560,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1098,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_560])).

cnf(c_24,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_806,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_807,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_221,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_736,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(X2,X3)),k1_relat_1(X2))
    | X1 != k1_relat_1(X2)
    | X0 != k1_relat_1(k7_relat_1(X2,X3)) ),
    inference(instantiation,[status(thm)],[c_221])).

cnf(c_784,plain,
    ( r1_tarski(X0,k1_relat_1(sK2))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),k1_relat_1(sK3))
    | X0 != k1_relat_1(k7_relat_1(sK3,X1))
    | k1_relat_1(sK2) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_736])).

cnf(c_952,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK3))
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK2))
    | k1_relat_1(k7_relat_1(sK3,X0)) != k1_relat_1(k7_relat_1(sK3,X0))
    | k1_relat_1(sK2) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_954,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) != k1_relat_1(k7_relat_1(sK3,X0))
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_952])).

cnf(c_213,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_790,plain,
    ( k1_relat_1(X0) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_953,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(c_1212,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1098,c_24,c_17,c_807,c_954,c_953])).

cnf(c_2292,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2265,c_1212])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | r2_hidden(sK1(X2,X1,X0),X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_553,plain,
    ( k7_relat_1(X0,X1) = k7_relat_1(X2,X1)
    | r1_tarski(X1,k1_relat_1(X2)) != iProver_top
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X1) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_561,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2157,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X3,k1_relat_1(k7_relat_1(X1,X2)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X3)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X0)) != iProver_top
    | r2_hidden(sK1(X3,X0,k1_relat_1(k7_relat_1(X1,X2))),X2) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_553,c_561])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_551,plain,
    ( k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_31164,plain,
    ( k1_funct_1(sK3,sK1(X0,X1,k1_relat_1(k7_relat_1(X2,sK4)))) = k1_funct_1(sK2,sK1(X0,X1,k1_relat_1(k7_relat_1(X2,sK4))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X2,sK4))) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(X2,sK4)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X2,sK4)),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2157,c_551])).

cnf(c_32723,plain,
    ( k1_funct_1(sK2,sK1(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK1(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_31164])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_25,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_33137,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK2,sK1(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK1(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32723,c_24,c_25])).

cnf(c_33138,plain,
    ( k1_funct_1(sK2,sK1(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK1(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_33137])).

cnf(c_33152,plain,
    ( k1_funct_1(sK3,sK1(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK1(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4))))
    | k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,sK4))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2292,c_33138])).

cnf(c_11,plain,
    ( v1_relat_1(sK0(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_555,plain,
    ( v1_relat_1(sK0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,k1_relat_1(k7_relat_1(X0,k1_relat_1(X1)))) = k7_relat_1(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_564,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5490,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(sK0(X1),k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(sK0(X1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_555,c_564])).

cnf(c_9,plain,
    ( k1_relat_1(sK0(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_5503,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(sK0(X1),k1_relat_1(X0)))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5490,c_9])).

cnf(c_5766,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK0(X0),k1_relat_1(sK2)))) = k7_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_547,c_5503])).

cnf(c_0,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1354,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(sK0(X0)),k1_relat_1(sK0(X0)),X1)) = k1_relat_1(k7_relat_1(sK0(X0),X1)) ),
    inference(superposition,[status(thm)],[c_555,c_559])).

cnf(c_1363,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(sK0(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_1354,c_9])).

cnf(c_1377,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(sK0(X1),X0)) ),
    inference(superposition,[status(thm)],[c_0,c_1363])).

cnf(c_2272,plain,
    ( k1_relat_1(k7_relat_1(sK0(X0),k1_relat_1(sK2))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_1356,c_1377])).

cnf(c_5768,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) = k7_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_5766,c_2272])).

cnf(c_5765,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK0(X0),k1_relat_1(sK3)))) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_549,c_5503])).

cnf(c_5771,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,X0))) = k7_relat_1(sK3,X0) ),
    inference(light_normalisation,[status(thm)],[c_5765,c_17,c_2272])).

cnf(c_33399,plain,
    ( k1_funct_1(sK3,sK1(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK1(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4))))
    | k7_relat_1(sK3,sK4) = k7_relat_1(sK2,sK4)
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_33152,c_5768,c_5771])).

cnf(c_22,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_15,negated_conjecture,
    ( k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_214,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_734,plain,
    ( k7_relat_1(sK3,sK4) != X0
    | k7_relat_1(sK2,sK4) != X0
    | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_754,plain,
    ( k7_relat_1(sK3,sK4) != k7_relat_1(X0,sK4)
    | k7_relat_1(sK2,sK4) != k7_relat_1(X0,sK4)
    | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_757,plain,
    ( k7_relat_1(sK3,sK4) != k7_relat_1(sK2,sK4)
    | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4)
    | k7_relat_1(sK2,sK4) != k7_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_22268,plain,
    ( k7_relat_1(sK2,sK4) = k7_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_33635,plain,
    ( k1_funct_1(sK3,sK1(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK1(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4))))
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33399,c_22,c_23,c_15,c_757,c_22268])).

cnf(c_33641,plain,
    ( k1_funct_1(sK3,sK1(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK1(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_33635,c_2292])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X1,sK1(X2,X1,X0)) != k1_funct_1(X2,sK1(X2,X1,X0))
    | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_554,plain,
    ( k1_funct_1(X0,sK1(X1,X0,X2)) != k1_funct_1(X1,sK1(X1,X0,X2))
    | k7_relat_1(X1,X2) = k7_relat_1(X0,X2)
    | r1_tarski(X2,k1_relat_1(X0)) != iProver_top
    | r1_tarski(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_33642,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,sK4))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_33641,c_554])).

cnf(c_33643,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,sK4))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33642,c_17])).

cnf(c_33644,plain,
    ( k7_relat_1(sK3,sK4) = k7_relat_1(sK2,sK4)
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_33643,c_5768,c_5771])).

cnf(c_33647,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33644,c_22,c_23,c_24,c_25,c_15,c_757,c_22268])).

cnf(c_33652,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_33647,c_2292])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:13:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.74/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/1.49  
% 7.74/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.74/1.49  
% 7.74/1.49  ------  iProver source info
% 7.74/1.49  
% 7.74/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.74/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.74/1.49  git: non_committed_changes: false
% 7.74/1.49  git: last_make_outside_of_git: false
% 7.74/1.49  
% 7.74/1.49  ------ 
% 7.74/1.49  
% 7.74/1.49  ------ Input Options
% 7.74/1.49  
% 7.74/1.49  --out_options                           all
% 7.74/1.49  --tptp_safe_out                         true
% 7.74/1.49  --problem_path                          ""
% 7.74/1.49  --include_path                          ""
% 7.74/1.49  --clausifier                            res/vclausify_rel
% 7.74/1.49  --clausifier_options                    --mode clausify
% 7.74/1.49  --stdin                                 false
% 7.74/1.49  --stats_out                             all
% 7.74/1.49  
% 7.74/1.49  ------ General Options
% 7.74/1.49  
% 7.74/1.49  --fof                                   false
% 7.74/1.49  --time_out_real                         305.
% 7.74/1.49  --time_out_virtual                      -1.
% 7.74/1.49  --symbol_type_check                     false
% 7.74/1.49  --clausify_out                          false
% 7.74/1.49  --sig_cnt_out                           false
% 7.74/1.49  --trig_cnt_out                          false
% 7.74/1.49  --trig_cnt_out_tolerance                1.
% 7.74/1.49  --trig_cnt_out_sk_spl                   false
% 7.74/1.49  --abstr_cl_out                          false
% 7.74/1.49  
% 7.74/1.49  ------ Global Options
% 7.74/1.49  
% 7.74/1.49  --schedule                              default
% 7.74/1.49  --add_important_lit                     false
% 7.74/1.49  --prop_solver_per_cl                    1000
% 7.74/1.49  --min_unsat_core                        false
% 7.74/1.49  --soft_assumptions                      false
% 7.74/1.49  --soft_lemma_size                       3
% 7.74/1.49  --prop_impl_unit_size                   0
% 7.74/1.49  --prop_impl_unit                        []
% 7.74/1.49  --share_sel_clauses                     true
% 7.74/1.49  --reset_solvers                         false
% 7.74/1.49  --bc_imp_inh                            [conj_cone]
% 7.74/1.49  --conj_cone_tolerance                   3.
% 7.74/1.49  --extra_neg_conj                        none
% 7.74/1.49  --large_theory_mode                     true
% 7.74/1.49  --prolific_symb_bound                   200
% 7.74/1.49  --lt_threshold                          2000
% 7.74/1.49  --clause_weak_htbl                      true
% 7.74/1.49  --gc_record_bc_elim                     false
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing Options
% 7.74/1.49  
% 7.74/1.49  --preprocessing_flag                    true
% 7.74/1.49  --time_out_prep_mult                    0.1
% 7.74/1.49  --splitting_mode                        input
% 7.74/1.49  --splitting_grd                         true
% 7.74/1.49  --splitting_cvd                         false
% 7.74/1.49  --splitting_cvd_svl                     false
% 7.74/1.49  --splitting_nvd                         32
% 7.74/1.49  --sub_typing                            true
% 7.74/1.49  --prep_gs_sim                           true
% 7.74/1.49  --prep_unflatten                        true
% 7.74/1.49  --prep_res_sim                          true
% 7.74/1.49  --prep_upred                            true
% 7.74/1.49  --prep_sem_filter                       exhaustive
% 7.74/1.49  --prep_sem_filter_out                   false
% 7.74/1.49  --pred_elim                             true
% 7.74/1.49  --res_sim_input                         true
% 7.74/1.49  --eq_ax_congr_red                       true
% 7.74/1.49  --pure_diseq_elim                       true
% 7.74/1.49  --brand_transform                       false
% 7.74/1.49  --non_eq_to_eq                          false
% 7.74/1.49  --prep_def_merge                        true
% 7.74/1.49  --prep_def_merge_prop_impl              false
% 7.74/1.49  --prep_def_merge_mbd                    true
% 7.74/1.49  --prep_def_merge_tr_red                 false
% 7.74/1.49  --prep_def_merge_tr_cl                  false
% 7.74/1.49  --smt_preprocessing                     true
% 7.74/1.49  --smt_ac_axioms                         fast
% 7.74/1.49  --preprocessed_out                      false
% 7.74/1.49  --preprocessed_stats                    false
% 7.74/1.49  
% 7.74/1.49  ------ Abstraction refinement Options
% 7.74/1.49  
% 7.74/1.49  --abstr_ref                             []
% 7.74/1.49  --abstr_ref_prep                        false
% 7.74/1.49  --abstr_ref_until_sat                   false
% 7.74/1.49  --abstr_ref_sig_restrict                funpre
% 7.74/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.74/1.49  --abstr_ref_under                       []
% 7.74/1.49  
% 7.74/1.49  ------ SAT Options
% 7.74/1.49  
% 7.74/1.49  --sat_mode                              false
% 7.74/1.49  --sat_fm_restart_options                ""
% 7.74/1.49  --sat_gr_def                            false
% 7.74/1.49  --sat_epr_types                         true
% 7.74/1.49  --sat_non_cyclic_types                  false
% 7.74/1.49  --sat_finite_models                     false
% 7.74/1.49  --sat_fm_lemmas                         false
% 7.74/1.49  --sat_fm_prep                           false
% 7.74/1.49  --sat_fm_uc_incr                        true
% 7.74/1.49  --sat_out_model                         small
% 7.74/1.49  --sat_out_clauses                       false
% 7.74/1.49  
% 7.74/1.49  ------ QBF Options
% 7.74/1.49  
% 7.74/1.49  --qbf_mode                              false
% 7.74/1.49  --qbf_elim_univ                         false
% 7.74/1.49  --qbf_dom_inst                          none
% 7.74/1.49  --qbf_dom_pre_inst                      false
% 7.74/1.49  --qbf_sk_in                             false
% 7.74/1.49  --qbf_pred_elim                         true
% 7.74/1.49  --qbf_split                             512
% 7.74/1.49  
% 7.74/1.49  ------ BMC1 Options
% 7.74/1.49  
% 7.74/1.49  --bmc1_incremental                      false
% 7.74/1.49  --bmc1_axioms                           reachable_all
% 7.74/1.49  --bmc1_min_bound                        0
% 7.74/1.49  --bmc1_max_bound                        -1
% 7.74/1.49  --bmc1_max_bound_default                -1
% 7.74/1.49  --bmc1_symbol_reachability              true
% 7.74/1.49  --bmc1_property_lemmas                  false
% 7.74/1.49  --bmc1_k_induction                      false
% 7.74/1.49  --bmc1_non_equiv_states                 false
% 7.74/1.49  --bmc1_deadlock                         false
% 7.74/1.49  --bmc1_ucm                              false
% 7.74/1.49  --bmc1_add_unsat_core                   none
% 7.74/1.49  --bmc1_unsat_core_children              false
% 7.74/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.74/1.49  --bmc1_out_stat                         full
% 7.74/1.49  --bmc1_ground_init                      false
% 7.74/1.49  --bmc1_pre_inst_next_state              false
% 7.74/1.49  --bmc1_pre_inst_state                   false
% 7.74/1.49  --bmc1_pre_inst_reach_state             false
% 7.74/1.49  --bmc1_out_unsat_core                   false
% 7.74/1.49  --bmc1_aig_witness_out                  false
% 7.74/1.49  --bmc1_verbose                          false
% 7.74/1.49  --bmc1_dump_clauses_tptp                false
% 7.74/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.74/1.49  --bmc1_dump_file                        -
% 7.74/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.74/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.74/1.49  --bmc1_ucm_extend_mode                  1
% 7.74/1.49  --bmc1_ucm_init_mode                    2
% 7.74/1.49  --bmc1_ucm_cone_mode                    none
% 7.74/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.74/1.49  --bmc1_ucm_relax_model                  4
% 7.74/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.74/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.74/1.49  --bmc1_ucm_layered_model                none
% 7.74/1.49  --bmc1_ucm_max_lemma_size               10
% 7.74/1.49  
% 7.74/1.49  ------ AIG Options
% 7.74/1.49  
% 7.74/1.49  --aig_mode                              false
% 7.74/1.49  
% 7.74/1.49  ------ Instantiation Options
% 7.74/1.49  
% 7.74/1.49  --instantiation_flag                    true
% 7.74/1.49  --inst_sos_flag                         false
% 7.74/1.49  --inst_sos_phase                        true
% 7.74/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.74/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.74/1.49  --inst_lit_sel_side                     num_symb
% 7.74/1.49  --inst_solver_per_active                1400
% 7.74/1.49  --inst_solver_calls_frac                1.
% 7.74/1.49  --inst_passive_queue_type               priority_queues
% 7.74/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.74/1.49  --inst_passive_queues_freq              [25;2]
% 7.74/1.49  --inst_dismatching                      true
% 7.74/1.49  --inst_eager_unprocessed_to_passive     true
% 7.74/1.49  --inst_prop_sim_given                   true
% 7.74/1.49  --inst_prop_sim_new                     false
% 7.74/1.49  --inst_subs_new                         false
% 7.74/1.49  --inst_eq_res_simp                      false
% 7.74/1.49  --inst_subs_given                       false
% 7.74/1.49  --inst_orphan_elimination               true
% 7.74/1.49  --inst_learning_loop_flag               true
% 7.74/1.49  --inst_learning_start                   3000
% 7.74/1.49  --inst_learning_factor                  2
% 7.74/1.49  --inst_start_prop_sim_after_learn       3
% 7.74/1.49  --inst_sel_renew                        solver
% 7.74/1.49  --inst_lit_activity_flag                true
% 7.74/1.49  --inst_restr_to_given                   false
% 7.74/1.49  --inst_activity_threshold               500
% 7.74/1.49  --inst_out_proof                        true
% 7.74/1.49  
% 7.74/1.49  ------ Resolution Options
% 7.74/1.49  
% 7.74/1.49  --resolution_flag                       true
% 7.74/1.49  --res_lit_sel                           adaptive
% 7.74/1.49  --res_lit_sel_side                      none
% 7.74/1.49  --res_ordering                          kbo
% 7.74/1.49  --res_to_prop_solver                    active
% 7.74/1.49  --res_prop_simpl_new                    false
% 7.74/1.49  --res_prop_simpl_given                  true
% 7.74/1.49  --res_passive_queue_type                priority_queues
% 7.74/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.74/1.49  --res_passive_queues_freq               [15;5]
% 7.74/1.49  --res_forward_subs                      full
% 7.74/1.49  --res_backward_subs                     full
% 7.74/1.49  --res_forward_subs_resolution           true
% 7.74/1.49  --res_backward_subs_resolution          true
% 7.74/1.49  --res_orphan_elimination                true
% 7.74/1.49  --res_time_limit                        2.
% 7.74/1.49  --res_out_proof                         true
% 7.74/1.49  
% 7.74/1.49  ------ Superposition Options
% 7.74/1.49  
% 7.74/1.49  --superposition_flag                    true
% 7.74/1.49  --sup_passive_queue_type                priority_queues
% 7.74/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.74/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.74/1.49  --demod_completeness_check              fast
% 7.74/1.49  --demod_use_ground                      true
% 7.74/1.49  --sup_to_prop_solver                    passive
% 7.74/1.49  --sup_prop_simpl_new                    true
% 7.74/1.49  --sup_prop_simpl_given                  true
% 7.74/1.49  --sup_fun_splitting                     false
% 7.74/1.49  --sup_smt_interval                      50000
% 7.74/1.49  
% 7.74/1.49  ------ Superposition Simplification Setup
% 7.74/1.49  
% 7.74/1.49  --sup_indices_passive                   []
% 7.74/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.74/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.74/1.49  --sup_full_bw                           [BwDemod]
% 7.74/1.49  --sup_immed_triv                        [TrivRules]
% 7.74/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.74/1.49  --sup_immed_bw_main                     []
% 7.74/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.74/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.74/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.74/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.74/1.49  
% 7.74/1.49  ------ Combination Options
% 7.74/1.49  
% 7.74/1.49  --comb_res_mult                         3
% 7.74/1.49  --comb_sup_mult                         2
% 7.74/1.49  --comb_inst_mult                        10
% 7.74/1.49  
% 7.74/1.49  ------ Debug Options
% 7.74/1.49  
% 7.74/1.49  --dbg_backtrace                         false
% 7.74/1.49  --dbg_dump_prop_clauses                 false
% 7.74/1.49  --dbg_dump_prop_clauses_file            -
% 7.74/1.49  --dbg_out_stat                          false
% 7.74/1.49  ------ Parsing...
% 7.74/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.49  ------ Proving...
% 7.74/1.49  ------ Problem Properties 
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  clauses                                 22
% 7.74/1.49  conjectures                             7
% 7.74/1.49  EPR                                     4
% 7.74/1.49  Horn                                    21
% 7.74/1.49  unary                                   10
% 7.74/1.49  binary                                  4
% 7.74/1.49  lits                                    59
% 7.74/1.49  lits eq                                 14
% 7.74/1.49  fd_pure                                 0
% 7.74/1.49  fd_pseudo                               0
% 7.74/1.49  fd_cond                                 0
% 7.74/1.49  fd_pseudo_cond                          0
% 7.74/1.49  AC symbols                              0
% 7.74/1.49  
% 7.74/1.49  ------ Schedule dynamic 5 is on 
% 7.74/1.49  
% 7.74/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  ------ 
% 7.74/1.49  Current options:
% 7.74/1.49  ------ 
% 7.74/1.49  
% 7.74/1.49  ------ Input Options
% 7.74/1.49  
% 7.74/1.49  --out_options                           all
% 7.74/1.49  --tptp_safe_out                         true
% 7.74/1.49  --problem_path                          ""
% 7.74/1.49  --include_path                          ""
% 7.74/1.49  --clausifier                            res/vclausify_rel
% 7.74/1.49  --clausifier_options                    --mode clausify
% 7.74/1.49  --stdin                                 false
% 7.74/1.49  --stats_out                             all
% 7.74/1.49  
% 7.74/1.49  ------ General Options
% 7.74/1.49  
% 7.74/1.49  --fof                                   false
% 7.74/1.49  --time_out_real                         305.
% 7.74/1.49  --time_out_virtual                      -1.
% 7.74/1.49  --symbol_type_check                     false
% 7.74/1.49  --clausify_out                          false
% 7.74/1.49  --sig_cnt_out                           false
% 7.74/1.49  --trig_cnt_out                          false
% 7.74/1.49  --trig_cnt_out_tolerance                1.
% 7.74/1.49  --trig_cnt_out_sk_spl                   false
% 7.74/1.49  --abstr_cl_out                          false
% 7.74/1.49  
% 7.74/1.49  ------ Global Options
% 7.74/1.49  
% 7.74/1.49  --schedule                              default
% 7.74/1.49  --add_important_lit                     false
% 7.74/1.49  --prop_solver_per_cl                    1000
% 7.74/1.49  --min_unsat_core                        false
% 7.74/1.49  --soft_assumptions                      false
% 7.74/1.49  --soft_lemma_size                       3
% 7.74/1.49  --prop_impl_unit_size                   0
% 7.74/1.49  --prop_impl_unit                        []
% 7.74/1.49  --share_sel_clauses                     true
% 7.74/1.49  --reset_solvers                         false
% 7.74/1.49  --bc_imp_inh                            [conj_cone]
% 7.74/1.49  --conj_cone_tolerance                   3.
% 7.74/1.49  --extra_neg_conj                        none
% 7.74/1.49  --large_theory_mode                     true
% 7.74/1.49  --prolific_symb_bound                   200
% 7.74/1.49  --lt_threshold                          2000
% 7.74/1.49  --clause_weak_htbl                      true
% 7.74/1.49  --gc_record_bc_elim                     false
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing Options
% 7.74/1.49  
% 7.74/1.49  --preprocessing_flag                    true
% 7.74/1.49  --time_out_prep_mult                    0.1
% 7.74/1.49  --splitting_mode                        input
% 7.74/1.49  --splitting_grd                         true
% 7.74/1.49  --splitting_cvd                         false
% 7.74/1.49  --splitting_cvd_svl                     false
% 7.74/1.49  --splitting_nvd                         32
% 7.74/1.49  --sub_typing                            true
% 7.74/1.49  --prep_gs_sim                           true
% 7.74/1.49  --prep_unflatten                        true
% 7.74/1.49  --prep_res_sim                          true
% 7.74/1.49  --prep_upred                            true
% 7.74/1.49  --prep_sem_filter                       exhaustive
% 7.74/1.49  --prep_sem_filter_out                   false
% 7.74/1.49  --pred_elim                             true
% 7.74/1.49  --res_sim_input                         true
% 7.74/1.49  --eq_ax_congr_red                       true
% 7.74/1.49  --pure_diseq_elim                       true
% 7.74/1.49  --brand_transform                       false
% 7.74/1.49  --non_eq_to_eq                          false
% 7.74/1.49  --prep_def_merge                        true
% 7.74/1.49  --prep_def_merge_prop_impl              false
% 7.74/1.49  --prep_def_merge_mbd                    true
% 7.74/1.49  --prep_def_merge_tr_red                 false
% 7.74/1.49  --prep_def_merge_tr_cl                  false
% 7.74/1.49  --smt_preprocessing                     true
% 7.74/1.49  --smt_ac_axioms                         fast
% 7.74/1.49  --preprocessed_out                      false
% 7.74/1.49  --preprocessed_stats                    false
% 7.74/1.49  
% 7.74/1.49  ------ Abstraction refinement Options
% 7.74/1.49  
% 7.74/1.49  --abstr_ref                             []
% 7.74/1.49  --abstr_ref_prep                        false
% 7.74/1.49  --abstr_ref_until_sat                   false
% 7.74/1.49  --abstr_ref_sig_restrict                funpre
% 7.74/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.74/1.49  --abstr_ref_under                       []
% 7.74/1.49  
% 7.74/1.49  ------ SAT Options
% 7.74/1.49  
% 7.74/1.49  --sat_mode                              false
% 7.74/1.49  --sat_fm_restart_options                ""
% 7.74/1.49  --sat_gr_def                            false
% 7.74/1.49  --sat_epr_types                         true
% 7.74/1.49  --sat_non_cyclic_types                  false
% 7.74/1.49  --sat_finite_models                     false
% 7.74/1.49  --sat_fm_lemmas                         false
% 7.74/1.49  --sat_fm_prep                           false
% 7.74/1.49  --sat_fm_uc_incr                        true
% 7.74/1.49  --sat_out_model                         small
% 7.74/1.49  --sat_out_clauses                       false
% 7.74/1.49  
% 7.74/1.49  ------ QBF Options
% 7.74/1.49  
% 7.74/1.49  --qbf_mode                              false
% 7.74/1.49  --qbf_elim_univ                         false
% 7.74/1.49  --qbf_dom_inst                          none
% 7.74/1.49  --qbf_dom_pre_inst                      false
% 7.74/1.49  --qbf_sk_in                             false
% 7.74/1.49  --qbf_pred_elim                         true
% 7.74/1.49  --qbf_split                             512
% 7.74/1.49  
% 7.74/1.49  ------ BMC1 Options
% 7.74/1.49  
% 7.74/1.49  --bmc1_incremental                      false
% 7.74/1.49  --bmc1_axioms                           reachable_all
% 7.74/1.49  --bmc1_min_bound                        0
% 7.74/1.49  --bmc1_max_bound                        -1
% 7.74/1.49  --bmc1_max_bound_default                -1
% 7.74/1.49  --bmc1_symbol_reachability              true
% 7.74/1.49  --bmc1_property_lemmas                  false
% 7.74/1.49  --bmc1_k_induction                      false
% 7.74/1.49  --bmc1_non_equiv_states                 false
% 7.74/1.49  --bmc1_deadlock                         false
% 7.74/1.49  --bmc1_ucm                              false
% 7.74/1.49  --bmc1_add_unsat_core                   none
% 7.74/1.49  --bmc1_unsat_core_children              false
% 7.74/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.74/1.49  --bmc1_out_stat                         full
% 7.74/1.49  --bmc1_ground_init                      false
% 7.74/1.49  --bmc1_pre_inst_next_state              false
% 7.74/1.49  --bmc1_pre_inst_state                   false
% 7.74/1.49  --bmc1_pre_inst_reach_state             false
% 7.74/1.49  --bmc1_out_unsat_core                   false
% 7.74/1.49  --bmc1_aig_witness_out                  false
% 7.74/1.49  --bmc1_verbose                          false
% 7.74/1.49  --bmc1_dump_clauses_tptp                false
% 7.74/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.74/1.49  --bmc1_dump_file                        -
% 7.74/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.74/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.74/1.49  --bmc1_ucm_extend_mode                  1
% 7.74/1.49  --bmc1_ucm_init_mode                    2
% 7.74/1.49  --bmc1_ucm_cone_mode                    none
% 7.74/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.74/1.49  --bmc1_ucm_relax_model                  4
% 7.74/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.74/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.74/1.49  --bmc1_ucm_layered_model                none
% 7.74/1.49  --bmc1_ucm_max_lemma_size               10
% 7.74/1.49  
% 7.74/1.49  ------ AIG Options
% 7.74/1.49  
% 7.74/1.49  --aig_mode                              false
% 7.74/1.49  
% 7.74/1.49  ------ Instantiation Options
% 7.74/1.49  
% 7.74/1.49  --instantiation_flag                    true
% 7.74/1.49  --inst_sos_flag                         false
% 7.74/1.49  --inst_sos_phase                        true
% 7.74/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.74/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.74/1.49  --inst_lit_sel_side                     none
% 7.74/1.49  --inst_solver_per_active                1400
% 7.74/1.49  --inst_solver_calls_frac                1.
% 7.74/1.49  --inst_passive_queue_type               priority_queues
% 7.74/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.74/1.49  --inst_passive_queues_freq              [25;2]
% 7.74/1.49  --inst_dismatching                      true
% 7.74/1.49  --inst_eager_unprocessed_to_passive     true
% 7.74/1.49  --inst_prop_sim_given                   true
% 7.74/1.49  --inst_prop_sim_new                     false
% 7.74/1.49  --inst_subs_new                         false
% 7.74/1.49  --inst_eq_res_simp                      false
% 7.74/1.49  --inst_subs_given                       false
% 7.74/1.49  --inst_orphan_elimination               true
% 7.74/1.49  --inst_learning_loop_flag               true
% 7.74/1.49  --inst_learning_start                   3000
% 7.74/1.49  --inst_learning_factor                  2
% 7.74/1.49  --inst_start_prop_sim_after_learn       3
% 7.74/1.49  --inst_sel_renew                        solver
% 7.74/1.49  --inst_lit_activity_flag                true
% 7.74/1.49  --inst_restr_to_given                   false
% 7.74/1.49  --inst_activity_threshold               500
% 7.74/1.49  --inst_out_proof                        true
% 7.74/1.49  
% 7.74/1.49  ------ Resolution Options
% 7.74/1.49  
% 7.74/1.49  --resolution_flag                       false
% 7.74/1.49  --res_lit_sel                           adaptive
% 7.74/1.49  --res_lit_sel_side                      none
% 7.74/1.49  --res_ordering                          kbo
% 7.74/1.49  --res_to_prop_solver                    active
% 7.74/1.49  --res_prop_simpl_new                    false
% 7.74/1.49  --res_prop_simpl_given                  true
% 7.74/1.49  --res_passive_queue_type                priority_queues
% 7.74/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.74/1.49  --res_passive_queues_freq               [15;5]
% 7.74/1.49  --res_forward_subs                      full
% 7.74/1.49  --res_backward_subs                     full
% 7.74/1.49  --res_forward_subs_resolution           true
% 7.74/1.49  --res_backward_subs_resolution          true
% 7.74/1.49  --res_orphan_elimination                true
% 7.74/1.49  --res_time_limit                        2.
% 7.74/1.49  --res_out_proof                         true
% 7.74/1.49  
% 7.74/1.49  ------ Superposition Options
% 7.74/1.49  
% 7.74/1.49  --superposition_flag                    true
% 7.74/1.49  --sup_passive_queue_type                priority_queues
% 7.74/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.74/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.74/1.49  --demod_completeness_check              fast
% 7.74/1.49  --demod_use_ground                      true
% 7.74/1.49  --sup_to_prop_solver                    passive
% 7.74/1.49  --sup_prop_simpl_new                    true
% 7.74/1.49  --sup_prop_simpl_given                  true
% 7.74/1.49  --sup_fun_splitting                     false
% 7.74/1.49  --sup_smt_interval                      50000
% 7.74/1.49  
% 7.74/1.49  ------ Superposition Simplification Setup
% 7.74/1.49  
% 7.74/1.49  --sup_indices_passive                   []
% 7.74/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.74/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.74/1.49  --sup_full_bw                           [BwDemod]
% 7.74/1.49  --sup_immed_triv                        [TrivRules]
% 7.74/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.74/1.49  --sup_immed_bw_main                     []
% 7.74/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.74/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.74/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.74/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.74/1.49  
% 7.74/1.49  ------ Combination Options
% 7.74/1.49  
% 7.74/1.49  --comb_res_mult                         3
% 7.74/1.49  --comb_sup_mult                         2
% 7.74/1.49  --comb_inst_mult                        10
% 7.74/1.49  
% 7.74/1.49  ------ Debug Options
% 7.74/1.49  
% 7.74/1.49  --dbg_backtrace                         false
% 7.74/1.49  --dbg_dump_prop_clauses                 false
% 7.74/1.49  --dbg_dump_prop_clauses_file            -
% 7.74/1.49  --dbg_out_stat                          false
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  ------ Proving...
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  % SZS status Theorem for theBenchmark.p
% 7.74/1.49  
% 7.74/1.49   Resolution empty clause
% 7.74/1.49  
% 7.74/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.74/1.49  
% 7.74/1.49  fof(f11,conjecture,(
% 7.74/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X0) = k1_relat_1(X1)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f12,negated_conjecture,(
% 7.74/1.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X0) = k1_relat_1(X1)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 7.74/1.49    inference(negated_conjecture,[],[f11])).
% 7.74/1.49  
% 7.74/1.49  fof(f22,plain,(
% 7.74/1.49    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 7.74/1.49    inference(ennf_transformation,[],[f12])).
% 7.74/1.49  
% 7.74/1.49  fof(f23,plain,(
% 7.74/1.49    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.74/1.49    inference(flattening,[],[f22])).
% 7.74/1.49  
% 7.74/1.49  fof(f34,plain,(
% 7.74/1.49    ( ! [X0,X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => (k7_relat_1(X0,sK4) != k7_relat_1(X1,sK4) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,sK4)) & k1_relat_1(X0) = k1_relat_1(X1))) )),
% 7.74/1.49    introduced(choice_axiom,[])).
% 7.74/1.49  
% 7.74/1.49  fof(f33,plain,(
% 7.74/1.49    ( ! [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK3,X2) != k7_relat_1(X0,X2) & ! [X3] : (k1_funct_1(sK3,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK3) = k1_relat_1(X0)) & v1_funct_1(sK3) & v1_relat_1(sK3))) )),
% 7.74/1.49    introduced(choice_axiom,[])).
% 7.74/1.49  
% 7.74/1.49  fof(f32,plain,(
% 7.74/1.49    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(sK2,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(sK2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK2) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 7.74/1.49    introduced(choice_axiom,[])).
% 7.74/1.49  
% 7.74/1.49  fof(f35,plain,(
% 7.74/1.49    ((k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4) & ! [X3] : (k1_funct_1(sK2,X3) = k1_funct_1(sK3,X3) | ~r2_hidden(X3,sK4)) & k1_relat_1(sK2) = k1_relat_1(sK3)) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 7.74/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f34,f33,f32])).
% 7.74/1.49  
% 7.74/1.49  fof(f53,plain,(
% 7.74/1.49    v1_relat_1(sK2)),
% 7.74/1.49    inference(cnf_transformation,[],[f35])).
% 7.74/1.49  
% 7.74/1.49  fof(f7,axiom,(
% 7.74/1.49    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f16,plain,(
% 7.74/1.49    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.74/1.49    inference(ennf_transformation,[],[f7])).
% 7.74/1.49  
% 7.74/1.49  fof(f44,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f16])).
% 7.74/1.49  
% 7.74/1.49  fof(f3,axiom,(
% 7.74/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f38,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f3])).
% 7.74/1.49  
% 7.74/1.49  fof(f2,axiom,(
% 7.74/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f37,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f2])).
% 7.74/1.49  
% 7.74/1.49  fof(f60,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 7.74/1.49    inference(definition_unfolding,[],[f38,f37])).
% 7.74/1.49  
% 7.74/1.49  fof(f62,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.74/1.49    inference(definition_unfolding,[],[f44,f60])).
% 7.74/1.49  
% 7.74/1.49  fof(f55,plain,(
% 7.74/1.49    v1_relat_1(sK3)),
% 7.74/1.49    inference(cnf_transformation,[],[f35])).
% 7.74/1.49  
% 7.74/1.49  fof(f57,plain,(
% 7.74/1.49    k1_relat_1(sK2) = k1_relat_1(sK3)),
% 7.74/1.49    inference(cnf_transformation,[],[f35])).
% 7.74/1.49  
% 7.74/1.49  fof(f6,axiom,(
% 7.74/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f15,plain,(
% 7.74/1.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.74/1.49    inference(ennf_transformation,[],[f6])).
% 7.74/1.49  
% 7.74/1.49  fof(f43,plain,(
% 7.74/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f15])).
% 7.74/1.49  
% 7.74/1.49  fof(f10,axiom,(
% 7.74/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f20,plain,(
% 7.74/1.49    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | (~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.74/1.49    inference(ennf_transformation,[],[f10])).
% 7.74/1.49  
% 7.74/1.49  fof(f21,plain,(
% 7.74/1.49    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.74/1.49    inference(flattening,[],[f20])).
% 7.74/1.49  
% 7.74/1.49  fof(f28,plain,(
% 7.74/1.49    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.74/1.49    inference(nnf_transformation,[],[f21])).
% 7.74/1.49  
% 7.74/1.49  fof(f29,plain,(
% 7.74/1.49    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.74/1.49    inference(rectify,[],[f28])).
% 7.74/1.49  
% 7.74/1.49  fof(f30,plain,(
% 7.74/1.49    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK1(X0,X1,X2)) != k1_funct_1(X1,sK1(X0,X1,X2)) & r2_hidden(sK1(X0,X1,X2),X2)))),
% 7.74/1.49    introduced(choice_axiom,[])).
% 7.74/1.49  
% 7.74/1.49  fof(f31,plain,(
% 7.74/1.49    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | (k1_funct_1(X0,sK1(X0,X1,X2)) != k1_funct_1(X1,sK1(X0,X1,X2)) & r2_hidden(sK1(X0,X1,X2),X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.74/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 7.74/1.49  
% 7.74/1.49  fof(f51,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f31])).
% 7.74/1.49  
% 7.74/1.49  fof(f5,axiom,(
% 7.74/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f14,plain,(
% 7.74/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 7.74/1.49    inference(ennf_transformation,[],[f5])).
% 7.74/1.49  
% 7.74/1.49  fof(f24,plain,(
% 7.74/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 7.74/1.49    inference(nnf_transformation,[],[f14])).
% 7.74/1.49  
% 7.74/1.49  fof(f25,plain,(
% 7.74/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 7.74/1.49    inference(flattening,[],[f24])).
% 7.74/1.49  
% 7.74/1.49  fof(f40,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f25])).
% 7.74/1.49  
% 7.74/1.49  fof(f58,plain,(
% 7.74/1.49    ( ! [X3] : (k1_funct_1(sK2,X3) = k1_funct_1(sK3,X3) | ~r2_hidden(X3,sK4)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f35])).
% 7.74/1.49  
% 7.74/1.49  fof(f56,plain,(
% 7.74/1.49    v1_funct_1(sK3)),
% 7.74/1.49    inference(cnf_transformation,[],[f35])).
% 7.74/1.49  
% 7.74/1.49  fof(f9,axiom,(
% 7.74/1.49    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = k1_xboole_0) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f19,plain,(
% 7.74/1.49    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = k1_xboole_0 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.74/1.49    inference(ennf_transformation,[],[f9])).
% 7.74/1.49  
% 7.74/1.49  fof(f26,plain,(
% 7.74/1.49    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = k1_xboole_0 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_funct_1(sK0(X0),X2) = k1_xboole_0 | ~r2_hidden(X2,X0)) & k1_relat_1(sK0(X0)) = X0 & v1_funct_1(sK0(X0)) & v1_relat_1(sK0(X0))))),
% 7.74/1.49    introduced(choice_axiom,[])).
% 7.74/1.49  
% 7.74/1.49  fof(f27,plain,(
% 7.74/1.49    ! [X0] : (! [X2] : (k1_funct_1(sK0(X0),X2) = k1_xboole_0 | ~r2_hidden(X2,X0)) & k1_relat_1(sK0(X0)) = X0 & v1_funct_1(sK0(X0)) & v1_relat_1(sK0(X0)))),
% 7.74/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f26])).
% 7.74/1.49  
% 7.74/1.49  fof(f46,plain,(
% 7.74/1.49    ( ! [X0] : (v1_relat_1(sK0(X0))) )),
% 7.74/1.49    inference(cnf_transformation,[],[f27])).
% 7.74/1.49  
% 7.74/1.49  fof(f4,axiom,(
% 7.74/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f13,plain,(
% 7.74/1.49    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.74/1.49    inference(ennf_transformation,[],[f4])).
% 7.74/1.49  
% 7.74/1.49  fof(f39,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f13])).
% 7.74/1.49  
% 7.74/1.49  fof(f48,plain,(
% 7.74/1.49    ( ! [X0] : (k1_relat_1(sK0(X0)) = X0) )),
% 7.74/1.49    inference(cnf_transformation,[],[f27])).
% 7.74/1.49  
% 7.74/1.49  fof(f1,axiom,(
% 7.74/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.74/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.74/1.49  
% 7.74/1.49  fof(f36,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f1])).
% 7.74/1.49  
% 7.74/1.49  fof(f61,plain,(
% 7.74/1.49    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0))) )),
% 7.74/1.49    inference(definition_unfolding,[],[f36,f60,f60])).
% 7.74/1.49  
% 7.74/1.49  fof(f54,plain,(
% 7.74/1.49    v1_funct_1(sK2)),
% 7.74/1.49    inference(cnf_transformation,[],[f35])).
% 7.74/1.49  
% 7.74/1.49  fof(f59,plain,(
% 7.74/1.49    k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4)),
% 7.74/1.49    inference(cnf_transformation,[],[f35])).
% 7.74/1.49  
% 7.74/1.49  fof(f52,plain,(
% 7.74/1.49    ( ! [X2,X0,X1] : (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | k1_funct_1(X0,sK1(X0,X1,X2)) != k1_funct_1(X1,sK1(X0,X1,X2)) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.74/1.49    inference(cnf_transformation,[],[f31])).
% 7.74/1.49  
% 7.74/1.49  cnf(c_21,negated_conjecture,
% 7.74/1.49      ( v1_relat_1(sK2) ),
% 7.74/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_547,plain,
% 7.74/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_6,plain,
% 7.74/1.49      ( ~ v1_relat_1(X0)
% 7.74/1.49      | k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 7.74/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_559,plain,
% 7.74/1.49      ( k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 7.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1356,plain,
% 7.74/1.49      ( k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_547,c_559]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_19,negated_conjecture,
% 7.74/1.49      ( v1_relat_1(sK3) ),
% 7.74/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_549,plain,
% 7.74/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1355,plain,
% 7.74/1.49      ( k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_549,c_559]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_17,negated_conjecture,
% 7.74/1.49      ( k1_relat_1(sK2) = k1_relat_1(sK3) ),
% 7.74/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1398,plain,
% 7.74/1.49      ( k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 7.74/1.49      inference(light_normalisation,[status(thm)],[c_1355,c_17]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2265,plain,
% 7.74/1.49      ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_1356,c_1398]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_5,plain,
% 7.74/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
% 7.74/1.49      | ~ v1_relat_1(X0) ),
% 7.74/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_560,plain,
% 7.74/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 7.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1098,plain,
% 7.74/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK2)) = iProver_top
% 7.74/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_17,c_560]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_24,plain,
% 7.74/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_806,plain,
% 7.74/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK3))
% 7.74/1.49      | ~ v1_relat_1(sK3) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_807,plain,
% 7.74/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK3)) = iProver_top
% 7.74/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_221,plain,
% 7.74/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.74/1.49      theory(equality) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_736,plain,
% 7.74/1.49      ( r1_tarski(X0,X1)
% 7.74/1.49      | ~ r1_tarski(k1_relat_1(k7_relat_1(X2,X3)),k1_relat_1(X2))
% 7.74/1.49      | X1 != k1_relat_1(X2)
% 7.74/1.49      | X0 != k1_relat_1(k7_relat_1(X2,X3)) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_221]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_784,plain,
% 7.74/1.49      ( r1_tarski(X0,k1_relat_1(sK2))
% 7.74/1.49      | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),k1_relat_1(sK3))
% 7.74/1.49      | X0 != k1_relat_1(k7_relat_1(sK3,X1))
% 7.74/1.49      | k1_relat_1(sK2) != k1_relat_1(sK3) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_736]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_952,plain,
% 7.74/1.49      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK3))
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK2))
% 7.74/1.49      | k1_relat_1(k7_relat_1(sK3,X0)) != k1_relat_1(k7_relat_1(sK3,X0))
% 7.74/1.49      | k1_relat_1(sK2) != k1_relat_1(sK3) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_784]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_954,plain,
% 7.74/1.49      ( k1_relat_1(k7_relat_1(sK3,X0)) != k1_relat_1(k7_relat_1(sK3,X0))
% 7.74/1.49      | k1_relat_1(sK2) != k1_relat_1(sK3)
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK3)) != iProver_top
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK2)) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_952]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_213,plain,( X0 = X0 ),theory(equality) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_790,plain,
% 7.74/1.49      ( k1_relat_1(X0) = k1_relat_1(X0) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_213]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_953,plain,
% 7.74/1.49      ( k1_relat_1(k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_790]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1212,plain,
% 7.74/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK2)) = iProver_top ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_1098,c_24,c_17,c_807,c_954,c_953]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2292,plain,
% 7.74/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK2)) = iProver_top ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_2265,c_1212]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_13,plain,
% 7.74/1.49      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.74/1.49      | ~ r1_tarski(X0,k1_relat_1(X2))
% 7.74/1.49      | r2_hidden(sK1(X2,X1,X0),X0)
% 7.74/1.49      | ~ v1_funct_1(X1)
% 7.74/1.49      | ~ v1_funct_1(X2)
% 7.74/1.49      | ~ v1_relat_1(X1)
% 7.74/1.49      | ~ v1_relat_1(X2)
% 7.74/1.49      | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
% 7.74/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_553,plain,
% 7.74/1.49      ( k7_relat_1(X0,X1) = k7_relat_1(X2,X1)
% 7.74/1.49      | r1_tarski(X1,k1_relat_1(X2)) != iProver_top
% 7.74/1.49      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.74/1.49      | r2_hidden(sK1(X0,X2,X1),X1) = iProver_top
% 7.74/1.49      | v1_funct_1(X2) != iProver_top
% 7.74/1.49      | v1_funct_1(X0) != iProver_top
% 7.74/1.49      | v1_relat_1(X2) != iProver_top
% 7.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_4,plain,
% 7.74/1.49      ( r2_hidden(X0,X1)
% 7.74/1.49      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 7.74/1.49      | ~ v1_relat_1(X2) ),
% 7.74/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_561,plain,
% 7.74/1.49      ( r2_hidden(X0,X1) = iProver_top
% 7.74/1.49      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
% 7.74/1.49      | v1_relat_1(X2) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2157,plain,
% 7.74/1.49      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X3,k1_relat_1(k7_relat_1(X1,X2)))
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X3)) != iProver_top
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X0)) != iProver_top
% 7.74/1.49      | r2_hidden(sK1(X3,X0,k1_relat_1(k7_relat_1(X1,X2))),X2) = iProver_top
% 7.74/1.49      | v1_funct_1(X3) != iProver_top
% 7.74/1.49      | v1_funct_1(X0) != iProver_top
% 7.74/1.49      | v1_relat_1(X1) != iProver_top
% 7.74/1.49      | v1_relat_1(X3) != iProver_top
% 7.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_553,c_561]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_16,negated_conjecture,
% 7.74/1.49      ( ~ r2_hidden(X0,sK4) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
% 7.74/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_551,plain,
% 7.74/1.49      ( k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
% 7.74/1.49      | r2_hidden(X0,sK4) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_31164,plain,
% 7.74/1.49      ( k1_funct_1(sK3,sK1(X0,X1,k1_relat_1(k7_relat_1(X2,sK4)))) = k1_funct_1(sK2,sK1(X0,X1,k1_relat_1(k7_relat_1(X2,sK4))))
% 7.74/1.49      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X2,sK4))) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,sK4)))
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(X2,sK4)),k1_relat_1(X0)) != iProver_top
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(X2,sK4)),k1_relat_1(X1)) != iProver_top
% 7.74/1.49      | v1_funct_1(X0) != iProver_top
% 7.74/1.49      | v1_funct_1(X1) != iProver_top
% 7.74/1.49      | v1_relat_1(X2) != iProver_top
% 7.74/1.49      | v1_relat_1(X0) != iProver_top
% 7.74/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_2157,c_551]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_32723,plain,
% 7.74/1.49      ( k1_funct_1(sK2,sK1(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK1(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4))))
% 7.74/1.49      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.74/1.49      | v1_funct_1(X0) != iProver_top
% 7.74/1.49      | v1_funct_1(sK3) != iProver_top
% 7.74/1.49      | v1_relat_1(X0) != iProver_top
% 7.74/1.49      | v1_relat_1(X1) != iProver_top
% 7.74/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_17,c_31164]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_18,negated_conjecture,
% 7.74/1.49      ( v1_funct_1(sK3) ),
% 7.74/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_25,plain,
% 7.74/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_33137,plain,
% 7.74/1.49      ( v1_relat_1(X1) != iProver_top
% 7.74/1.49      | v1_relat_1(X0) != iProver_top
% 7.74/1.49      | k1_funct_1(sK2,sK1(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK1(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4))))
% 7.74/1.49      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.74/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_32723,c_24,c_25]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_33138,plain,
% 7.74/1.49      ( k1_funct_1(sK2,sK1(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK1(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4))))
% 7.74/1.49      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.74/1.49      | v1_funct_1(X0) != iProver_top
% 7.74/1.49      | v1_relat_1(X1) != iProver_top
% 7.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.74/1.49      inference(renaming,[status(thm)],[c_33137]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_33152,plain,
% 7.74/1.49      ( k1_funct_1(sK3,sK1(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK1(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4))))
% 7.74/1.49      | k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,sK4))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK4)))
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top
% 7.74/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_2292,c_33138]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_11,plain,
% 7.74/1.49      ( v1_relat_1(sK0(X0)) ),
% 7.74/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_555,plain,
% 7.74/1.49      ( v1_relat_1(sK0(X0)) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1,plain,
% 7.74/1.49      ( ~ v1_relat_1(X0)
% 7.74/1.49      | ~ v1_relat_1(X1)
% 7.74/1.49      | k7_relat_1(X1,k1_relat_1(k7_relat_1(X0,k1_relat_1(X1)))) = k7_relat_1(X1,k1_relat_1(X0)) ),
% 7.74/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_564,plain,
% 7.74/1.49      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1))
% 7.74/1.49      | v1_relat_1(X0) != iProver_top
% 7.74/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_5490,plain,
% 7.74/1.49      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(sK0(X1),k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(sK0(X1)))
% 7.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_555,c_564]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_9,plain,
% 7.74/1.49      ( k1_relat_1(sK0(X0)) = X0 ),
% 7.74/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_5503,plain,
% 7.74/1.49      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(sK0(X1),k1_relat_1(X0)))) = k7_relat_1(X0,X1)
% 7.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_5490,c_9]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_5766,plain,
% 7.74/1.49      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK0(X0),k1_relat_1(sK2)))) = k7_relat_1(sK2,X0) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_547,c_5503]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_0,plain,
% 7.74/1.49      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
% 7.74/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1354,plain,
% 7.74/1.49      ( k1_setfam_1(k1_enumset1(k1_relat_1(sK0(X0)),k1_relat_1(sK0(X0)),X1)) = k1_relat_1(k7_relat_1(sK0(X0),X1)) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_555,c_559]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1363,plain,
% 7.74/1.49      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(sK0(X0),X1)) ),
% 7.74/1.49      inference(light_normalisation,[status(thm)],[c_1354,c_9]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_1377,plain,
% 7.74/1.49      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(sK0(X1),X0)) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_0,c_1363]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_2272,plain,
% 7.74/1.49      ( k1_relat_1(k7_relat_1(sK0(X0),k1_relat_1(sK2))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_1356,c_1377]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_5768,plain,
% 7.74/1.49      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) = k7_relat_1(sK2,X0) ),
% 7.74/1.49      inference(light_normalisation,[status(thm)],[c_5766,c_2272]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_5765,plain,
% 7.74/1.49      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK0(X0),k1_relat_1(sK3)))) = k7_relat_1(sK3,X0) ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_549,c_5503]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_5771,plain,
% 7.74/1.49      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,X0))) = k7_relat_1(sK3,X0) ),
% 7.74/1.49      inference(light_normalisation,[status(thm)],[c_5765,c_17,c_2272]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_33399,plain,
% 7.74/1.49      ( k1_funct_1(sK3,sK1(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK1(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4))))
% 7.74/1.49      | k7_relat_1(sK3,sK4) = k7_relat_1(sK2,sK4)
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top
% 7.74/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_33152,c_5768,c_5771]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_22,plain,
% 7.74/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_20,negated_conjecture,
% 7.74/1.49      ( v1_funct_1(sK2) ),
% 7.74/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_23,plain,
% 7.74/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_15,negated_conjecture,
% 7.74/1.49      ( k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4) ),
% 7.74/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_214,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_734,plain,
% 7.74/1.49      ( k7_relat_1(sK3,sK4) != X0
% 7.74/1.49      | k7_relat_1(sK2,sK4) != X0
% 7.74/1.49      | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_214]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_754,plain,
% 7.74/1.49      ( k7_relat_1(sK3,sK4) != k7_relat_1(X0,sK4)
% 7.74/1.49      | k7_relat_1(sK2,sK4) != k7_relat_1(X0,sK4)
% 7.74/1.49      | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_734]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_757,plain,
% 7.74/1.49      ( k7_relat_1(sK3,sK4) != k7_relat_1(sK2,sK4)
% 7.74/1.49      | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4)
% 7.74/1.49      | k7_relat_1(sK2,sK4) != k7_relat_1(sK2,sK4) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_754]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_22268,plain,
% 7.74/1.49      ( k7_relat_1(sK2,sK4) = k7_relat_1(sK2,sK4) ),
% 7.74/1.49      inference(instantiation,[status(thm)],[c_213]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_33635,plain,
% 7.74/1.49      ( k1_funct_1(sK3,sK1(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK1(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4))))
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_33399,c_22,c_23,c_15,c_757,c_22268]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_33641,plain,
% 7.74/1.49      ( k1_funct_1(sK3,sK1(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK1(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) ),
% 7.74/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_33635,c_2292]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_12,plain,
% 7.74/1.49      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.74/1.49      | ~ r1_tarski(X0,k1_relat_1(X2))
% 7.74/1.49      | ~ v1_funct_1(X1)
% 7.74/1.49      | ~ v1_funct_1(X2)
% 7.74/1.49      | ~ v1_relat_1(X1)
% 7.74/1.49      | ~ v1_relat_1(X2)
% 7.74/1.49      | k1_funct_1(X1,sK1(X2,X1,X0)) != k1_funct_1(X2,sK1(X2,X1,X0))
% 7.74/1.49      | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
% 7.74/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_554,plain,
% 7.74/1.49      ( k1_funct_1(X0,sK1(X1,X0,X2)) != k1_funct_1(X1,sK1(X1,X0,X2))
% 7.74/1.49      | k7_relat_1(X1,X2) = k7_relat_1(X0,X2)
% 7.74/1.49      | r1_tarski(X2,k1_relat_1(X0)) != iProver_top
% 7.74/1.49      | r1_tarski(X2,k1_relat_1(X1)) != iProver_top
% 7.74/1.49      | v1_funct_1(X0) != iProver_top
% 7.74/1.49      | v1_funct_1(X1) != iProver_top
% 7.74/1.49      | v1_relat_1(X0) != iProver_top
% 7.74/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.74/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_33642,plain,
% 7.74/1.49      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,sK4))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK4)))
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK3)) != iProver_top
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.74/1.49      | v1_funct_1(sK3) != iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top
% 7.74/1.49      | v1_relat_1(sK3) != iProver_top
% 7.74/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.74/1.49      inference(superposition,[status(thm)],[c_33641,c_554]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_33643,plain,
% 7.74/1.49      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,sK4))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK4)))
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.74/1.49      | v1_funct_1(sK3) != iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top
% 7.74/1.49      | v1_relat_1(sK3) != iProver_top
% 7.74/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.74/1.49      inference(light_normalisation,[status(thm)],[c_33642,c_17]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_33644,plain,
% 7.74/1.49      ( k7_relat_1(sK3,sK4) = k7_relat_1(sK2,sK4)
% 7.74/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.74/1.49      | v1_funct_1(sK3) != iProver_top
% 7.74/1.49      | v1_funct_1(sK2) != iProver_top
% 7.74/1.49      | v1_relat_1(sK3) != iProver_top
% 7.74/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.74/1.49      inference(demodulation,[status(thm)],[c_33643,c_5768,c_5771]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_33647,plain,
% 7.74/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top ),
% 7.74/1.49      inference(global_propositional_subsumption,
% 7.74/1.49                [status(thm)],
% 7.74/1.49                [c_33644,c_22,c_23,c_24,c_25,c_15,c_757,c_22268]) ).
% 7.74/1.49  
% 7.74/1.49  cnf(c_33652,plain,
% 7.74/1.49      ( $false ),
% 7.74/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_33647,c_2292]) ).
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.74/1.49  
% 7.74/1.49  ------                               Statistics
% 7.74/1.49  
% 7.74/1.49  ------ General
% 7.74/1.49  
% 7.74/1.49  abstr_ref_over_cycles:                  0
% 7.74/1.49  abstr_ref_under_cycles:                 0
% 7.74/1.49  gc_basic_clause_elim:                   0
% 7.74/1.49  forced_gc_time:                         0
% 7.74/1.49  parsing_time:                           0.01
% 7.74/1.49  unif_index_cands_time:                  0.
% 7.74/1.49  unif_index_add_time:                    0.
% 7.74/1.49  orderings_time:                         0.
% 7.74/1.49  out_proof_time:                         0.011
% 7.74/1.49  total_time:                             0.912
% 7.74/1.49  num_of_symbols:                         46
% 7.74/1.49  num_of_terms:                           32352
% 7.74/1.49  
% 7.74/1.49  ------ Preprocessing
% 7.74/1.49  
% 7.74/1.49  num_of_splits:                          0
% 7.74/1.49  num_of_split_atoms:                     0
% 7.74/1.49  num_of_reused_defs:                     0
% 7.74/1.49  num_eq_ax_congr_red:                    10
% 7.74/1.49  num_of_sem_filtered_clauses:            1
% 7.74/1.49  num_of_subtypes:                        0
% 7.74/1.49  monotx_restored_types:                  0
% 7.74/1.49  sat_num_of_epr_types:                   0
% 7.74/1.49  sat_num_of_non_cyclic_types:            0
% 7.74/1.49  sat_guarded_non_collapsed_types:        0
% 7.74/1.49  num_pure_diseq_elim:                    0
% 7.74/1.49  simp_replaced_by:                       0
% 7.74/1.49  res_preprocessed:                       89
% 7.74/1.49  prep_upred:                             0
% 7.74/1.49  prep_unflattend:                        0
% 7.74/1.49  smt_new_axioms:                         0
% 7.74/1.49  pred_elim_cands:                        4
% 7.74/1.49  pred_elim:                              0
% 7.74/1.49  pred_elim_cl:                           0
% 7.74/1.49  pred_elim_cycles:                       1
% 7.74/1.49  merged_defs:                            0
% 7.74/1.49  merged_defs_ncl:                        0
% 7.74/1.49  bin_hyper_res:                          0
% 7.74/1.49  prep_cycles:                            3
% 7.74/1.49  pred_elim_time:                         0.
% 7.74/1.49  splitting_time:                         0.
% 7.74/1.49  sem_filter_time:                        0.
% 7.74/1.49  monotx_time:                            0.
% 7.74/1.49  subtype_inf_time:                       0.
% 7.74/1.49  
% 7.74/1.49  ------ Problem properties
% 7.74/1.49  
% 7.74/1.49  clauses:                                22
% 7.74/1.49  conjectures:                            7
% 7.74/1.49  epr:                                    4
% 7.74/1.49  horn:                                   21
% 7.74/1.49  ground:                                 6
% 7.74/1.49  unary:                                  10
% 7.74/1.49  binary:                                 4
% 7.74/1.49  lits:                                   59
% 7.74/1.49  lits_eq:                                14
% 7.74/1.49  fd_pure:                                0
% 7.74/1.49  fd_pseudo:                              0
% 7.74/1.49  fd_cond:                                0
% 7.74/1.49  fd_pseudo_cond:                         0
% 7.74/1.49  ac_symbols:                             0
% 7.74/1.49  
% 7.74/1.49  ------ Propositional Solver
% 7.74/1.49  
% 7.74/1.49  prop_solver_calls:                      28
% 7.74/1.49  prop_fast_solver_calls:                 1600
% 7.74/1.49  smt_solver_calls:                       0
% 7.74/1.49  smt_fast_solver_calls:                  0
% 7.74/1.49  prop_num_of_clauses:                    8162
% 7.74/1.49  prop_preprocess_simplified:             16098
% 7.74/1.49  prop_fo_subsumed:                       97
% 7.74/1.49  prop_solver_time:                       0.
% 7.74/1.49  smt_solver_time:                        0.
% 7.74/1.49  smt_fast_solver_time:                   0.
% 7.74/1.49  prop_fast_solver_time:                  0.
% 7.74/1.49  prop_unsat_core_time:                   0.
% 7.74/1.49  
% 7.74/1.49  ------ QBF
% 7.74/1.49  
% 7.74/1.49  qbf_q_res:                              0
% 7.74/1.49  qbf_num_tautologies:                    0
% 7.74/1.49  qbf_prep_cycles:                        0
% 7.74/1.49  
% 7.74/1.49  ------ BMC1
% 7.74/1.49  
% 7.74/1.49  bmc1_current_bound:                     -1
% 7.74/1.49  bmc1_last_solved_bound:                 -1
% 7.74/1.49  bmc1_unsat_core_size:                   -1
% 7.74/1.49  bmc1_unsat_core_parents_size:           -1
% 7.74/1.49  bmc1_merge_next_fun:                    0
% 7.74/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.74/1.49  
% 7.74/1.49  ------ Instantiation
% 7.74/1.49  
% 7.74/1.49  inst_num_of_clauses:                    2382
% 7.74/1.49  inst_num_in_passive:                    1357
% 7.74/1.49  inst_num_in_active:                     910
% 7.74/1.49  inst_num_in_unprocessed:                115
% 7.74/1.49  inst_num_of_loops:                      960
% 7.74/1.49  inst_num_of_learning_restarts:          0
% 7.74/1.49  inst_num_moves_active_passive:          45
% 7.74/1.49  inst_lit_activity:                      0
% 7.74/1.49  inst_lit_activity_moves:                0
% 7.74/1.49  inst_num_tautologies:                   0
% 7.74/1.49  inst_num_prop_implied:                  0
% 7.74/1.49  inst_num_existing_simplified:           0
% 7.74/1.49  inst_num_eq_res_simplified:             0
% 7.74/1.49  inst_num_child_elim:                    0
% 7.74/1.49  inst_num_of_dismatching_blockings:      6553
% 7.74/1.49  inst_num_of_non_proper_insts:           4502
% 7.74/1.49  inst_num_of_duplicates:                 0
% 7.74/1.49  inst_inst_num_from_inst_to_res:         0
% 7.74/1.49  inst_dismatching_checking_time:         0.
% 7.74/1.49  
% 7.74/1.49  ------ Resolution
% 7.74/1.49  
% 7.74/1.49  res_num_of_clauses:                     0
% 7.74/1.49  res_num_in_passive:                     0
% 7.74/1.49  res_num_in_active:                      0
% 7.74/1.49  res_num_of_loops:                       92
% 7.74/1.49  res_forward_subset_subsumed:            359
% 7.74/1.49  res_backward_subset_subsumed:           4
% 7.74/1.49  res_forward_subsumed:                   0
% 7.74/1.49  res_backward_subsumed:                  0
% 7.74/1.49  res_forward_subsumption_resolution:     0
% 7.74/1.49  res_backward_subsumption_resolution:    0
% 7.74/1.49  res_clause_to_clause_subsumption:       3175
% 7.74/1.49  res_orphan_elimination:                 0
% 7.74/1.49  res_tautology_del:                      526
% 7.74/1.49  res_num_eq_res_simplified:              0
% 7.74/1.49  res_num_sel_changes:                    0
% 7.74/1.49  res_moves_from_active_to_pass:          0
% 7.74/1.49  
% 7.74/1.49  ------ Superposition
% 7.74/1.49  
% 7.74/1.49  sup_time_total:                         0.
% 7.74/1.49  sup_time_generating:                    0.
% 7.74/1.49  sup_time_sim_full:                      0.
% 7.74/1.49  sup_time_sim_immed:                     0.
% 7.74/1.49  
% 7.74/1.49  sup_num_of_clauses:                     654
% 7.74/1.49  sup_num_in_active:                      179
% 7.74/1.49  sup_num_in_passive:                     475
% 7.74/1.49  sup_num_of_loops:                       191
% 7.74/1.49  sup_fw_superposition:                   1153
% 7.74/1.49  sup_bw_superposition:                   342
% 7.74/1.49  sup_immediate_simplified:               531
% 7.74/1.49  sup_given_eliminated:                   1
% 7.74/1.49  comparisons_done:                       0
% 7.74/1.49  comparisons_avoided:                    199
% 7.74/1.49  
% 7.74/1.49  ------ Simplifications
% 7.74/1.49  
% 7.74/1.49  
% 7.74/1.49  sim_fw_subset_subsumed:                 32
% 7.74/1.49  sim_bw_subset_subsumed:                 13
% 7.74/1.49  sim_fw_subsumed:                        91
% 7.74/1.49  sim_bw_subsumed:                        25
% 7.74/1.49  sim_fw_subsumption_res:                 39
% 7.74/1.49  sim_bw_subsumption_res:                 2
% 7.74/1.49  sim_tautology_del:                      39
% 7.74/1.49  sim_eq_tautology_del:                   53
% 7.74/1.49  sim_eq_res_simp:                        0
% 7.74/1.49  sim_fw_demodulated:                     196
% 7.74/1.49  sim_bw_demodulated:                     12
% 7.74/1.49  sim_light_normalised:                   291
% 7.74/1.49  sim_joinable_taut:                      0
% 7.74/1.49  sim_joinable_simp:                      0
% 7.74/1.49  sim_ac_normalised:                      0
% 7.74/1.49  sim_smt_subsumption:                    0
% 7.74/1.49  
%------------------------------------------------------------------------------
