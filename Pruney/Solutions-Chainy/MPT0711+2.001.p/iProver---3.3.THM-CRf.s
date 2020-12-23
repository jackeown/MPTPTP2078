%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:42 EST 2020

% Result     : Theorem 11.63s
% Output     : CNFRefutation 11.63s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 724 expanded)
%              Number of clauses        :   64 ( 184 expanded)
%              Number of leaves         :   15 ( 218 expanded)
%              Depth                    :   25
%              Number of atoms          :  422 (3835 expanded)
%              Number of equality atoms :  227 (1726 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f24])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
          & ! [X3] :
              ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
              | ~ r2_hidden(X3,X2) )
          & k1_relat_1(X0) = k1_relat_1(X1) )
     => ( k7_relat_1(X0,sK5) != k7_relat_1(X1,sK5)
        & ! [X3] :
            ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,sK5) )
        & k1_relat_1(X0) = k1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
            ( k7_relat_1(sK4,X2) != k7_relat_1(X0,X2)
            & ! [X3] :
                ( k1_funct_1(sK4,X3) = k1_funct_1(X0,X3)
                | ~ r2_hidden(X3,X2) )
            & k1_relat_1(sK4) = k1_relat_1(X0) )
        & v1_funct_1(sK4)
        & v1_relat_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
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
              ( k7_relat_1(sK3,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(sK3,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(sK3) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k7_relat_1(sK3,sK5) != k7_relat_1(sK4,sK5)
    & ! [X3] :
        ( k1_funct_1(sK3,X3) = k1_funct_1(sK4,X3)
        | ~ r2_hidden(X3,sK5) )
    & k1_relat_1(sK3) = k1_relat_1(sK4)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f36,f35,f34])).

fof(f56,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f41])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f58,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    k1_relat_1(sK3) = k1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) != k1_funct_1(X1,sK2(X0,X1,X2))
        & r2_hidden(sK2(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ( k1_funct_1(X0,sK2(X0,X1,X2)) != k1_funct_1(X1,sK2(X0,X1,X2))
                    & r2_hidden(sK2(X0,X1,X2),X2) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,X3) = k1_funct_1(sK4,X3)
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    k7_relat_1(sK3,sK5) != k7_relat_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | k1_funct_1(X0,sK2(X0,X1,X2)) != k1_funct_1(X1,sK2(X0,X1,X2))
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_595,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_578,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_589,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1034,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_578,c_589])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_580,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1033,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_580,c_589])).

cnf(c_18,negated_conjecture,
    ( k1_relat_1(sK3) = k1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1064,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1033,c_18])).

cnf(c_1125,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_1034,c_1064])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_591,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2398,plain,
    ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK3,X1))) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1125,c_591])).

cnf(c_2414,plain,
    ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK3,X1))) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2398,c_18])).

cnf(c_25,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2461,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(sK3,X1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2414,c_25])).

cnf(c_2462,plain,
    ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK3,X1))) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2461])).

cnf(c_2469,plain,
    ( r2_hidden(sK0(k1_relat_1(k7_relat_1(sK3,X0)),X1),k1_relat_1(sK3)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_595,c_2462])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_596,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2571,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2469,c_596])).

cnf(c_14,plain,
    ( r2_hidden(sK2(X0,X1,X2),X2)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_584,plain,
    ( k7_relat_1(X0,X1) = k7_relat_1(X2,X1)
    | r2_hidden(sK2(X0,X2,X1),X1) = iProver_top
    | r1_tarski(X1,k1_relat_1(X2)) != iProver_top
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_590,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2233,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X3,k1_relat_1(k7_relat_1(X1,X2)))
    | r2_hidden(sK2(X3,X0,k1_relat_1(k7_relat_1(X1,X2))),X2) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X3)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_584,c_590])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_582,plain,
    ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_30754,plain,
    ( k1_funct_1(sK4,sK2(X0,X1,k1_relat_1(k7_relat_1(X2,sK5)))) = k1_funct_1(sK3,sK2(X0,X1,k1_relat_1(k7_relat_1(X2,sK5))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X2,sK5))) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,sK5)))
    | r1_tarski(k1_relat_1(k7_relat_1(X2,sK5)),k1_relat_1(X1)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X2,sK5)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2233,c_582])).

cnf(c_36379,plain,
    ( k1_funct_1(sK3,sK2(X0,sK4,k1_relat_1(k7_relat_1(X1,sK5)))) = k1_funct_1(sK4,sK2(X0,sK4,k1_relat_1(k7_relat_1(X1,sK5))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK5))) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(X1,sK5)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK5)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK5)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_30754])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_37136,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | k1_funct_1(sK3,sK2(X0,sK4,k1_relat_1(k7_relat_1(X1,sK5)))) = k1_funct_1(sK4,sK2(X0,sK4,k1_relat_1(k7_relat_1(X1,sK5))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK5))) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(X1,sK5)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK5)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK5)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36379,c_25,c_26])).

cnf(c_37137,plain,
    ( k1_funct_1(sK3,sK2(X0,sK4,k1_relat_1(k7_relat_1(X1,sK5)))) = k1_funct_1(sK4,sK2(X0,sK4,k1_relat_1(k7_relat_1(X1,sK5))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK5))) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(X1,sK5)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK5)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK5)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_37136])).

cnf(c_37151,plain,
    ( k1_funct_1(sK4,sK2(sK3,sK4,k1_relat_1(k7_relat_1(sK3,sK5)))) = k1_funct_1(sK3,sK2(sK3,sK4,k1_relat_1(k7_relat_1(sK3,sK5))))
    | k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK5))) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK3,sK5)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK5)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2571,c_37137])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_593,plain,
    ( k7_relat_1(X0,k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1416,plain,
    ( k7_relat_1(sK3,k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),X0))) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_578,c_593])).

cnf(c_1418,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0))) = k7_relat_1(sK3,X0) ),
    inference(light_normalisation,[status(thm)],[c_1416,c_1034])).

cnf(c_1415,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k1_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),X0))) = k7_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_580,c_593])).

cnf(c_1421,plain,
    ( k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK3,X0))) = k7_relat_1(sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_1415,c_18,c_1034])).

cnf(c_37574,plain,
    ( k1_funct_1(sK4,sK2(sK3,sK4,k1_relat_1(k7_relat_1(sK3,sK5)))) = k1_funct_1(sK3,sK2(sK3,sK4,k1_relat_1(k7_relat_1(sK3,sK5))))
    | k7_relat_1(sK4,sK5) = k7_relat_1(sK3,sK5)
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK5)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_37151,c_1418,c_1421])).

cnf(c_23,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_24,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,negated_conjecture,
    ( k7_relat_1(sK3,sK5) != k7_relat_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_227,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_765,plain,
    ( k7_relat_1(sK4,sK5) != X0
    | k7_relat_1(sK3,sK5) != X0
    | k7_relat_1(sK3,sK5) = k7_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_794,plain,
    ( k7_relat_1(sK4,sK5) != k7_relat_1(X0,sK5)
    | k7_relat_1(sK3,sK5) != k7_relat_1(X0,sK5)
    | k7_relat_1(sK3,sK5) = k7_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_796,plain,
    ( k7_relat_1(sK4,sK5) != k7_relat_1(sK3,sK5)
    | k7_relat_1(sK3,sK5) = k7_relat_1(sK4,sK5)
    | k7_relat_1(sK3,sK5) != k7_relat_1(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_226,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_998,plain,
    ( k7_relat_1(sK3,sK5) = k7_relat_1(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_38740,plain,
    ( k1_funct_1(sK4,sK2(sK3,sK4,k1_relat_1(k7_relat_1(sK3,sK5)))) = k1_funct_1(sK3,sK2(sK3,sK4,k1_relat_1(k7_relat_1(sK3,sK5))))
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK5)),k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37574,c_23,c_24,c_16,c_796,c_998])).

cnf(c_38746,plain,
    ( k1_funct_1(sK4,sK2(sK3,sK4,k1_relat_1(k7_relat_1(sK3,sK5)))) = k1_funct_1(sK3,sK2(sK3,sK4,k1_relat_1(k7_relat_1(sK3,sK5)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_38740,c_2571])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X1,sK2(X2,X1,X0)) != k1_funct_1(X2,sK2(X2,X1,X0))
    | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_585,plain,
    ( k1_funct_1(X0,sK2(X1,X0,X2)) != k1_funct_1(X1,sK2(X1,X0,X2))
    | k7_relat_1(X1,X2) = k7_relat_1(X0,X2)
    | r1_tarski(X2,k1_relat_1(X0)) != iProver_top
    | r1_tarski(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_38747,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK5))) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK3,sK5)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK5)),k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK5)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_38746,c_585])).

cnf(c_38748,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK5))) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK3,sK5)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK5)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38747,c_18])).

cnf(c_38749,plain,
    ( k7_relat_1(sK4,sK5) = k7_relat_1(sK3,sK5)
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK5)),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_38748,c_1418,c_1421])).

cnf(c_39014,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK5)),k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38749,c_23,c_24,c_25,c_26,c_16,c_796,c_998])).

cnf(c_39019,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_39014,c_2571])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.63/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.63/1.99  
% 11.63/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.63/1.99  
% 11.63/1.99  ------  iProver source info
% 11.63/1.99  
% 11.63/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.63/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.63/1.99  git: non_committed_changes: false
% 11.63/1.99  git: last_make_outside_of_git: false
% 11.63/1.99  
% 11.63/1.99  ------ 
% 11.63/1.99  
% 11.63/1.99  ------ Input Options
% 11.63/1.99  
% 11.63/1.99  --out_options                           all
% 11.63/1.99  --tptp_safe_out                         true
% 11.63/1.99  --problem_path                          ""
% 11.63/1.99  --include_path                          ""
% 11.63/1.99  --clausifier                            res/vclausify_rel
% 11.63/1.99  --clausifier_options                    --mode clausify
% 11.63/1.99  --stdin                                 false
% 11.63/1.99  --stats_out                             all
% 11.63/1.99  
% 11.63/1.99  ------ General Options
% 11.63/1.99  
% 11.63/1.99  --fof                                   false
% 11.63/1.99  --time_out_real                         305.
% 11.63/1.99  --time_out_virtual                      -1.
% 11.63/1.99  --symbol_type_check                     false
% 11.63/1.99  --clausify_out                          false
% 11.63/1.99  --sig_cnt_out                           false
% 11.63/1.99  --trig_cnt_out                          false
% 11.63/1.99  --trig_cnt_out_tolerance                1.
% 11.63/1.99  --trig_cnt_out_sk_spl                   false
% 11.63/1.99  --abstr_cl_out                          false
% 11.63/1.99  
% 11.63/1.99  ------ Global Options
% 11.63/1.99  
% 11.63/1.99  --schedule                              default
% 11.63/1.99  --add_important_lit                     false
% 11.63/1.99  --prop_solver_per_cl                    1000
% 11.63/1.99  --min_unsat_core                        false
% 11.63/1.99  --soft_assumptions                      false
% 11.63/1.99  --soft_lemma_size                       3
% 11.63/1.99  --prop_impl_unit_size                   0
% 11.63/1.99  --prop_impl_unit                        []
% 11.63/1.99  --share_sel_clauses                     true
% 11.63/1.99  --reset_solvers                         false
% 11.63/1.99  --bc_imp_inh                            [conj_cone]
% 11.63/1.99  --conj_cone_tolerance                   3.
% 11.63/1.99  --extra_neg_conj                        none
% 11.63/1.99  --large_theory_mode                     true
% 11.63/1.99  --prolific_symb_bound                   200
% 11.63/1.99  --lt_threshold                          2000
% 11.63/1.99  --clause_weak_htbl                      true
% 11.63/1.99  --gc_record_bc_elim                     false
% 11.63/1.99  
% 11.63/1.99  ------ Preprocessing Options
% 11.63/1.99  
% 11.63/1.99  --preprocessing_flag                    true
% 11.63/1.99  --time_out_prep_mult                    0.1
% 11.63/1.99  --splitting_mode                        input
% 11.63/1.99  --splitting_grd                         true
% 11.63/1.99  --splitting_cvd                         false
% 11.63/1.99  --splitting_cvd_svl                     false
% 11.63/1.99  --splitting_nvd                         32
% 11.63/1.99  --sub_typing                            true
% 11.63/1.99  --prep_gs_sim                           true
% 11.63/1.99  --prep_unflatten                        true
% 11.63/1.99  --prep_res_sim                          true
% 11.63/1.99  --prep_upred                            true
% 11.63/1.99  --prep_sem_filter                       exhaustive
% 11.63/1.99  --prep_sem_filter_out                   false
% 11.63/1.99  --pred_elim                             true
% 11.63/1.99  --res_sim_input                         true
% 11.63/1.99  --eq_ax_congr_red                       true
% 11.63/1.99  --pure_diseq_elim                       true
% 11.63/1.99  --brand_transform                       false
% 11.63/1.99  --non_eq_to_eq                          false
% 11.63/1.99  --prep_def_merge                        true
% 11.63/1.99  --prep_def_merge_prop_impl              false
% 11.63/1.99  --prep_def_merge_mbd                    true
% 11.63/1.99  --prep_def_merge_tr_red                 false
% 11.63/1.99  --prep_def_merge_tr_cl                  false
% 11.63/1.99  --smt_preprocessing                     true
% 11.63/1.99  --smt_ac_axioms                         fast
% 11.63/1.99  --preprocessed_out                      false
% 11.63/1.99  --preprocessed_stats                    false
% 11.63/1.99  
% 11.63/1.99  ------ Abstraction refinement Options
% 11.63/1.99  
% 11.63/1.99  --abstr_ref                             []
% 11.63/1.99  --abstr_ref_prep                        false
% 11.63/1.99  --abstr_ref_until_sat                   false
% 11.63/1.99  --abstr_ref_sig_restrict                funpre
% 11.63/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.63/1.99  --abstr_ref_under                       []
% 11.63/1.99  
% 11.63/1.99  ------ SAT Options
% 11.63/1.99  
% 11.63/1.99  --sat_mode                              false
% 11.63/1.99  --sat_fm_restart_options                ""
% 11.63/1.99  --sat_gr_def                            false
% 11.63/1.99  --sat_epr_types                         true
% 11.63/1.99  --sat_non_cyclic_types                  false
% 11.63/1.99  --sat_finite_models                     false
% 11.63/1.99  --sat_fm_lemmas                         false
% 11.63/1.99  --sat_fm_prep                           false
% 11.63/1.99  --sat_fm_uc_incr                        true
% 11.63/1.99  --sat_out_model                         small
% 11.63/1.99  --sat_out_clauses                       false
% 11.63/1.99  
% 11.63/1.99  ------ QBF Options
% 11.63/1.99  
% 11.63/1.99  --qbf_mode                              false
% 11.63/1.99  --qbf_elim_univ                         false
% 11.63/1.99  --qbf_dom_inst                          none
% 11.63/1.99  --qbf_dom_pre_inst                      false
% 11.63/1.99  --qbf_sk_in                             false
% 11.63/1.99  --qbf_pred_elim                         true
% 11.63/1.99  --qbf_split                             512
% 11.63/1.99  
% 11.63/1.99  ------ BMC1 Options
% 11.63/1.99  
% 11.63/1.99  --bmc1_incremental                      false
% 11.63/1.99  --bmc1_axioms                           reachable_all
% 11.63/1.99  --bmc1_min_bound                        0
% 11.63/1.99  --bmc1_max_bound                        -1
% 11.63/1.99  --bmc1_max_bound_default                -1
% 11.63/1.99  --bmc1_symbol_reachability              true
% 11.63/1.99  --bmc1_property_lemmas                  false
% 11.63/1.99  --bmc1_k_induction                      false
% 11.63/1.99  --bmc1_non_equiv_states                 false
% 11.63/1.99  --bmc1_deadlock                         false
% 11.63/1.99  --bmc1_ucm                              false
% 11.63/1.99  --bmc1_add_unsat_core                   none
% 11.63/1.99  --bmc1_unsat_core_children              false
% 11.63/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.63/1.99  --bmc1_out_stat                         full
% 11.63/1.99  --bmc1_ground_init                      false
% 11.63/1.99  --bmc1_pre_inst_next_state              false
% 11.63/1.99  --bmc1_pre_inst_state                   false
% 11.63/1.99  --bmc1_pre_inst_reach_state             false
% 11.63/1.99  --bmc1_out_unsat_core                   false
% 11.63/1.99  --bmc1_aig_witness_out                  false
% 11.63/1.99  --bmc1_verbose                          false
% 11.63/1.99  --bmc1_dump_clauses_tptp                false
% 11.63/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.63/1.99  --bmc1_dump_file                        -
% 11.63/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.63/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.63/1.99  --bmc1_ucm_extend_mode                  1
% 11.63/1.99  --bmc1_ucm_init_mode                    2
% 11.63/1.99  --bmc1_ucm_cone_mode                    none
% 11.63/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.63/1.99  --bmc1_ucm_relax_model                  4
% 11.63/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.63/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.63/1.99  --bmc1_ucm_layered_model                none
% 11.63/1.99  --bmc1_ucm_max_lemma_size               10
% 11.63/1.99  
% 11.63/1.99  ------ AIG Options
% 11.63/1.99  
% 11.63/1.99  --aig_mode                              false
% 11.63/1.99  
% 11.63/1.99  ------ Instantiation Options
% 11.63/1.99  
% 11.63/1.99  --instantiation_flag                    true
% 11.63/1.99  --inst_sos_flag                         false
% 11.63/1.99  --inst_sos_phase                        true
% 11.63/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.63/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.63/1.99  --inst_lit_sel_side                     num_symb
% 11.63/1.99  --inst_solver_per_active                1400
% 11.63/1.99  --inst_solver_calls_frac                1.
% 11.63/1.99  --inst_passive_queue_type               priority_queues
% 11.63/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.63/1.99  --inst_passive_queues_freq              [25;2]
% 11.63/1.99  --inst_dismatching                      true
% 11.63/1.99  --inst_eager_unprocessed_to_passive     true
% 11.63/1.99  --inst_prop_sim_given                   true
% 11.63/1.99  --inst_prop_sim_new                     false
% 11.63/1.99  --inst_subs_new                         false
% 11.63/1.99  --inst_eq_res_simp                      false
% 11.63/1.99  --inst_subs_given                       false
% 11.63/1.99  --inst_orphan_elimination               true
% 11.63/1.99  --inst_learning_loop_flag               true
% 11.63/1.99  --inst_learning_start                   3000
% 11.63/1.99  --inst_learning_factor                  2
% 11.63/1.99  --inst_start_prop_sim_after_learn       3
% 11.63/1.99  --inst_sel_renew                        solver
% 11.63/1.99  --inst_lit_activity_flag                true
% 11.63/1.99  --inst_restr_to_given                   false
% 11.63/1.99  --inst_activity_threshold               500
% 11.63/1.99  --inst_out_proof                        true
% 11.63/1.99  
% 11.63/1.99  ------ Resolution Options
% 11.63/1.99  
% 11.63/1.99  --resolution_flag                       true
% 11.63/1.99  --res_lit_sel                           adaptive
% 11.63/1.99  --res_lit_sel_side                      none
% 11.63/1.99  --res_ordering                          kbo
% 11.63/1.99  --res_to_prop_solver                    active
% 11.63/1.99  --res_prop_simpl_new                    false
% 11.63/1.99  --res_prop_simpl_given                  true
% 11.63/1.99  --res_passive_queue_type                priority_queues
% 11.63/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.63/1.99  --res_passive_queues_freq               [15;5]
% 11.63/1.99  --res_forward_subs                      full
% 11.63/1.99  --res_backward_subs                     full
% 11.63/1.99  --res_forward_subs_resolution           true
% 11.63/1.99  --res_backward_subs_resolution          true
% 11.63/1.99  --res_orphan_elimination                true
% 11.63/1.99  --res_time_limit                        2.
% 11.63/1.99  --res_out_proof                         true
% 11.63/1.99  
% 11.63/1.99  ------ Superposition Options
% 11.63/1.99  
% 11.63/1.99  --superposition_flag                    true
% 11.63/1.99  --sup_passive_queue_type                priority_queues
% 11.63/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.63/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.63/1.99  --demod_completeness_check              fast
% 11.63/1.99  --demod_use_ground                      true
% 11.63/1.99  --sup_to_prop_solver                    passive
% 11.63/1.99  --sup_prop_simpl_new                    true
% 11.63/1.99  --sup_prop_simpl_given                  true
% 11.63/1.99  --sup_fun_splitting                     false
% 11.63/1.99  --sup_smt_interval                      50000
% 11.63/1.99  
% 11.63/1.99  ------ Superposition Simplification Setup
% 11.63/1.99  
% 11.63/1.99  --sup_indices_passive                   []
% 11.63/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.63/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/1.99  --sup_full_bw                           [BwDemod]
% 11.63/1.99  --sup_immed_triv                        [TrivRules]
% 11.63/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.63/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/1.99  --sup_immed_bw_main                     []
% 11.63/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.63/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.63/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.63/1.99  
% 11.63/1.99  ------ Combination Options
% 11.63/1.99  
% 11.63/1.99  --comb_res_mult                         3
% 11.63/1.99  --comb_sup_mult                         2
% 11.63/1.99  --comb_inst_mult                        10
% 11.63/1.99  
% 11.63/1.99  ------ Debug Options
% 11.63/1.99  
% 11.63/1.99  --dbg_backtrace                         false
% 11.63/1.99  --dbg_dump_prop_clauses                 false
% 11.63/1.99  --dbg_dump_prop_clauses_file            -
% 11.63/1.99  --dbg_out_stat                          false
% 11.63/1.99  ------ Parsing...
% 11.63/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.63/1.99  
% 11.63/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.63/1.99  
% 11.63/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.63/1.99  
% 11.63/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.63/1.99  ------ Proving...
% 11.63/1.99  ------ Problem Properties 
% 11.63/1.99  
% 11.63/1.99  
% 11.63/1.99  clauses                                 23
% 11.63/1.99  conjectures                             7
% 11.63/1.99  EPR                                     4
% 11.63/1.99  Horn                                    21
% 11.63/1.99  unary                                   10
% 11.63/1.99  binary                                  6
% 11.63/1.99  lits                                    60
% 11.63/1.99  lits eq                                 14
% 11.63/1.99  fd_pure                                 0
% 11.63/1.99  fd_pseudo                               0
% 11.63/1.99  fd_cond                                 0
% 11.63/1.99  fd_pseudo_cond                          0
% 11.63/1.99  AC symbols                              0
% 11.63/1.99  
% 11.63/1.99  ------ Schedule dynamic 5 is on 
% 11.63/1.99  
% 11.63/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.63/1.99  
% 11.63/1.99  
% 11.63/1.99  ------ 
% 11.63/1.99  Current options:
% 11.63/1.99  ------ 
% 11.63/1.99  
% 11.63/1.99  ------ Input Options
% 11.63/1.99  
% 11.63/1.99  --out_options                           all
% 11.63/1.99  --tptp_safe_out                         true
% 11.63/1.99  --problem_path                          ""
% 11.63/1.99  --include_path                          ""
% 11.63/1.99  --clausifier                            res/vclausify_rel
% 11.63/1.99  --clausifier_options                    --mode clausify
% 11.63/1.99  --stdin                                 false
% 11.63/1.99  --stats_out                             all
% 11.63/1.99  
% 11.63/1.99  ------ General Options
% 11.63/1.99  
% 11.63/1.99  --fof                                   false
% 11.63/1.99  --time_out_real                         305.
% 11.63/1.99  --time_out_virtual                      -1.
% 11.63/1.99  --symbol_type_check                     false
% 11.63/1.99  --clausify_out                          false
% 11.63/1.99  --sig_cnt_out                           false
% 11.63/1.99  --trig_cnt_out                          false
% 11.63/1.99  --trig_cnt_out_tolerance                1.
% 11.63/1.99  --trig_cnt_out_sk_spl                   false
% 11.63/1.99  --abstr_cl_out                          false
% 11.63/1.99  
% 11.63/1.99  ------ Global Options
% 11.63/1.99  
% 11.63/1.99  --schedule                              default
% 11.63/1.99  --add_important_lit                     false
% 11.63/1.99  --prop_solver_per_cl                    1000
% 11.63/1.99  --min_unsat_core                        false
% 11.63/1.99  --soft_assumptions                      false
% 11.63/1.99  --soft_lemma_size                       3
% 11.63/1.99  --prop_impl_unit_size                   0
% 11.63/1.99  --prop_impl_unit                        []
% 11.63/1.99  --share_sel_clauses                     true
% 11.63/1.99  --reset_solvers                         false
% 11.63/1.99  --bc_imp_inh                            [conj_cone]
% 11.63/1.99  --conj_cone_tolerance                   3.
% 11.63/1.99  --extra_neg_conj                        none
% 11.63/1.99  --large_theory_mode                     true
% 11.63/1.99  --prolific_symb_bound                   200
% 11.63/1.99  --lt_threshold                          2000
% 11.63/1.99  --clause_weak_htbl                      true
% 11.63/1.99  --gc_record_bc_elim                     false
% 11.63/1.99  
% 11.63/1.99  ------ Preprocessing Options
% 11.63/1.99  
% 11.63/1.99  --preprocessing_flag                    true
% 11.63/1.99  --time_out_prep_mult                    0.1
% 11.63/1.99  --splitting_mode                        input
% 11.63/1.99  --splitting_grd                         true
% 11.63/1.99  --splitting_cvd                         false
% 11.63/1.99  --splitting_cvd_svl                     false
% 11.63/1.99  --splitting_nvd                         32
% 11.63/1.99  --sub_typing                            true
% 11.63/1.99  --prep_gs_sim                           true
% 11.63/1.99  --prep_unflatten                        true
% 11.63/1.99  --prep_res_sim                          true
% 11.63/1.99  --prep_upred                            true
% 11.63/1.99  --prep_sem_filter                       exhaustive
% 11.63/1.99  --prep_sem_filter_out                   false
% 11.63/1.99  --pred_elim                             true
% 11.63/1.99  --res_sim_input                         true
% 11.63/1.99  --eq_ax_congr_red                       true
% 11.63/1.99  --pure_diseq_elim                       true
% 11.63/1.99  --brand_transform                       false
% 11.63/1.99  --non_eq_to_eq                          false
% 11.63/1.99  --prep_def_merge                        true
% 11.63/1.99  --prep_def_merge_prop_impl              false
% 11.63/1.99  --prep_def_merge_mbd                    true
% 11.63/1.99  --prep_def_merge_tr_red                 false
% 11.63/1.99  --prep_def_merge_tr_cl                  false
% 11.63/1.99  --smt_preprocessing                     true
% 11.63/1.99  --smt_ac_axioms                         fast
% 11.63/1.99  --preprocessed_out                      false
% 11.63/1.99  --preprocessed_stats                    false
% 11.63/1.99  
% 11.63/1.99  ------ Abstraction refinement Options
% 11.63/1.99  
% 11.63/1.99  --abstr_ref                             []
% 11.63/1.99  --abstr_ref_prep                        false
% 11.63/1.99  --abstr_ref_until_sat                   false
% 11.63/1.99  --abstr_ref_sig_restrict                funpre
% 11.63/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.63/1.99  --abstr_ref_under                       []
% 11.63/1.99  
% 11.63/1.99  ------ SAT Options
% 11.63/1.99  
% 11.63/1.99  --sat_mode                              false
% 11.63/1.99  --sat_fm_restart_options                ""
% 11.63/1.99  --sat_gr_def                            false
% 11.63/1.99  --sat_epr_types                         true
% 11.63/1.99  --sat_non_cyclic_types                  false
% 11.63/1.99  --sat_finite_models                     false
% 11.63/1.99  --sat_fm_lemmas                         false
% 11.63/1.99  --sat_fm_prep                           false
% 11.63/1.99  --sat_fm_uc_incr                        true
% 11.63/1.99  --sat_out_model                         small
% 11.63/1.99  --sat_out_clauses                       false
% 11.63/1.99  
% 11.63/1.99  ------ QBF Options
% 11.63/1.99  
% 11.63/1.99  --qbf_mode                              false
% 11.63/1.99  --qbf_elim_univ                         false
% 11.63/1.99  --qbf_dom_inst                          none
% 11.63/1.99  --qbf_dom_pre_inst                      false
% 11.63/1.99  --qbf_sk_in                             false
% 11.63/1.99  --qbf_pred_elim                         true
% 11.63/1.99  --qbf_split                             512
% 11.63/1.99  
% 11.63/1.99  ------ BMC1 Options
% 11.63/1.99  
% 11.63/1.99  --bmc1_incremental                      false
% 11.63/1.99  --bmc1_axioms                           reachable_all
% 11.63/1.99  --bmc1_min_bound                        0
% 11.63/1.99  --bmc1_max_bound                        -1
% 11.63/1.99  --bmc1_max_bound_default                -1
% 11.63/1.99  --bmc1_symbol_reachability              true
% 11.63/1.99  --bmc1_property_lemmas                  false
% 11.63/1.99  --bmc1_k_induction                      false
% 11.63/1.99  --bmc1_non_equiv_states                 false
% 11.63/1.99  --bmc1_deadlock                         false
% 11.63/1.99  --bmc1_ucm                              false
% 11.63/1.99  --bmc1_add_unsat_core                   none
% 11.63/1.99  --bmc1_unsat_core_children              false
% 11.63/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.63/1.99  --bmc1_out_stat                         full
% 11.63/1.99  --bmc1_ground_init                      false
% 11.63/1.99  --bmc1_pre_inst_next_state              false
% 11.63/1.99  --bmc1_pre_inst_state                   false
% 11.63/1.99  --bmc1_pre_inst_reach_state             false
% 11.63/1.99  --bmc1_out_unsat_core                   false
% 11.63/1.99  --bmc1_aig_witness_out                  false
% 11.63/1.99  --bmc1_verbose                          false
% 11.63/1.99  --bmc1_dump_clauses_tptp                false
% 11.63/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.63/1.99  --bmc1_dump_file                        -
% 11.63/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.63/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.63/1.99  --bmc1_ucm_extend_mode                  1
% 11.63/1.99  --bmc1_ucm_init_mode                    2
% 11.63/1.99  --bmc1_ucm_cone_mode                    none
% 11.63/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.63/1.99  --bmc1_ucm_relax_model                  4
% 11.63/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.63/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.63/1.99  --bmc1_ucm_layered_model                none
% 11.63/1.99  --bmc1_ucm_max_lemma_size               10
% 11.63/1.99  
% 11.63/1.99  ------ AIG Options
% 11.63/1.99  
% 11.63/1.99  --aig_mode                              false
% 11.63/1.99  
% 11.63/1.99  ------ Instantiation Options
% 11.63/1.99  
% 11.63/1.99  --instantiation_flag                    true
% 11.63/1.99  --inst_sos_flag                         false
% 11.63/1.99  --inst_sos_phase                        true
% 11.63/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.63/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.63/1.99  --inst_lit_sel_side                     none
% 11.63/1.99  --inst_solver_per_active                1400
% 11.63/1.99  --inst_solver_calls_frac                1.
% 11.63/1.99  --inst_passive_queue_type               priority_queues
% 11.63/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.63/1.99  --inst_passive_queues_freq              [25;2]
% 11.63/1.99  --inst_dismatching                      true
% 11.63/1.99  --inst_eager_unprocessed_to_passive     true
% 11.63/1.99  --inst_prop_sim_given                   true
% 11.63/1.99  --inst_prop_sim_new                     false
% 11.63/1.99  --inst_subs_new                         false
% 11.63/1.99  --inst_eq_res_simp                      false
% 11.63/1.99  --inst_subs_given                       false
% 11.63/1.99  --inst_orphan_elimination               true
% 11.63/1.99  --inst_learning_loop_flag               true
% 11.63/1.99  --inst_learning_start                   3000
% 11.63/1.99  --inst_learning_factor                  2
% 11.63/1.99  --inst_start_prop_sim_after_learn       3
% 11.63/1.99  --inst_sel_renew                        solver
% 11.63/1.99  --inst_lit_activity_flag                true
% 11.63/1.99  --inst_restr_to_given                   false
% 11.63/1.99  --inst_activity_threshold               500
% 11.63/1.99  --inst_out_proof                        true
% 11.63/1.99  
% 11.63/1.99  ------ Resolution Options
% 11.63/1.99  
% 11.63/1.99  --resolution_flag                       false
% 11.63/1.99  --res_lit_sel                           adaptive
% 11.63/1.99  --res_lit_sel_side                      none
% 11.63/1.99  --res_ordering                          kbo
% 11.63/1.99  --res_to_prop_solver                    active
% 11.63/1.99  --res_prop_simpl_new                    false
% 11.63/1.99  --res_prop_simpl_given                  true
% 11.63/1.99  --res_passive_queue_type                priority_queues
% 11.63/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.63/1.99  --res_passive_queues_freq               [15;5]
% 11.63/1.99  --res_forward_subs                      full
% 11.63/1.99  --res_backward_subs                     full
% 11.63/1.99  --res_forward_subs_resolution           true
% 11.63/1.99  --res_backward_subs_resolution          true
% 11.63/1.99  --res_orphan_elimination                true
% 11.63/1.99  --res_time_limit                        2.
% 11.63/1.99  --res_out_proof                         true
% 11.63/1.99  
% 11.63/1.99  ------ Superposition Options
% 11.63/1.99  
% 11.63/1.99  --superposition_flag                    true
% 11.63/1.99  --sup_passive_queue_type                priority_queues
% 11.63/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.63/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.63/1.99  --demod_completeness_check              fast
% 11.63/1.99  --demod_use_ground                      true
% 11.63/1.99  --sup_to_prop_solver                    passive
% 11.63/1.99  --sup_prop_simpl_new                    true
% 11.63/1.99  --sup_prop_simpl_given                  true
% 11.63/1.99  --sup_fun_splitting                     false
% 11.63/1.99  --sup_smt_interval                      50000
% 11.63/1.99  
% 11.63/1.99  ------ Superposition Simplification Setup
% 11.63/1.99  
% 11.63/1.99  --sup_indices_passive                   []
% 11.63/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.63/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/1.99  --sup_full_bw                           [BwDemod]
% 11.63/1.99  --sup_immed_triv                        [TrivRules]
% 11.63/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.63/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/1.99  --sup_immed_bw_main                     []
% 11.63/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.63/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.63/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.63/1.99  
% 11.63/1.99  ------ Combination Options
% 11.63/1.99  
% 11.63/1.99  --comb_res_mult                         3
% 11.63/1.99  --comb_sup_mult                         2
% 11.63/1.99  --comb_inst_mult                        10
% 11.63/1.99  
% 11.63/1.99  ------ Debug Options
% 11.63/1.99  
% 11.63/1.99  --dbg_backtrace                         false
% 11.63/1.99  --dbg_dump_prop_clauses                 false
% 11.63/1.99  --dbg_dump_prop_clauses_file            -
% 11.63/1.99  --dbg_out_stat                          false
% 11.63/1.99  
% 11.63/1.99  
% 11.63/1.99  
% 11.63/1.99  
% 11.63/1.99  ------ Proving...
% 11.63/1.99  
% 11.63/1.99  
% 11.63/1.99  % SZS status Theorem for theBenchmark.p
% 11.63/1.99  
% 11.63/1.99   Resolution empty clause
% 11.63/1.99  
% 11.63/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.63/1.99  
% 11.63/1.99  fof(f2,axiom,(
% 11.63/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.63/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.99  
% 11.63/1.99  fof(f13,plain,(
% 11.63/1.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 11.63/1.99    inference(unused_predicate_definition_removal,[],[f2])).
% 11.63/1.99  
% 11.63/1.99  fof(f14,plain,(
% 11.63/1.99    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 11.63/1.99    inference(ennf_transformation,[],[f13])).
% 11.63/1.99  
% 11.63/1.99  fof(f24,plain,(
% 11.63/1.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.63/1.99    introduced(choice_axiom,[])).
% 11.63/1.99  
% 11.63/1.99  fof(f25,plain,(
% 11.63/1.99    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.63/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f24])).
% 11.63/1.99  
% 11.63/1.99  fof(f39,plain,(
% 11.63/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.63/1.99    inference(cnf_transformation,[],[f25])).
% 11.63/1.99  
% 11.63/1.99  fof(f11,conjecture,(
% 11.63/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X0) = k1_relat_1(X1)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 11.63/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.99  
% 11.63/1.99  fof(f12,negated_conjecture,(
% 11.63/1.99    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X0) = k1_relat_1(X1)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 11.63/1.99    inference(negated_conjecture,[],[f11])).
% 11.63/1.99  
% 11.63/1.99  fof(f22,plain,(
% 11.63/1.99    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 11.63/1.99    inference(ennf_transformation,[],[f12])).
% 11.63/1.99  
% 11.63/1.99  fof(f23,plain,(
% 11.63/1.99    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 11.63/1.99    inference(flattening,[],[f22])).
% 11.63/1.99  
% 11.63/1.99  fof(f36,plain,(
% 11.63/1.99    ( ! [X0,X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => (k7_relat_1(X0,sK5) != k7_relat_1(X1,sK5) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,sK5)) & k1_relat_1(X0) = k1_relat_1(X1))) )),
% 11.63/1.99    introduced(choice_axiom,[])).
% 11.63/1.99  
% 11.63/1.99  fof(f35,plain,(
% 11.63/1.99    ( ! [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK4,X2) != k7_relat_1(X0,X2) & ! [X3] : (k1_funct_1(sK4,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK4) = k1_relat_1(X0)) & v1_funct_1(sK4) & v1_relat_1(sK4))) )),
% 11.63/1.99    introduced(choice_axiom,[])).
% 11.63/1.99  
% 11.63/1.99  fof(f34,plain,(
% 11.63/1.99    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(sK3,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(sK3,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK3) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 11.63/1.99    introduced(choice_axiom,[])).
% 11.63/1.99  
% 11.63/1.99  fof(f37,plain,(
% 11.63/1.99    ((k7_relat_1(sK3,sK5) != k7_relat_1(sK4,sK5) & ! [X3] : (k1_funct_1(sK3,X3) = k1_funct_1(sK4,X3) | ~r2_hidden(X3,sK5)) & k1_relat_1(sK3) = k1_relat_1(sK4)) & v1_funct_1(sK4) & v1_relat_1(sK4)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 11.63/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f36,f35,f34])).
% 11.63/1.99  
% 11.63/1.99  fof(f56,plain,(
% 11.63/1.99    v1_relat_1(sK3)),
% 11.63/1.99    inference(cnf_transformation,[],[f37])).
% 11.63/1.99  
% 11.63/1.99  fof(f8,axiom,(
% 11.63/1.99    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 11.63/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.99  
% 11.63/1.99  fof(f18,plain,(
% 11.63/1.99    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 11.63/1.99    inference(ennf_transformation,[],[f8])).
% 11.63/1.99  
% 11.63/1.99  fof(f48,plain,(
% 11.63/1.99    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 11.63/1.99    inference(cnf_transformation,[],[f18])).
% 11.63/1.99  
% 11.63/1.99  fof(f4,axiom,(
% 11.63/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.63/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.99  
% 11.63/1.99  fof(f42,plain,(
% 11.63/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.63/1.99    inference(cnf_transformation,[],[f4])).
% 11.63/1.99  
% 11.63/1.99  fof(f3,axiom,(
% 11.63/1.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.63/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.99  
% 11.63/1.99  fof(f41,plain,(
% 11.63/1.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.63/1.99    inference(cnf_transformation,[],[f3])).
% 11.63/1.99  
% 11.63/1.99  fof(f63,plain,(
% 11.63/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 11.63/1.99    inference(definition_unfolding,[],[f42,f41])).
% 11.63/1.99  
% 11.63/1.99  fof(f66,plain,(
% 11.63/1.99    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 11.63/1.99    inference(definition_unfolding,[],[f48,f63])).
% 11.63/1.99  
% 11.63/1.99  fof(f58,plain,(
% 11.63/1.99    v1_relat_1(sK4)),
% 11.63/1.99    inference(cnf_transformation,[],[f37])).
% 11.63/1.99  
% 11.63/1.99  fof(f60,plain,(
% 11.63/1.99    k1_relat_1(sK3) = k1_relat_1(sK4)),
% 11.63/1.99    inference(cnf_transformation,[],[f37])).
% 11.63/1.99  
% 11.63/1.99  fof(f7,axiom,(
% 11.63/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 11.63/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.99  
% 11.63/1.99  fof(f17,plain,(
% 11.63/1.99    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 11.63/1.99    inference(ennf_transformation,[],[f7])).
% 11.63/1.99  
% 11.63/1.99  fof(f26,plain,(
% 11.63/1.99    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 11.63/1.99    inference(nnf_transformation,[],[f17])).
% 11.63/1.99  
% 11.63/1.99  fof(f27,plain,(
% 11.63/1.99    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 11.63/1.99    inference(flattening,[],[f26])).
% 11.63/1.99  
% 11.63/1.99  fof(f46,plain,(
% 11.63/1.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 11.63/1.99    inference(cnf_transformation,[],[f27])).
% 11.63/1.99  
% 11.63/1.99  fof(f40,plain,(
% 11.63/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.63/1.99    inference(cnf_transformation,[],[f25])).
% 11.63/1.99  
% 11.63/1.99  fof(f10,axiom,(
% 11.63/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 11.63/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.99  
% 11.63/1.99  fof(f20,plain,(
% 11.63/1.99    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | (~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.63/1.99    inference(ennf_transformation,[],[f10])).
% 11.63/1.99  
% 11.63/1.99  fof(f21,plain,(
% 11.63/1.99    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.63/1.99    inference(flattening,[],[f20])).
% 11.63/1.99  
% 11.63/1.99  fof(f30,plain,(
% 11.63/1.99    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.63/1.99    inference(nnf_transformation,[],[f21])).
% 11.63/1.99  
% 11.63/1.99  fof(f31,plain,(
% 11.63/1.99    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.63/1.99    inference(rectify,[],[f30])).
% 11.63/1.99  
% 11.63/1.99  fof(f32,plain,(
% 11.63/1.99    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK2(X0,X1,X2)) != k1_funct_1(X1,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X2)))),
% 11.63/1.99    introduced(choice_axiom,[])).
% 11.63/1.99  
% 11.63/1.99  fof(f33,plain,(
% 11.63/1.99    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | (k1_funct_1(X0,sK2(X0,X1,X2)) != k1_funct_1(X1,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.63/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 11.63/1.99  
% 11.63/1.99  fof(f54,plain,(
% 11.63/1.99    ( ! [X2,X0,X1] : (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | r2_hidden(sK2(X0,X1,X2),X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.63/1.99    inference(cnf_transformation,[],[f33])).
% 11.63/1.99  
% 11.63/1.99  fof(f45,plain,(
% 11.63/1.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 11.63/1.99    inference(cnf_transformation,[],[f27])).
% 11.63/1.99  
% 11.63/1.99  fof(f61,plain,(
% 11.63/1.99    ( ! [X3] : (k1_funct_1(sK3,X3) = k1_funct_1(sK4,X3) | ~r2_hidden(X3,sK5)) )),
% 11.63/1.99    inference(cnf_transformation,[],[f37])).
% 11.63/1.99  
% 11.63/1.99  fof(f59,plain,(
% 11.63/1.99    v1_funct_1(sK4)),
% 11.63/1.99    inference(cnf_transformation,[],[f37])).
% 11.63/1.99  
% 11.63/1.99  fof(f6,axiom,(
% 11.63/1.99    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 11.63/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.99  
% 11.63/1.99  fof(f16,plain,(
% 11.63/1.99    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.63/1.99    inference(ennf_transformation,[],[f6])).
% 11.63/1.99  
% 11.63/1.99  fof(f44,plain,(
% 11.63/1.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 11.63/1.99    inference(cnf_transformation,[],[f16])).
% 11.63/1.99  
% 11.63/1.99  fof(f65,plain,(
% 11.63/1.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 11.63/1.99    inference(definition_unfolding,[],[f44,f63])).
% 11.63/1.99  
% 11.63/1.99  fof(f57,plain,(
% 11.63/1.99    v1_funct_1(sK3)),
% 11.63/1.99    inference(cnf_transformation,[],[f37])).
% 11.63/1.99  
% 11.63/1.99  fof(f62,plain,(
% 11.63/1.99    k7_relat_1(sK3,sK5) != k7_relat_1(sK4,sK5)),
% 11.63/1.99    inference(cnf_transformation,[],[f37])).
% 11.63/1.99  
% 11.63/1.99  fof(f55,plain,(
% 11.63/1.99    ( ! [X2,X0,X1] : (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | k1_funct_1(X0,sK2(X0,X1,X2)) != k1_funct_1(X1,sK2(X0,X1,X2)) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.63/1.99    inference(cnf_transformation,[],[f33])).
% 11.63/1.99  
% 11.63/1.99  cnf(c_2,plain,
% 11.63/1.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.63/1.99      inference(cnf_transformation,[],[f39]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_595,plain,
% 11.63/1.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.63/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.63/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_22,negated_conjecture,
% 11.63/1.99      ( v1_relat_1(sK3) ),
% 11.63/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_578,plain,
% 11.63/1.99      ( v1_relat_1(sK3) = iProver_top ),
% 11.63/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_8,plain,
% 11.63/1.99      ( ~ v1_relat_1(X0)
% 11.63/1.99      | k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 11.63/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_589,plain,
% 11.63/1.99      ( k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 11.63/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.63/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_1034,plain,
% 11.63/1.99      ( k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 11.63/1.99      inference(superposition,[status(thm)],[c_578,c_589]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_20,negated_conjecture,
% 11.63/1.99      ( v1_relat_1(sK4) ),
% 11.63/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_580,plain,
% 11.63/1.99      ( v1_relat_1(sK4) = iProver_top ),
% 11.63/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_1033,plain,
% 11.63/1.99      ( k1_setfam_1(k1_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
% 11.63/1.99      inference(superposition,[status(thm)],[c_580,c_589]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_18,negated_conjecture,
% 11.63/1.99      ( k1_relat_1(sK3) = k1_relat_1(sK4) ),
% 11.63/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_1064,plain,
% 11.63/1.99      ( k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
% 11.63/1.99      inference(light_normalisation,[status(thm)],[c_1033,c_18]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_1125,plain,
% 11.63/1.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
% 11.63/1.99      inference(demodulation,[status(thm)],[c_1034,c_1064]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_6,plain,
% 11.63/1.99      ( r2_hidden(X0,k1_relat_1(X1))
% 11.63/1.99      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
% 11.63/1.99      | ~ v1_relat_1(X1) ),
% 11.63/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_591,plain,
% 11.63/1.99      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 11.63/1.99      | r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
% 11.63/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.63/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_2398,plain,
% 11.63/1.99      ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK3,X1))) != iProver_top
% 11.63/1.99      | r2_hidden(X0,k1_relat_1(sK4)) = iProver_top
% 11.63/1.99      | v1_relat_1(sK4) != iProver_top ),
% 11.63/1.99      inference(superposition,[status(thm)],[c_1125,c_591]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_2414,plain,
% 11.63/1.99      ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK3,X1))) != iProver_top
% 11.63/1.99      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 11.63/1.99      | v1_relat_1(sK4) != iProver_top ),
% 11.63/1.99      inference(light_normalisation,[status(thm)],[c_2398,c_18]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_25,plain,
% 11.63/1.99      ( v1_relat_1(sK4) = iProver_top ),
% 11.63/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_2461,plain,
% 11.63/1.99      ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 11.63/1.99      | r2_hidden(X0,k1_relat_1(k7_relat_1(sK3,X1))) != iProver_top ),
% 11.63/1.99      inference(global_propositional_subsumption,[status(thm)],[c_2414,c_25]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_2462,plain,
% 11.63/1.99      ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK3,X1))) != iProver_top
% 11.63/1.99      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
% 11.63/1.99      inference(renaming,[status(thm)],[c_2461]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_2469,plain,
% 11.63/1.99      ( r2_hidden(sK0(k1_relat_1(k7_relat_1(sK3,X0)),X1),k1_relat_1(sK3)) = iProver_top
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) = iProver_top ),
% 11.63/1.99      inference(superposition,[status(thm)],[c_595,c_2462]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_1,plain,
% 11.63/1.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.63/1.99      inference(cnf_transformation,[],[f40]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_596,plain,
% 11.63/1.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 11.63/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.63/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_2571,plain,
% 11.63/1.99      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK3)) = iProver_top ),
% 11.63/1.99      inference(superposition,[status(thm)],[c_2469,c_596]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_14,plain,
% 11.63/1.99      ( r2_hidden(sK2(X0,X1,X2),X2)
% 11.63/1.99      | ~ r1_tarski(X2,k1_relat_1(X1))
% 11.63/1.99      | ~ r1_tarski(X2,k1_relat_1(X0))
% 11.63/1.99      | ~ v1_funct_1(X1)
% 11.63/1.99      | ~ v1_funct_1(X0)
% 11.63/1.99      | ~ v1_relat_1(X1)
% 11.63/1.99      | ~ v1_relat_1(X0)
% 11.63/1.99      | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ),
% 11.63/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_584,plain,
% 11.63/1.99      ( k7_relat_1(X0,X1) = k7_relat_1(X2,X1)
% 11.63/1.99      | r2_hidden(sK2(X0,X2,X1),X1) = iProver_top
% 11.63/1.99      | r1_tarski(X1,k1_relat_1(X2)) != iProver_top
% 11.63/1.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 11.63/1.99      | v1_funct_1(X0) != iProver_top
% 11.63/1.99      | v1_funct_1(X2) != iProver_top
% 11.63/1.99      | v1_relat_1(X0) != iProver_top
% 11.63/1.99      | v1_relat_1(X2) != iProver_top ),
% 11.63/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_7,plain,
% 11.63/1.99      ( r2_hidden(X0,X1)
% 11.63/1.99      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 11.63/1.99      | ~ v1_relat_1(X2) ),
% 11.63/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_590,plain,
% 11.63/1.99      ( r2_hidden(X0,X1) = iProver_top
% 11.63/1.99      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
% 11.63/1.99      | v1_relat_1(X2) != iProver_top ),
% 11.63/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_2233,plain,
% 11.63/1.99      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X3,k1_relat_1(k7_relat_1(X1,X2)))
% 11.63/1.99      | r2_hidden(sK2(X3,X0,k1_relat_1(k7_relat_1(X1,X2))),X2) = iProver_top
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X0)) != iProver_top
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X3)) != iProver_top
% 11.63/1.99      | v1_funct_1(X0) != iProver_top
% 11.63/1.99      | v1_funct_1(X3) != iProver_top
% 11.63/1.99      | v1_relat_1(X0) != iProver_top
% 11.63/1.99      | v1_relat_1(X3) != iProver_top
% 11.63/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.63/1.99      inference(superposition,[status(thm)],[c_584,c_590]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_17,negated_conjecture,
% 11.63/1.99      ( ~ r2_hidden(X0,sK5) | k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0) ),
% 11.63/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_582,plain,
% 11.63/1.99      ( k1_funct_1(sK3,X0) = k1_funct_1(sK4,X0)
% 11.63/1.99      | r2_hidden(X0,sK5) != iProver_top ),
% 11.63/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_30754,plain,
% 11.63/1.99      ( k1_funct_1(sK4,sK2(X0,X1,k1_relat_1(k7_relat_1(X2,sK5)))) = k1_funct_1(sK3,sK2(X0,X1,k1_relat_1(k7_relat_1(X2,sK5))))
% 11.63/1.99      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X2,sK5))) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,sK5)))
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(X2,sK5)),k1_relat_1(X1)) != iProver_top
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(X2,sK5)),k1_relat_1(X0)) != iProver_top
% 11.63/1.99      | v1_funct_1(X0) != iProver_top
% 11.63/1.99      | v1_funct_1(X1) != iProver_top
% 11.63/1.99      | v1_relat_1(X0) != iProver_top
% 11.63/1.99      | v1_relat_1(X1) != iProver_top
% 11.63/1.99      | v1_relat_1(X2) != iProver_top ),
% 11.63/1.99      inference(superposition,[status(thm)],[c_2233,c_582]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_36379,plain,
% 11.63/1.99      ( k1_funct_1(sK3,sK2(X0,sK4,k1_relat_1(k7_relat_1(X1,sK5)))) = k1_funct_1(sK4,sK2(X0,sK4,k1_relat_1(k7_relat_1(X1,sK5))))
% 11.63/1.99      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK5))) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(X1,sK5)))
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK5)),k1_relat_1(X0)) != iProver_top
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK5)),k1_relat_1(sK3)) != iProver_top
% 11.63/1.99      | v1_funct_1(X0) != iProver_top
% 11.63/1.99      | v1_funct_1(sK4) != iProver_top
% 11.63/1.99      | v1_relat_1(X1) != iProver_top
% 11.63/1.99      | v1_relat_1(X0) != iProver_top
% 11.63/1.99      | v1_relat_1(sK4) != iProver_top ),
% 11.63/1.99      inference(superposition,[status(thm)],[c_18,c_30754]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_19,negated_conjecture,
% 11.63/1.99      ( v1_funct_1(sK4) ),
% 11.63/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_26,plain,
% 11.63/1.99      ( v1_funct_1(sK4) = iProver_top ),
% 11.63/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_37136,plain,
% 11.63/1.99      ( v1_relat_1(X0) != iProver_top
% 11.63/1.99      | v1_relat_1(X1) != iProver_top
% 11.63/1.99      | k1_funct_1(sK3,sK2(X0,sK4,k1_relat_1(k7_relat_1(X1,sK5)))) = k1_funct_1(sK4,sK2(X0,sK4,k1_relat_1(k7_relat_1(X1,sK5))))
% 11.63/1.99      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK5))) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(X1,sK5)))
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK5)),k1_relat_1(X0)) != iProver_top
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK5)),k1_relat_1(sK3)) != iProver_top
% 11.63/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.63/1.99      inference(global_propositional_subsumption,
% 11.63/1.99                [status(thm)],
% 11.63/1.99                [c_36379,c_25,c_26]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_37137,plain,
% 11.63/1.99      ( k1_funct_1(sK3,sK2(X0,sK4,k1_relat_1(k7_relat_1(X1,sK5)))) = k1_funct_1(sK4,sK2(X0,sK4,k1_relat_1(k7_relat_1(X1,sK5))))
% 11.63/1.99      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK5))) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(X1,sK5)))
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK5)),k1_relat_1(X0)) != iProver_top
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK5)),k1_relat_1(sK3)) != iProver_top
% 11.63/1.99      | v1_funct_1(X0) != iProver_top
% 11.63/1.99      | v1_relat_1(X0) != iProver_top
% 11.63/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.63/1.99      inference(renaming,[status(thm)],[c_37136]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_37151,plain,
% 11.63/1.99      ( k1_funct_1(sK4,sK2(sK3,sK4,k1_relat_1(k7_relat_1(sK3,sK5)))) = k1_funct_1(sK3,sK2(sK3,sK4,k1_relat_1(k7_relat_1(sK3,sK5))))
% 11.63/1.99      | k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK5))) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK3,sK5)))
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK5)),k1_relat_1(sK3)) != iProver_top
% 11.63/1.99      | v1_funct_1(sK3) != iProver_top
% 11.63/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.63/1.99      inference(superposition,[status(thm)],[c_2571,c_37137]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_4,plain,
% 11.63/1.99      ( ~ v1_relat_1(X0)
% 11.63/1.99      | k7_relat_1(X0,k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
% 11.63/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_593,plain,
% 11.63/1.99      ( k7_relat_1(X0,k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1))) = k7_relat_1(X0,X1)
% 11.63/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.63/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_1416,plain,
% 11.63/1.99      ( k7_relat_1(sK3,k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),X0))) = k7_relat_1(sK3,X0) ),
% 11.63/1.99      inference(superposition,[status(thm)],[c_578,c_593]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_1418,plain,
% 11.63/1.99      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0))) = k7_relat_1(sK3,X0) ),
% 11.63/1.99      inference(light_normalisation,[status(thm)],[c_1416,c_1034]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_1415,plain,
% 11.63/1.99      ( k7_relat_1(sK4,k1_setfam_1(k1_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),X0))) = k7_relat_1(sK4,X0) ),
% 11.63/1.99      inference(superposition,[status(thm)],[c_580,c_593]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_1421,plain,
% 11.63/1.99      ( k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK3,X0))) = k7_relat_1(sK4,X0) ),
% 11.63/1.99      inference(light_normalisation,[status(thm)],[c_1415,c_18,c_1034]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_37574,plain,
% 11.63/1.99      ( k1_funct_1(sK4,sK2(sK3,sK4,k1_relat_1(k7_relat_1(sK3,sK5)))) = k1_funct_1(sK3,sK2(sK3,sK4,k1_relat_1(k7_relat_1(sK3,sK5))))
% 11.63/1.99      | k7_relat_1(sK4,sK5) = k7_relat_1(sK3,sK5)
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK5)),k1_relat_1(sK3)) != iProver_top
% 11.63/1.99      | v1_funct_1(sK3) != iProver_top
% 11.63/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.63/1.99      inference(demodulation,[status(thm)],[c_37151,c_1418,c_1421]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_23,plain,
% 11.63/1.99      ( v1_relat_1(sK3) = iProver_top ),
% 11.63/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_21,negated_conjecture,
% 11.63/1.99      ( v1_funct_1(sK3) ),
% 11.63/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_24,plain,
% 11.63/1.99      ( v1_funct_1(sK3) = iProver_top ),
% 11.63/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_16,negated_conjecture,
% 11.63/1.99      ( k7_relat_1(sK3,sK5) != k7_relat_1(sK4,sK5) ),
% 11.63/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_227,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_765,plain,
% 11.63/1.99      ( k7_relat_1(sK4,sK5) != X0
% 11.63/1.99      | k7_relat_1(sK3,sK5) != X0
% 11.63/1.99      | k7_relat_1(sK3,sK5) = k7_relat_1(sK4,sK5) ),
% 11.63/1.99      inference(instantiation,[status(thm)],[c_227]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_794,plain,
% 11.63/1.99      ( k7_relat_1(sK4,sK5) != k7_relat_1(X0,sK5)
% 11.63/1.99      | k7_relat_1(sK3,sK5) != k7_relat_1(X0,sK5)
% 11.63/1.99      | k7_relat_1(sK3,sK5) = k7_relat_1(sK4,sK5) ),
% 11.63/1.99      inference(instantiation,[status(thm)],[c_765]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_796,plain,
% 11.63/1.99      ( k7_relat_1(sK4,sK5) != k7_relat_1(sK3,sK5)
% 11.63/1.99      | k7_relat_1(sK3,sK5) = k7_relat_1(sK4,sK5)
% 11.63/1.99      | k7_relat_1(sK3,sK5) != k7_relat_1(sK3,sK5) ),
% 11.63/1.99      inference(instantiation,[status(thm)],[c_794]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_226,plain,( X0 = X0 ),theory(equality) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_998,plain,
% 11.63/1.99      ( k7_relat_1(sK3,sK5) = k7_relat_1(sK3,sK5) ),
% 11.63/1.99      inference(instantiation,[status(thm)],[c_226]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_38740,plain,
% 11.63/1.99      ( k1_funct_1(sK4,sK2(sK3,sK4,k1_relat_1(k7_relat_1(sK3,sK5)))) = k1_funct_1(sK3,sK2(sK3,sK4,k1_relat_1(k7_relat_1(sK3,sK5))))
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK5)),k1_relat_1(sK3)) != iProver_top ),
% 11.63/1.99      inference(global_propositional_subsumption,
% 11.63/1.99                [status(thm)],
% 11.63/1.99                [c_37574,c_23,c_24,c_16,c_796,c_998]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_38746,plain,
% 11.63/1.99      ( k1_funct_1(sK4,sK2(sK3,sK4,k1_relat_1(k7_relat_1(sK3,sK5)))) = k1_funct_1(sK3,sK2(sK3,sK4,k1_relat_1(k7_relat_1(sK3,sK5)))) ),
% 11.63/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_38740,c_2571]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_13,plain,
% 11.63/1.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 11.63/1.99      | ~ r1_tarski(X0,k1_relat_1(X2))
% 11.63/1.99      | ~ v1_funct_1(X1)
% 11.63/1.99      | ~ v1_funct_1(X2)
% 11.63/1.99      | ~ v1_relat_1(X1)
% 11.63/1.99      | ~ v1_relat_1(X2)
% 11.63/1.99      | k1_funct_1(X1,sK2(X2,X1,X0)) != k1_funct_1(X2,sK2(X2,X1,X0))
% 11.63/1.99      | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
% 11.63/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_585,plain,
% 11.63/1.99      ( k1_funct_1(X0,sK2(X1,X0,X2)) != k1_funct_1(X1,sK2(X1,X0,X2))
% 11.63/1.99      | k7_relat_1(X1,X2) = k7_relat_1(X0,X2)
% 11.63/1.99      | r1_tarski(X2,k1_relat_1(X0)) != iProver_top
% 11.63/1.99      | r1_tarski(X2,k1_relat_1(X1)) != iProver_top
% 11.63/1.99      | v1_funct_1(X1) != iProver_top
% 11.63/1.99      | v1_funct_1(X0) != iProver_top
% 11.63/1.99      | v1_relat_1(X1) != iProver_top
% 11.63/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.63/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_38747,plain,
% 11.63/1.99      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK5))) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK3,sK5)))
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK5)),k1_relat_1(sK4)) != iProver_top
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK5)),k1_relat_1(sK3)) != iProver_top
% 11.63/1.99      | v1_funct_1(sK4) != iProver_top
% 11.63/1.99      | v1_funct_1(sK3) != iProver_top
% 11.63/1.99      | v1_relat_1(sK4) != iProver_top
% 11.63/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.63/1.99      inference(superposition,[status(thm)],[c_38746,c_585]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_38748,plain,
% 11.63/1.99      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK5))) = k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK3,sK5)))
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK5)),k1_relat_1(sK3)) != iProver_top
% 11.63/1.99      | v1_funct_1(sK4) != iProver_top
% 11.63/1.99      | v1_funct_1(sK3) != iProver_top
% 11.63/1.99      | v1_relat_1(sK4) != iProver_top
% 11.63/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.63/1.99      inference(light_normalisation,[status(thm)],[c_38747,c_18]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_38749,plain,
% 11.63/1.99      ( k7_relat_1(sK4,sK5) = k7_relat_1(sK3,sK5)
% 11.63/1.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK5)),k1_relat_1(sK3)) != iProver_top
% 11.63/1.99      | v1_funct_1(sK4) != iProver_top
% 11.63/1.99      | v1_funct_1(sK3) != iProver_top
% 11.63/1.99      | v1_relat_1(sK4) != iProver_top
% 11.63/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.63/1.99      inference(demodulation,[status(thm)],[c_38748,c_1418,c_1421]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_39014,plain,
% 11.63/1.99      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK5)),k1_relat_1(sK3)) != iProver_top ),
% 11.63/1.99      inference(global_propositional_subsumption,
% 11.63/1.99                [status(thm)],
% 11.63/1.99                [c_38749,c_23,c_24,c_25,c_26,c_16,c_796,c_998]) ).
% 11.63/1.99  
% 11.63/1.99  cnf(c_39019,plain,
% 11.63/1.99      ( $false ),
% 11.63/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_39014,c_2571]) ).
% 11.63/1.99  
% 11.63/1.99  
% 11.63/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.63/1.99  
% 11.63/1.99  ------                               Statistics
% 11.63/1.99  
% 11.63/1.99  ------ General
% 11.63/1.99  
% 11.63/1.99  abstr_ref_over_cycles:                  0
% 11.63/1.99  abstr_ref_under_cycles:                 0
% 11.63/1.99  gc_basic_clause_elim:                   0
% 11.63/1.99  forced_gc_time:                         0
% 11.63/1.99  parsing_time:                           0.01
% 11.63/1.99  unif_index_cands_time:                  0.
% 11.63/1.99  unif_index_add_time:                    0.
% 11.63/1.99  orderings_time:                         0.
% 11.63/1.99  out_proof_time:                         0.011
% 11.63/1.99  total_time:                             1.063
% 11.63/1.99  num_of_symbols:                         47
% 11.63/1.99  num_of_terms:                           27911
% 11.63/1.99  
% 11.63/1.99  ------ Preprocessing
% 11.63/1.99  
% 11.63/1.99  num_of_splits:                          0
% 11.63/1.99  num_of_split_atoms:                     0
% 11.63/1.99  num_of_reused_defs:                     0
% 11.63/1.99  num_eq_ax_congr_red:                    16
% 11.63/1.99  num_of_sem_filtered_clauses:            1
% 11.63/1.99  num_of_subtypes:                        0
% 11.63/1.99  monotx_restored_types:                  0
% 11.63/1.99  sat_num_of_epr_types:                   0
% 11.63/1.99  sat_num_of_non_cyclic_types:            0
% 11.63/1.99  sat_guarded_non_collapsed_types:        0
% 11.63/1.99  num_pure_diseq_elim:                    0
% 11.63/1.99  simp_replaced_by:                       0
% 11.63/1.99  res_preprocessed:                       92
% 11.63/1.99  prep_upred:                             0
% 11.63/1.99  prep_unflattend:                        0
% 11.63/1.99  smt_new_axioms:                         0
% 11.63/1.99  pred_elim_cands:                        4
% 11.63/1.99  pred_elim:                              0
% 11.63/1.99  pred_elim_cl:                           0
% 11.63/1.99  pred_elim_cycles:                       1
% 11.63/1.99  merged_defs:                            0
% 11.63/1.99  merged_defs_ncl:                        0
% 11.63/1.99  bin_hyper_res:                          0
% 11.63/1.99  prep_cycles:                            3
% 11.63/1.99  pred_elim_time:                         0.
% 11.63/1.99  splitting_time:                         0.
% 11.63/1.99  sem_filter_time:                        0.
% 11.63/1.99  monotx_time:                            0.001
% 11.63/1.99  subtype_inf_time:                       0.
% 11.63/1.99  
% 11.63/1.99  ------ Problem properties
% 11.63/1.99  
% 11.63/1.99  clauses:                                23
% 11.63/1.99  conjectures:                            7
% 11.63/1.99  epr:                                    4
% 11.63/1.99  horn:                                   21
% 11.63/1.99  ground:                                 6
% 11.63/1.99  unary:                                  10
% 11.63/1.99  binary:                                 6
% 11.63/1.99  lits:                                   60
% 11.63/1.99  lits_eq:                                14
% 11.63/1.99  fd_pure:                                0
% 11.63/1.99  fd_pseudo:                              0
% 11.63/1.99  fd_cond:                                0
% 11.63/1.99  fd_pseudo_cond:                         0
% 11.63/1.99  ac_symbols:                             0
% 11.63/1.99  
% 11.63/1.99  ------ Propositional Solver
% 11.63/1.99  
% 11.63/1.99  prop_solver_calls:                      31
% 11.63/1.99  prop_fast_solver_calls:                 2133
% 11.63/1.99  smt_solver_calls:                       0
% 11.63/1.99  smt_fast_solver_calls:                  0
% 11.63/1.99  prop_num_of_clauses:                    9100
% 11.63/1.99  prop_preprocess_simplified:             13480
% 11.63/1.99  prop_fo_subsumed:                       154
% 11.63/1.99  prop_solver_time:                       0.
% 11.63/1.99  smt_solver_time:                        0.
% 11.63/1.99  smt_fast_solver_time:                   0.
% 11.63/1.99  prop_fast_solver_time:                  0.
% 11.63/1.99  prop_unsat_core_time:                   0.
% 11.63/1.99  
% 11.63/1.99  ------ QBF
% 11.63/1.99  
% 11.63/1.99  qbf_q_res:                              0
% 11.63/1.99  qbf_num_tautologies:                    0
% 11.63/1.99  qbf_prep_cycles:                        0
% 11.63/1.99  
% 11.63/1.99  ------ BMC1
% 11.63/1.99  
% 11.63/1.99  bmc1_current_bound:                     -1
% 11.63/1.99  bmc1_last_solved_bound:                 -1
% 11.63/1.99  bmc1_unsat_core_size:                   -1
% 11.63/1.99  bmc1_unsat_core_parents_size:           -1
% 11.63/1.99  bmc1_merge_next_fun:                    0
% 11.63/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.63/1.99  
% 11.63/1.99  ------ Instantiation
% 11.63/1.99  
% 11.63/1.99  inst_num_of_clauses:                    2828
% 11.63/1.99  inst_num_in_passive:                    1323
% 11.63/1.99  inst_num_in_active:                     1216
% 11.63/1.99  inst_num_in_unprocessed:                289
% 11.63/1.99  inst_num_of_loops:                      1330
% 11.63/1.99  inst_num_of_learning_restarts:          0
% 11.63/1.99  inst_num_moves_active_passive:          105
% 11.63/1.99  inst_lit_activity:                      0
% 11.63/1.99  inst_lit_activity_moves:                0
% 11.63/1.99  inst_num_tautologies:                   0
% 11.63/1.99  inst_num_prop_implied:                  0
% 11.63/1.99  inst_num_existing_simplified:           0
% 11.63/1.99  inst_num_eq_res_simplified:             0
% 11.63/1.99  inst_num_child_elim:                    0
% 11.63/1.99  inst_num_of_dismatching_blockings:      4156
% 11.63/1.99  inst_num_of_non_proper_insts:           4734
% 11.63/1.99  inst_num_of_duplicates:                 0
% 11.63/1.99  inst_inst_num_from_inst_to_res:         0
% 11.63/1.99  inst_dismatching_checking_time:         0.
% 11.63/1.99  
% 11.63/1.99  ------ Resolution
% 11.63/1.99  
% 11.63/1.99  res_num_of_clauses:                     0
% 11.63/1.99  res_num_in_passive:                     0
% 11.63/1.99  res_num_in_active:                      0
% 11.63/1.99  res_num_of_loops:                       95
% 11.63/1.99  res_forward_subset_subsumed:            820
% 11.63/1.99  res_backward_subset_subsumed:           4
% 11.63/1.99  res_forward_subsumed:                   0
% 11.63/1.99  res_backward_subsumed:                  0
% 11.63/1.99  res_forward_subsumption_resolution:     0
% 11.63/1.99  res_backward_subsumption_resolution:    0
% 11.63/1.99  res_clause_to_clause_subsumption:       6589
% 11.63/1.99  res_orphan_elimination:                 0
% 11.63/1.99  res_tautology_del:                      615
% 11.63/1.99  res_num_eq_res_simplified:              0
% 11.63/1.99  res_num_sel_changes:                    0
% 11.63/1.99  res_moves_from_active_to_pass:          0
% 11.63/1.99  
% 11.63/1.99  ------ Superposition
% 11.63/1.99  
% 11.63/1.99  sup_time_total:                         0.
% 11.63/1.99  sup_time_generating:                    0.
% 11.63/1.99  sup_time_sim_full:                      0.
% 11.63/1.99  sup_time_sim_immed:                     0.
% 11.63/1.99  
% 11.63/1.99  sup_num_of_clauses:                     1222
% 11.63/1.99  sup_num_in_active:                      257
% 11.63/1.99  sup_num_in_passive:                     965
% 11.63/1.99  sup_num_of_loops:                       264
% 11.63/1.99  sup_fw_superposition:                   1631
% 11.63/1.99  sup_bw_superposition:                   791
% 11.63/1.99  sup_immediate_simplified:               901
% 11.63/1.99  sup_given_eliminated:                   1
% 11.63/1.99  comparisons_done:                       0
% 11.63/1.99  comparisons_avoided:                    409
% 11.63/1.99  
% 11.63/1.99  ------ Simplifications
% 11.63/1.99  
% 11.63/1.99  
% 11.63/1.99  sim_fw_subset_subsumed:                 98
% 11.63/1.99  sim_bw_subset_subsumed:                 23
% 11.63/1.99  sim_fw_subsumed:                        143
% 11.63/1.99  sim_bw_subsumed:                        21
% 11.63/1.99  sim_fw_subsumption_res:                 44
% 11.63/1.99  sim_bw_subsumption_res:                 0
% 11.63/1.99  sim_tautology_del:                      49
% 11.63/1.99  sim_eq_tautology_del:                   48
% 11.63/1.99  sim_eq_res_simp:                        0
% 11.63/1.99  sim_fw_demodulated:                     412
% 11.63/1.99  sim_bw_demodulated:                     16
% 11.63/1.99  sim_light_normalised:                   372
% 11.63/1.99  sim_joinable_taut:                      0
% 11.63/1.99  sim_joinable_simp:                      0
% 11.63/1.99  sim_ac_normalised:                      0
% 11.63/1.99  sim_smt_subsumption:                    0
% 11.63/1.99  
%------------------------------------------------------------------------------
