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
% DateTime   : Thu Dec  3 11:52:42 EST 2020

% Result     : Theorem 6.96s
% Output     : CNFRefutation 6.96s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 869 expanded)
%              Number of clauses        :   73 ( 248 expanded)
%              Number of leaves         :   17 ( 259 expanded)
%              Depth                    :   24
%              Number of atoms          :  430 (4073 expanded)
%              Number of equality atoms :  240 (1940 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
          & ! [X3] :
              ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
              | ~ r2_hidden(X3,X2) )
          & k1_relat_1(X0) = k1_relat_1(X1) )
     => ( k7_relat_1(X0,sK3) != k7_relat_1(X1,sK3)
        & ! [X3] :
            ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,sK3) )
        & k1_relat_1(X0) = k1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
            ( k7_relat_1(sK2,X2) != k7_relat_1(X0,X2)
            & ! [X3] :
                ( k1_funct_1(sK2,X3) = k1_funct_1(X0,X3)
                | ~ r2_hidden(X3,X2) )
            & k1_relat_1(sK2) = k1_relat_1(X0) )
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
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
              ( k7_relat_1(sK1,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(sK1,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(sK1) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3)
    & ! [X3] :
        ( k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)
        | ~ r2_hidden(X3,sK3) )
    & k1_relat_1(sK1) = k1_relat_1(sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f32,f31,f30])).

fof(f51,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f44,f58])).

fof(f53,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    k1_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

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

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ( k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2))
                    & r2_hidden(sK0(X0,X1,X2),X2) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

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

fof(f56,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(definition_unfolding,[],[f34,f58,f58])).

fof(f52,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2))
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_524,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_535,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1419,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_524,c_535])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_526,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1418,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_526,c_535])).

cnf(c_17,negated_conjecture,
    ( k1_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1461,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1418,c_17])).

cnf(c_2465,plain,
    ( k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_1419,c_1461])).

cnf(c_7,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_536,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1058,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_536])).

cnf(c_24,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_785,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_786,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_708,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(X2,X3)),k1_relat_1(X2))
    | X1 != k1_relat_1(X2)
    | X0 != k1_relat_1(k7_relat_1(X2,X3)) ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_767,plain,
    ( r1_tarski(X0,k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,X1)),k1_relat_1(sK2))
    | X0 != k1_relat_1(k7_relat_1(sK2,X1))
    | k1_relat_1(sK1) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_928,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK2))
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK1))
    | k1_relat_1(k7_relat_1(sK2,X0)) != k1_relat_1(k7_relat_1(sK2,X0))
    | k1_relat_1(sK1) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_930,plain,
    ( k1_relat_1(k7_relat_1(sK2,X0)) != k1_relat_1(k7_relat_1(sK2,X0))
    | k1_relat_1(sK1) != k1_relat_1(sK2)
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_928])).

cnf(c_204,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_773,plain,
    ( k1_relat_1(X0) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_929,plain,
    ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_1304,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1058,c_24,c_17,c_786,c_930,c_929])).

cnf(c_2492,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2465,c_1304])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | r2_hidden(sK0(X2,X1,X0),X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_530,plain,
    ( k7_relat_1(X0,X1) = k7_relat_1(X2,X1)
    | r1_tarski(X1,k1_relat_1(X2)) != iProver_top
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X1) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_537,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2131,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X3,k1_relat_1(k7_relat_1(X1,X2)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X3)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X0)) != iProver_top
    | r2_hidden(sK0(X3,X0,k1_relat_1(k7_relat_1(X1,X2))),X2) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_530,c_537])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_528,plain,
    ( k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_19307,plain,
    ( k1_funct_1(sK2,sK0(X0,X1,k1_relat_1(k7_relat_1(X2,sK3)))) = k1_funct_1(sK1,sK0(X0,X1,k1_relat_1(k7_relat_1(X2,sK3))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X2,sK3))) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,sK3)))
    | r1_tarski(k1_relat_1(k7_relat_1(X2,sK3)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X2,sK3)),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2131,c_528])).

cnf(c_20730,plain,
    ( k1_funct_1(sK1,sK0(sK2,X0,k1_relat_1(k7_relat_1(X1,sK3)))) = k1_funct_1(sK2,sK0(sK2,X0,k1_relat_1(k7_relat_1(X1,sK3))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK3))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(X1,sK3)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK3)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK3)),k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_19307])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_21240,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k1_funct_1(sK1,sK0(sK2,X0,k1_relat_1(k7_relat_1(X1,sK3)))) = k1_funct_1(sK2,sK0(sK2,X0,k1_relat_1(k7_relat_1(X1,sK3))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK3))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(X1,sK3)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK3)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK3)),k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20730,c_24,c_25])).

cnf(c_21241,plain,
    ( k1_funct_1(sK1,sK0(sK2,X0,k1_relat_1(k7_relat_1(X1,sK3)))) = k1_funct_1(sK2,sK0(sK2,X0,k1_relat_1(k7_relat_1(X1,sK3))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK3))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(X1,sK3)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK3)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK3)),k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_21240])).

cnf(c_21255,plain,
    ( k1_funct_1(sK2,sK0(sK2,sK1,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK2,sK1,k1_relat_1(k7_relat_1(sK1,sK3))))
    | k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2492,c_21241])).

cnf(c_11,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_532,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,k1_relat_1(k7_relat_1(X0,k1_relat_1(X1)))) = k7_relat_1(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_540,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5597,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_532,c_540])).

cnf(c_3,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5610,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(X0)))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5597,c_3])).

cnf(c_5787,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)))) = k7_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_524,c_5610])).

cnf(c_0,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1417,plain,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_532,c_535])).

cnf(c_1426,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_1417,c_3])).

cnf(c_1440,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_0,c_1426])).

cnf(c_2472,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_1419,c_1440])).

cnf(c_5789,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_5787,c_2472])).

cnf(c_5786,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2)))) = k7_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_526,c_5610])).

cnf(c_5792,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_5786,c_17,c_2472])).

cnf(c_21571,plain,
    ( k1_funct_1(sK2,sK0(sK2,sK1,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK2,sK1,k1_relat_1(k7_relat_1(sK1,sK3))))
    | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_21255,c_5789,c_5792])).

cnf(c_22,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_23,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21966,plain,
    ( k1_funct_1(sK2,sK0(sK2,sK1,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK2,sK1,k1_relat_1(k7_relat_1(sK1,sK3))))
    | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21571,c_22,c_23])).

cnf(c_21973,plain,
    ( k1_funct_1(sK2,sK0(sK2,sK1,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK2,sK1,k1_relat_1(k7_relat_1(sK1,sK3))))
    | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21966,c_2492])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X1,sK0(X2,X1,X0)) != k1_funct_1(X2,sK0(X2,X1,X0))
    | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_531,plain,
    ( k1_funct_1(X0,sK0(X1,X0,X2)) != k1_funct_1(X1,sK0(X1,X0,X2))
    | k7_relat_1(X1,X2) = k7_relat_1(X0,X2)
    | r1_tarski(X2,k1_relat_1(X0)) != iProver_top
    | r1_tarski(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_21974,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
    | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_21973,c_531])).

cnf(c_21975,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
    | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21974,c_17])).

cnf(c_21976,plain,
    ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_21975,c_5789,c_5792])).

cnf(c_21979,plain,
    ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21976,c_22,c_23,c_24,c_25])).

cnf(c_21985,plain,
    ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21979,c_2492])).

cnf(c_15,negated_conjecture,
    ( k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21988,plain,
    ( k7_relat_1(sK1,sK3) != k7_relat_1(sK1,sK3) ),
    inference(demodulation,[status(thm)],[c_21985,c_15])).

cnf(c_21989,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_21988])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:20:57 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 6.96/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.96/1.49  
% 6.96/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.96/1.49  
% 6.96/1.49  ------  iProver source info
% 6.96/1.49  
% 6.96/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.96/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.96/1.49  git: non_committed_changes: false
% 6.96/1.49  git: last_make_outside_of_git: false
% 6.96/1.49  
% 6.96/1.49  ------ 
% 6.96/1.49  
% 6.96/1.49  ------ Input Options
% 6.96/1.49  
% 6.96/1.49  --out_options                           all
% 6.96/1.49  --tptp_safe_out                         true
% 6.96/1.49  --problem_path                          ""
% 6.96/1.49  --include_path                          ""
% 6.96/1.49  --clausifier                            res/vclausify_rel
% 6.96/1.49  --clausifier_options                    --mode clausify
% 6.96/1.49  --stdin                                 false
% 6.96/1.49  --stats_out                             all
% 6.96/1.49  
% 6.96/1.49  ------ General Options
% 6.96/1.49  
% 6.96/1.49  --fof                                   false
% 6.96/1.49  --time_out_real                         305.
% 6.96/1.49  --time_out_virtual                      -1.
% 6.96/1.49  --symbol_type_check                     false
% 6.96/1.49  --clausify_out                          false
% 6.96/1.49  --sig_cnt_out                           false
% 6.96/1.49  --trig_cnt_out                          false
% 6.96/1.49  --trig_cnt_out_tolerance                1.
% 6.96/1.49  --trig_cnt_out_sk_spl                   false
% 6.96/1.49  --abstr_cl_out                          false
% 6.96/1.49  
% 6.96/1.49  ------ Global Options
% 6.96/1.49  
% 6.96/1.49  --schedule                              default
% 6.96/1.49  --add_important_lit                     false
% 6.96/1.49  --prop_solver_per_cl                    1000
% 6.96/1.49  --min_unsat_core                        false
% 6.96/1.49  --soft_assumptions                      false
% 6.96/1.49  --soft_lemma_size                       3
% 6.96/1.49  --prop_impl_unit_size                   0
% 6.96/1.49  --prop_impl_unit                        []
% 6.96/1.49  --share_sel_clauses                     true
% 6.96/1.49  --reset_solvers                         false
% 6.96/1.49  --bc_imp_inh                            [conj_cone]
% 6.96/1.49  --conj_cone_tolerance                   3.
% 6.96/1.49  --extra_neg_conj                        none
% 6.96/1.49  --large_theory_mode                     true
% 6.96/1.49  --prolific_symb_bound                   200
% 6.96/1.49  --lt_threshold                          2000
% 6.96/1.49  --clause_weak_htbl                      true
% 6.96/1.49  --gc_record_bc_elim                     false
% 6.96/1.49  
% 6.96/1.49  ------ Preprocessing Options
% 6.96/1.49  
% 6.96/1.49  --preprocessing_flag                    true
% 6.96/1.49  --time_out_prep_mult                    0.1
% 6.96/1.49  --splitting_mode                        input
% 6.96/1.49  --splitting_grd                         true
% 6.96/1.49  --splitting_cvd                         false
% 6.96/1.49  --splitting_cvd_svl                     false
% 6.96/1.49  --splitting_nvd                         32
% 6.96/1.49  --sub_typing                            true
% 6.96/1.49  --prep_gs_sim                           true
% 6.96/1.49  --prep_unflatten                        true
% 6.96/1.49  --prep_res_sim                          true
% 6.96/1.49  --prep_upred                            true
% 6.96/1.49  --prep_sem_filter                       exhaustive
% 6.96/1.49  --prep_sem_filter_out                   false
% 6.96/1.49  --pred_elim                             true
% 6.96/1.49  --res_sim_input                         true
% 6.96/1.49  --eq_ax_congr_red                       true
% 6.96/1.49  --pure_diseq_elim                       true
% 6.96/1.49  --brand_transform                       false
% 6.96/1.49  --non_eq_to_eq                          false
% 6.96/1.49  --prep_def_merge                        true
% 6.96/1.49  --prep_def_merge_prop_impl              false
% 6.96/1.49  --prep_def_merge_mbd                    true
% 6.96/1.49  --prep_def_merge_tr_red                 false
% 6.96/1.49  --prep_def_merge_tr_cl                  false
% 6.96/1.49  --smt_preprocessing                     true
% 6.96/1.49  --smt_ac_axioms                         fast
% 6.96/1.49  --preprocessed_out                      false
% 6.96/1.49  --preprocessed_stats                    false
% 6.96/1.49  
% 6.96/1.49  ------ Abstraction refinement Options
% 6.96/1.49  
% 6.96/1.49  --abstr_ref                             []
% 6.96/1.49  --abstr_ref_prep                        false
% 6.96/1.49  --abstr_ref_until_sat                   false
% 6.96/1.49  --abstr_ref_sig_restrict                funpre
% 6.96/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.96/1.49  --abstr_ref_under                       []
% 6.96/1.49  
% 6.96/1.49  ------ SAT Options
% 6.96/1.49  
% 6.96/1.49  --sat_mode                              false
% 6.96/1.49  --sat_fm_restart_options                ""
% 6.96/1.49  --sat_gr_def                            false
% 6.96/1.49  --sat_epr_types                         true
% 6.96/1.49  --sat_non_cyclic_types                  false
% 6.96/1.49  --sat_finite_models                     false
% 6.96/1.49  --sat_fm_lemmas                         false
% 6.96/1.49  --sat_fm_prep                           false
% 6.96/1.49  --sat_fm_uc_incr                        true
% 6.96/1.49  --sat_out_model                         small
% 6.96/1.49  --sat_out_clauses                       false
% 6.96/1.49  
% 6.96/1.49  ------ QBF Options
% 6.96/1.49  
% 6.96/1.49  --qbf_mode                              false
% 6.96/1.49  --qbf_elim_univ                         false
% 6.96/1.49  --qbf_dom_inst                          none
% 6.96/1.49  --qbf_dom_pre_inst                      false
% 6.96/1.49  --qbf_sk_in                             false
% 6.96/1.49  --qbf_pred_elim                         true
% 6.96/1.49  --qbf_split                             512
% 6.96/1.49  
% 6.96/1.49  ------ BMC1 Options
% 6.96/1.49  
% 6.96/1.49  --bmc1_incremental                      false
% 6.96/1.49  --bmc1_axioms                           reachable_all
% 6.96/1.49  --bmc1_min_bound                        0
% 6.96/1.49  --bmc1_max_bound                        -1
% 6.96/1.49  --bmc1_max_bound_default                -1
% 6.96/1.49  --bmc1_symbol_reachability              true
% 6.96/1.49  --bmc1_property_lemmas                  false
% 6.96/1.49  --bmc1_k_induction                      false
% 6.96/1.49  --bmc1_non_equiv_states                 false
% 6.96/1.49  --bmc1_deadlock                         false
% 6.96/1.49  --bmc1_ucm                              false
% 6.96/1.49  --bmc1_add_unsat_core                   none
% 6.96/1.49  --bmc1_unsat_core_children              false
% 6.96/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.96/1.49  --bmc1_out_stat                         full
% 6.96/1.49  --bmc1_ground_init                      false
% 6.96/1.49  --bmc1_pre_inst_next_state              false
% 6.96/1.49  --bmc1_pre_inst_state                   false
% 6.96/1.49  --bmc1_pre_inst_reach_state             false
% 6.96/1.49  --bmc1_out_unsat_core                   false
% 6.96/1.49  --bmc1_aig_witness_out                  false
% 6.96/1.49  --bmc1_verbose                          false
% 6.96/1.49  --bmc1_dump_clauses_tptp                false
% 6.96/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.96/1.49  --bmc1_dump_file                        -
% 6.96/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.96/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.96/1.49  --bmc1_ucm_extend_mode                  1
% 6.96/1.49  --bmc1_ucm_init_mode                    2
% 6.96/1.49  --bmc1_ucm_cone_mode                    none
% 6.96/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.96/1.49  --bmc1_ucm_relax_model                  4
% 6.96/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.96/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.96/1.49  --bmc1_ucm_layered_model                none
% 6.96/1.49  --bmc1_ucm_max_lemma_size               10
% 6.96/1.49  
% 6.96/1.49  ------ AIG Options
% 6.96/1.49  
% 6.96/1.49  --aig_mode                              false
% 6.96/1.49  
% 6.96/1.49  ------ Instantiation Options
% 6.96/1.49  
% 6.96/1.49  --instantiation_flag                    true
% 6.96/1.49  --inst_sos_flag                         false
% 6.96/1.49  --inst_sos_phase                        true
% 6.96/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.96/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.96/1.49  --inst_lit_sel_side                     num_symb
% 6.96/1.49  --inst_solver_per_active                1400
% 6.96/1.49  --inst_solver_calls_frac                1.
% 6.96/1.49  --inst_passive_queue_type               priority_queues
% 6.96/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.96/1.49  --inst_passive_queues_freq              [25;2]
% 6.96/1.49  --inst_dismatching                      true
% 6.96/1.49  --inst_eager_unprocessed_to_passive     true
% 6.96/1.49  --inst_prop_sim_given                   true
% 6.96/1.49  --inst_prop_sim_new                     false
% 6.96/1.49  --inst_subs_new                         false
% 6.96/1.49  --inst_eq_res_simp                      false
% 6.96/1.49  --inst_subs_given                       false
% 6.96/1.49  --inst_orphan_elimination               true
% 6.96/1.49  --inst_learning_loop_flag               true
% 6.96/1.49  --inst_learning_start                   3000
% 6.96/1.49  --inst_learning_factor                  2
% 6.96/1.49  --inst_start_prop_sim_after_learn       3
% 6.96/1.49  --inst_sel_renew                        solver
% 6.96/1.49  --inst_lit_activity_flag                true
% 6.96/1.49  --inst_restr_to_given                   false
% 6.96/1.49  --inst_activity_threshold               500
% 6.96/1.49  --inst_out_proof                        true
% 6.96/1.49  
% 6.96/1.49  ------ Resolution Options
% 6.96/1.49  
% 6.96/1.49  --resolution_flag                       true
% 6.96/1.49  --res_lit_sel                           adaptive
% 6.96/1.49  --res_lit_sel_side                      none
% 6.96/1.49  --res_ordering                          kbo
% 6.96/1.49  --res_to_prop_solver                    active
% 6.96/1.49  --res_prop_simpl_new                    false
% 6.96/1.49  --res_prop_simpl_given                  true
% 6.96/1.49  --res_passive_queue_type                priority_queues
% 6.96/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.96/1.49  --res_passive_queues_freq               [15;5]
% 6.96/1.49  --res_forward_subs                      full
% 6.96/1.49  --res_backward_subs                     full
% 6.96/1.49  --res_forward_subs_resolution           true
% 6.96/1.49  --res_backward_subs_resolution          true
% 6.96/1.49  --res_orphan_elimination                true
% 6.96/1.49  --res_time_limit                        2.
% 6.96/1.49  --res_out_proof                         true
% 6.96/1.49  
% 6.96/1.49  ------ Superposition Options
% 6.96/1.49  
% 6.96/1.49  --superposition_flag                    true
% 6.96/1.49  --sup_passive_queue_type                priority_queues
% 6.96/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.96/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.96/1.49  --demod_completeness_check              fast
% 6.96/1.49  --demod_use_ground                      true
% 6.96/1.49  --sup_to_prop_solver                    passive
% 6.96/1.49  --sup_prop_simpl_new                    true
% 6.96/1.49  --sup_prop_simpl_given                  true
% 6.96/1.49  --sup_fun_splitting                     false
% 6.96/1.49  --sup_smt_interval                      50000
% 6.96/1.49  
% 6.96/1.49  ------ Superposition Simplification Setup
% 6.96/1.49  
% 6.96/1.49  --sup_indices_passive                   []
% 6.96/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.96/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.96/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.96/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.96/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.96/1.49  --sup_full_bw                           [BwDemod]
% 6.96/1.49  --sup_immed_triv                        [TrivRules]
% 6.96/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.96/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.96/1.49  --sup_immed_bw_main                     []
% 6.96/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.96/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.96/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.96/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.96/1.49  
% 6.96/1.49  ------ Combination Options
% 6.96/1.49  
% 6.96/1.49  --comb_res_mult                         3
% 6.96/1.49  --comb_sup_mult                         2
% 6.96/1.49  --comb_inst_mult                        10
% 6.96/1.49  
% 6.96/1.49  ------ Debug Options
% 6.96/1.49  
% 6.96/1.49  --dbg_backtrace                         false
% 6.96/1.49  --dbg_dump_prop_clauses                 false
% 6.96/1.49  --dbg_dump_prop_clauses_file            -
% 6.96/1.49  --dbg_out_stat                          false
% 6.96/1.49  ------ Parsing...
% 6.96/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.96/1.49  
% 6.96/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.96/1.49  
% 6.96/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.96/1.49  
% 6.96/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.96/1.49  ------ Proving...
% 6.96/1.49  ------ Problem Properties 
% 6.96/1.49  
% 6.96/1.49  
% 6.96/1.49  clauses                                 22
% 6.96/1.49  conjectures                             7
% 6.96/1.49  EPR                                     4
% 6.96/1.49  Horn                                    21
% 6.96/1.49  unary                                   11
% 6.96/1.49  binary                                  3
% 6.96/1.49  lits                                    58
% 6.96/1.49  lits eq                                 14
% 6.96/1.49  fd_pure                                 0
% 6.96/1.49  fd_pseudo                               0
% 6.96/1.49  fd_cond                                 0
% 6.96/1.49  fd_pseudo_cond                          0
% 6.96/1.49  AC symbols                              0
% 6.96/1.49  
% 6.96/1.49  ------ Schedule dynamic 5 is on 
% 6.96/1.49  
% 6.96/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.96/1.49  
% 6.96/1.49  
% 6.96/1.49  ------ 
% 6.96/1.49  Current options:
% 6.96/1.49  ------ 
% 6.96/1.49  
% 6.96/1.49  ------ Input Options
% 6.96/1.49  
% 6.96/1.49  --out_options                           all
% 6.96/1.49  --tptp_safe_out                         true
% 6.96/1.49  --problem_path                          ""
% 6.96/1.49  --include_path                          ""
% 6.96/1.49  --clausifier                            res/vclausify_rel
% 6.96/1.49  --clausifier_options                    --mode clausify
% 6.96/1.49  --stdin                                 false
% 6.96/1.49  --stats_out                             all
% 6.96/1.49  
% 6.96/1.49  ------ General Options
% 6.96/1.49  
% 6.96/1.49  --fof                                   false
% 6.96/1.49  --time_out_real                         305.
% 6.96/1.49  --time_out_virtual                      -1.
% 6.96/1.49  --symbol_type_check                     false
% 6.96/1.49  --clausify_out                          false
% 6.96/1.49  --sig_cnt_out                           false
% 6.96/1.49  --trig_cnt_out                          false
% 6.96/1.49  --trig_cnt_out_tolerance                1.
% 6.96/1.49  --trig_cnt_out_sk_spl                   false
% 6.96/1.49  --abstr_cl_out                          false
% 6.96/1.49  
% 6.96/1.49  ------ Global Options
% 6.96/1.49  
% 6.96/1.49  --schedule                              default
% 6.96/1.49  --add_important_lit                     false
% 6.96/1.49  --prop_solver_per_cl                    1000
% 6.96/1.49  --min_unsat_core                        false
% 6.96/1.49  --soft_assumptions                      false
% 6.96/1.49  --soft_lemma_size                       3
% 6.96/1.49  --prop_impl_unit_size                   0
% 6.96/1.49  --prop_impl_unit                        []
% 6.96/1.49  --share_sel_clauses                     true
% 6.96/1.49  --reset_solvers                         false
% 6.96/1.49  --bc_imp_inh                            [conj_cone]
% 6.96/1.49  --conj_cone_tolerance                   3.
% 6.96/1.49  --extra_neg_conj                        none
% 6.96/1.49  --large_theory_mode                     true
% 6.96/1.49  --prolific_symb_bound                   200
% 6.96/1.49  --lt_threshold                          2000
% 6.96/1.49  --clause_weak_htbl                      true
% 6.96/1.49  --gc_record_bc_elim                     false
% 6.96/1.49  
% 6.96/1.49  ------ Preprocessing Options
% 6.96/1.49  
% 6.96/1.49  --preprocessing_flag                    true
% 6.96/1.49  --time_out_prep_mult                    0.1
% 6.96/1.49  --splitting_mode                        input
% 6.96/1.49  --splitting_grd                         true
% 6.96/1.49  --splitting_cvd                         false
% 6.96/1.49  --splitting_cvd_svl                     false
% 6.96/1.49  --splitting_nvd                         32
% 6.96/1.49  --sub_typing                            true
% 6.96/1.49  --prep_gs_sim                           true
% 6.96/1.49  --prep_unflatten                        true
% 6.96/1.49  --prep_res_sim                          true
% 6.96/1.49  --prep_upred                            true
% 6.96/1.49  --prep_sem_filter                       exhaustive
% 6.96/1.49  --prep_sem_filter_out                   false
% 6.96/1.49  --pred_elim                             true
% 6.96/1.49  --res_sim_input                         true
% 6.96/1.49  --eq_ax_congr_red                       true
% 6.96/1.49  --pure_diseq_elim                       true
% 6.96/1.49  --brand_transform                       false
% 6.96/1.49  --non_eq_to_eq                          false
% 6.96/1.49  --prep_def_merge                        true
% 6.96/1.49  --prep_def_merge_prop_impl              false
% 6.96/1.49  --prep_def_merge_mbd                    true
% 6.96/1.49  --prep_def_merge_tr_red                 false
% 6.96/1.49  --prep_def_merge_tr_cl                  false
% 6.96/1.49  --smt_preprocessing                     true
% 6.96/1.49  --smt_ac_axioms                         fast
% 6.96/1.49  --preprocessed_out                      false
% 6.96/1.49  --preprocessed_stats                    false
% 6.96/1.49  
% 6.96/1.49  ------ Abstraction refinement Options
% 6.96/1.49  
% 6.96/1.49  --abstr_ref                             []
% 6.96/1.49  --abstr_ref_prep                        false
% 6.96/1.49  --abstr_ref_until_sat                   false
% 6.96/1.49  --abstr_ref_sig_restrict                funpre
% 6.96/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.96/1.49  --abstr_ref_under                       []
% 6.96/1.49  
% 6.96/1.49  ------ SAT Options
% 6.96/1.49  
% 6.96/1.49  --sat_mode                              false
% 6.96/1.49  --sat_fm_restart_options                ""
% 6.96/1.49  --sat_gr_def                            false
% 6.96/1.49  --sat_epr_types                         true
% 6.96/1.49  --sat_non_cyclic_types                  false
% 6.96/1.49  --sat_finite_models                     false
% 6.96/1.49  --sat_fm_lemmas                         false
% 6.96/1.49  --sat_fm_prep                           false
% 6.96/1.49  --sat_fm_uc_incr                        true
% 6.96/1.49  --sat_out_model                         small
% 6.96/1.49  --sat_out_clauses                       false
% 6.96/1.49  
% 6.96/1.49  ------ QBF Options
% 6.96/1.49  
% 6.96/1.49  --qbf_mode                              false
% 6.96/1.49  --qbf_elim_univ                         false
% 6.96/1.49  --qbf_dom_inst                          none
% 6.96/1.49  --qbf_dom_pre_inst                      false
% 6.96/1.49  --qbf_sk_in                             false
% 6.96/1.49  --qbf_pred_elim                         true
% 6.96/1.49  --qbf_split                             512
% 6.96/1.49  
% 6.96/1.49  ------ BMC1 Options
% 6.96/1.49  
% 6.96/1.49  --bmc1_incremental                      false
% 6.96/1.49  --bmc1_axioms                           reachable_all
% 6.96/1.49  --bmc1_min_bound                        0
% 6.96/1.49  --bmc1_max_bound                        -1
% 6.96/1.49  --bmc1_max_bound_default                -1
% 6.96/1.49  --bmc1_symbol_reachability              true
% 6.96/1.49  --bmc1_property_lemmas                  false
% 6.96/1.49  --bmc1_k_induction                      false
% 6.96/1.49  --bmc1_non_equiv_states                 false
% 6.96/1.49  --bmc1_deadlock                         false
% 6.96/1.49  --bmc1_ucm                              false
% 6.96/1.49  --bmc1_add_unsat_core                   none
% 6.96/1.49  --bmc1_unsat_core_children              false
% 6.96/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.96/1.49  --bmc1_out_stat                         full
% 6.96/1.49  --bmc1_ground_init                      false
% 6.96/1.49  --bmc1_pre_inst_next_state              false
% 6.96/1.49  --bmc1_pre_inst_state                   false
% 6.96/1.49  --bmc1_pre_inst_reach_state             false
% 6.96/1.49  --bmc1_out_unsat_core                   false
% 6.96/1.49  --bmc1_aig_witness_out                  false
% 6.96/1.49  --bmc1_verbose                          false
% 6.96/1.49  --bmc1_dump_clauses_tptp                false
% 6.96/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.96/1.49  --bmc1_dump_file                        -
% 6.96/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.96/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.96/1.49  --bmc1_ucm_extend_mode                  1
% 6.96/1.49  --bmc1_ucm_init_mode                    2
% 6.96/1.49  --bmc1_ucm_cone_mode                    none
% 6.96/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.96/1.49  --bmc1_ucm_relax_model                  4
% 6.96/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.96/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.96/1.49  --bmc1_ucm_layered_model                none
% 6.96/1.49  --bmc1_ucm_max_lemma_size               10
% 6.96/1.49  
% 6.96/1.49  ------ AIG Options
% 6.96/1.49  
% 6.96/1.49  --aig_mode                              false
% 6.96/1.49  
% 6.96/1.49  ------ Instantiation Options
% 6.96/1.49  
% 6.96/1.49  --instantiation_flag                    true
% 6.96/1.49  --inst_sos_flag                         false
% 6.96/1.49  --inst_sos_phase                        true
% 6.96/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.96/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.96/1.49  --inst_lit_sel_side                     none
% 6.96/1.49  --inst_solver_per_active                1400
% 6.96/1.49  --inst_solver_calls_frac                1.
% 6.96/1.49  --inst_passive_queue_type               priority_queues
% 6.96/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.96/1.49  --inst_passive_queues_freq              [25;2]
% 6.96/1.49  --inst_dismatching                      true
% 6.96/1.49  --inst_eager_unprocessed_to_passive     true
% 6.96/1.49  --inst_prop_sim_given                   true
% 6.96/1.49  --inst_prop_sim_new                     false
% 6.96/1.49  --inst_subs_new                         false
% 6.96/1.49  --inst_eq_res_simp                      false
% 6.96/1.49  --inst_subs_given                       false
% 6.96/1.49  --inst_orphan_elimination               true
% 6.96/1.49  --inst_learning_loop_flag               true
% 6.96/1.49  --inst_learning_start                   3000
% 6.96/1.49  --inst_learning_factor                  2
% 6.96/1.49  --inst_start_prop_sim_after_learn       3
% 6.96/1.49  --inst_sel_renew                        solver
% 6.96/1.49  --inst_lit_activity_flag                true
% 6.96/1.49  --inst_restr_to_given                   false
% 6.96/1.49  --inst_activity_threshold               500
% 6.96/1.49  --inst_out_proof                        true
% 6.96/1.49  
% 6.96/1.49  ------ Resolution Options
% 6.96/1.49  
% 6.96/1.49  --resolution_flag                       false
% 6.96/1.49  --res_lit_sel                           adaptive
% 6.96/1.49  --res_lit_sel_side                      none
% 6.96/1.49  --res_ordering                          kbo
% 6.96/1.49  --res_to_prop_solver                    active
% 6.96/1.49  --res_prop_simpl_new                    false
% 6.96/1.49  --res_prop_simpl_given                  true
% 6.96/1.49  --res_passive_queue_type                priority_queues
% 6.96/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.96/1.49  --res_passive_queues_freq               [15;5]
% 6.96/1.49  --res_forward_subs                      full
% 6.96/1.49  --res_backward_subs                     full
% 6.96/1.49  --res_forward_subs_resolution           true
% 6.96/1.49  --res_backward_subs_resolution          true
% 6.96/1.49  --res_orphan_elimination                true
% 6.96/1.49  --res_time_limit                        2.
% 6.96/1.49  --res_out_proof                         true
% 6.96/1.49  
% 6.96/1.49  ------ Superposition Options
% 6.96/1.49  
% 6.96/1.49  --superposition_flag                    true
% 6.96/1.49  --sup_passive_queue_type                priority_queues
% 6.96/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.96/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.96/1.49  --demod_completeness_check              fast
% 6.96/1.49  --demod_use_ground                      true
% 6.96/1.49  --sup_to_prop_solver                    passive
% 6.96/1.49  --sup_prop_simpl_new                    true
% 6.96/1.49  --sup_prop_simpl_given                  true
% 6.96/1.49  --sup_fun_splitting                     false
% 6.96/1.49  --sup_smt_interval                      50000
% 6.96/1.49  
% 6.96/1.49  ------ Superposition Simplification Setup
% 6.96/1.49  
% 6.96/1.49  --sup_indices_passive                   []
% 6.96/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.96/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.96/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.96/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.96/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.96/1.49  --sup_full_bw                           [BwDemod]
% 6.96/1.49  --sup_immed_triv                        [TrivRules]
% 6.96/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.96/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.96/1.49  --sup_immed_bw_main                     []
% 6.96/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.96/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.96/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.96/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.96/1.49  
% 6.96/1.49  ------ Combination Options
% 6.96/1.49  
% 6.96/1.49  --comb_res_mult                         3
% 6.96/1.49  --comb_sup_mult                         2
% 6.96/1.49  --comb_inst_mult                        10
% 6.96/1.49  
% 6.96/1.49  ------ Debug Options
% 6.96/1.49  
% 6.96/1.49  --dbg_backtrace                         false
% 6.96/1.49  --dbg_dump_prop_clauses                 false
% 6.96/1.49  --dbg_dump_prop_clauses_file            -
% 6.96/1.49  --dbg_out_stat                          false
% 6.96/1.49  
% 6.96/1.49  
% 6.96/1.49  
% 6.96/1.49  
% 6.96/1.49  ------ Proving...
% 6.96/1.49  
% 6.96/1.49  
% 6.96/1.49  % SZS status Theorem for theBenchmark.p
% 6.96/1.49  
% 6.96/1.49   Resolution empty clause
% 6.96/1.49  
% 6.96/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.96/1.49  
% 6.96/1.49  fof(f12,conjecture,(
% 6.96/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X0) = k1_relat_1(X1)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 6.96/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.49  
% 6.96/1.49  fof(f13,negated_conjecture,(
% 6.96/1.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X0) = k1_relat_1(X1)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 6.96/1.49    inference(negated_conjecture,[],[f12])).
% 6.96/1.49  
% 6.96/1.49  fof(f22,plain,(
% 6.96/1.49    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 6.96/1.49    inference(ennf_transformation,[],[f13])).
% 6.96/1.49  
% 6.96/1.49  fof(f23,plain,(
% 6.96/1.49    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 6.96/1.49    inference(flattening,[],[f22])).
% 6.96/1.49  
% 6.96/1.49  fof(f32,plain,(
% 6.96/1.49    ( ! [X0,X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => (k7_relat_1(X0,sK3) != k7_relat_1(X1,sK3) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,sK3)) & k1_relat_1(X0) = k1_relat_1(X1))) )),
% 6.96/1.49    introduced(choice_axiom,[])).
% 6.96/1.49  
% 6.96/1.49  fof(f31,plain,(
% 6.96/1.49    ( ! [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK2,X2) != k7_relat_1(X0,X2) & ! [X3] : (k1_funct_1(sK2,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK2) = k1_relat_1(X0)) & v1_funct_1(sK2) & v1_relat_1(sK2))) )),
% 6.96/1.49    introduced(choice_axiom,[])).
% 6.96/1.49  
% 6.96/1.49  fof(f30,plain,(
% 6.96/1.49    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(sK1,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(sK1,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK1) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 6.96/1.49    introduced(choice_axiom,[])).
% 6.96/1.49  
% 6.96/1.49  fof(f33,plain,(
% 6.96/1.49    ((k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) & ! [X3] : (k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) | ~r2_hidden(X3,sK3)) & k1_relat_1(sK1) = k1_relat_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 6.96/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f32,f31,f30])).
% 6.96/1.49  
% 6.96/1.49  fof(f51,plain,(
% 6.96/1.49    v1_relat_1(sK1)),
% 6.96/1.49    inference(cnf_transformation,[],[f33])).
% 6.96/1.49  
% 6.96/1.49  fof(f8,axiom,(
% 6.96/1.49    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 6.96/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.49  
% 6.96/1.49  fof(f17,plain,(
% 6.96/1.49    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 6.96/1.49    inference(ennf_transformation,[],[f8])).
% 6.96/1.49  
% 6.96/1.49  fof(f44,plain,(
% 6.96/1.49    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 6.96/1.49    inference(cnf_transformation,[],[f17])).
% 6.96/1.49  
% 6.96/1.49  fof(f3,axiom,(
% 6.96/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.96/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.49  
% 6.96/1.49  fof(f36,plain,(
% 6.96/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.96/1.49    inference(cnf_transformation,[],[f3])).
% 6.96/1.49  
% 6.96/1.49  fof(f2,axiom,(
% 6.96/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 6.96/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.49  
% 6.96/1.49  fof(f35,plain,(
% 6.96/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 6.96/1.49    inference(cnf_transformation,[],[f2])).
% 6.96/1.49  
% 6.96/1.49  fof(f58,plain,(
% 6.96/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 6.96/1.49    inference(definition_unfolding,[],[f36,f35])).
% 6.96/1.49  
% 6.96/1.49  fof(f60,plain,(
% 6.96/1.49    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 6.96/1.49    inference(definition_unfolding,[],[f44,f58])).
% 6.96/1.49  
% 6.96/1.49  fof(f53,plain,(
% 6.96/1.49    v1_relat_1(sK2)),
% 6.96/1.49    inference(cnf_transformation,[],[f33])).
% 6.96/1.49  
% 6.96/1.49  fof(f55,plain,(
% 6.96/1.49    k1_relat_1(sK1) = k1_relat_1(sK2)),
% 6.96/1.49    inference(cnf_transformation,[],[f33])).
% 6.96/1.49  
% 6.96/1.49  fof(f7,axiom,(
% 6.96/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 6.96/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.49  
% 6.96/1.49  fof(f16,plain,(
% 6.96/1.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 6.96/1.49    inference(ennf_transformation,[],[f7])).
% 6.96/1.49  
% 6.96/1.49  fof(f43,plain,(
% 6.96/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 6.96/1.49    inference(cnf_transformation,[],[f16])).
% 6.96/1.49  
% 6.96/1.49  fof(f11,axiom,(
% 6.96/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 6.96/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.49  
% 6.96/1.49  fof(f20,plain,(
% 6.96/1.49    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | (~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.96/1.49    inference(ennf_transformation,[],[f11])).
% 6.96/1.49  
% 6.96/1.49  fof(f21,plain,(
% 6.96/1.49    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.96/1.49    inference(flattening,[],[f20])).
% 6.96/1.49  
% 6.96/1.49  fof(f26,plain,(
% 6.96/1.49    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.96/1.49    inference(nnf_transformation,[],[f21])).
% 6.96/1.49  
% 6.96/1.49  fof(f27,plain,(
% 6.96/1.49    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.96/1.49    inference(rectify,[],[f26])).
% 6.96/1.49  
% 6.96/1.49  fof(f28,plain,(
% 6.96/1.49    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2)))),
% 6.96/1.49    introduced(choice_axiom,[])).
% 6.96/1.49  
% 6.96/1.49  fof(f29,plain,(
% 6.96/1.49    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | (k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.96/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 6.96/1.49  
% 6.96/1.49  fof(f49,plain,(
% 6.96/1.49    ( ! [X2,X0,X1] : (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.96/1.49    inference(cnf_transformation,[],[f29])).
% 6.96/1.49  
% 6.96/1.49  fof(f6,axiom,(
% 6.96/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 6.96/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.49  
% 6.96/1.49  fof(f15,plain,(
% 6.96/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 6.96/1.49    inference(ennf_transformation,[],[f6])).
% 6.96/1.49  
% 6.96/1.49  fof(f24,plain,(
% 6.96/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 6.96/1.49    inference(nnf_transformation,[],[f15])).
% 6.96/1.49  
% 6.96/1.49  fof(f25,plain,(
% 6.96/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 6.96/1.49    inference(flattening,[],[f24])).
% 6.96/1.49  
% 6.96/1.49  fof(f40,plain,(
% 6.96/1.49    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 6.96/1.49    inference(cnf_transformation,[],[f25])).
% 6.96/1.49  
% 6.96/1.49  fof(f56,plain,(
% 6.96/1.49    ( ! [X3] : (k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) | ~r2_hidden(X3,sK3)) )),
% 6.96/1.49    inference(cnf_transformation,[],[f33])).
% 6.96/1.49  
% 6.96/1.49  fof(f54,plain,(
% 6.96/1.49    v1_funct_1(sK2)),
% 6.96/1.49    inference(cnf_transformation,[],[f33])).
% 6.96/1.49  
% 6.96/1.49  fof(f10,axiom,(
% 6.96/1.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 6.96/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.49  
% 6.96/1.49  fof(f46,plain,(
% 6.96/1.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 6.96/1.49    inference(cnf_transformation,[],[f10])).
% 6.96/1.49  
% 6.96/1.49  fof(f4,axiom,(
% 6.96/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 6.96/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.49  
% 6.96/1.49  fof(f14,plain,(
% 6.96/1.49    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.96/1.49    inference(ennf_transformation,[],[f4])).
% 6.96/1.49  
% 6.96/1.49  fof(f37,plain,(
% 6.96/1.49    ( ! [X0,X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 6.96/1.49    inference(cnf_transformation,[],[f14])).
% 6.96/1.49  
% 6.96/1.49  fof(f5,axiom,(
% 6.96/1.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 6.96/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.49  
% 6.96/1.49  fof(f38,plain,(
% 6.96/1.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 6.96/1.49    inference(cnf_transformation,[],[f5])).
% 6.96/1.49  
% 6.96/1.49  fof(f1,axiom,(
% 6.96/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.96/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.49  
% 6.96/1.49  fof(f34,plain,(
% 6.96/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.96/1.49    inference(cnf_transformation,[],[f1])).
% 6.96/1.49  
% 6.96/1.49  fof(f59,plain,(
% 6.96/1.49    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0))) )),
% 6.96/1.49    inference(definition_unfolding,[],[f34,f58,f58])).
% 6.96/1.49  
% 6.96/1.49  fof(f52,plain,(
% 6.96/1.49    v1_funct_1(sK1)),
% 6.96/1.49    inference(cnf_transformation,[],[f33])).
% 6.96/1.49  
% 6.96/1.49  fof(f50,plain,(
% 6.96/1.49    ( ! [X2,X0,X1] : (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2)) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.96/1.49    inference(cnf_transformation,[],[f29])).
% 6.96/1.49  
% 6.96/1.49  fof(f57,plain,(
% 6.96/1.49    k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3)),
% 6.96/1.49    inference(cnf_transformation,[],[f33])).
% 6.96/1.49  
% 6.96/1.49  cnf(c_21,negated_conjecture,
% 6.96/1.49      ( v1_relat_1(sK1) ),
% 6.96/1.49      inference(cnf_transformation,[],[f51]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_524,plain,
% 6.96/1.49      ( v1_relat_1(sK1) = iProver_top ),
% 6.96/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_8,plain,
% 6.96/1.49      ( ~ v1_relat_1(X0)
% 6.96/1.49      | k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 6.96/1.49      inference(cnf_transformation,[],[f60]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_535,plain,
% 6.96/1.49      ( k1_setfam_1(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 6.96/1.49      | v1_relat_1(X0) != iProver_top ),
% 6.96/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_1419,plain,
% 6.96/1.49      ( k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 6.96/1.49      inference(superposition,[status(thm)],[c_524,c_535]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_19,negated_conjecture,
% 6.96/1.49      ( v1_relat_1(sK2) ),
% 6.96/1.49      inference(cnf_transformation,[],[f53]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_526,plain,
% 6.96/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 6.96/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_1418,plain,
% 6.96/1.49      ( k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 6.96/1.49      inference(superposition,[status(thm)],[c_526,c_535]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_17,negated_conjecture,
% 6.96/1.49      ( k1_relat_1(sK1) = k1_relat_1(sK2) ),
% 6.96/1.49      inference(cnf_transformation,[],[f55]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_1461,plain,
% 6.96/1.49      ( k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 6.96/1.49      inference(light_normalisation,[status(thm)],[c_1418,c_17]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_2465,plain,
% 6.96/1.49      ( k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 6.96/1.49      inference(demodulation,[status(thm)],[c_1419,c_1461]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_7,plain,
% 6.96/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
% 6.96/1.49      | ~ v1_relat_1(X0) ),
% 6.96/1.49      inference(cnf_transformation,[],[f43]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_536,plain,
% 6.96/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 6.96/1.49      | v1_relat_1(X0) != iProver_top ),
% 6.96/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_1058,plain,
% 6.96/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK1)) = iProver_top
% 6.96/1.49      | v1_relat_1(sK2) != iProver_top ),
% 6.96/1.49      inference(superposition,[status(thm)],[c_17,c_536]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_24,plain,
% 6.96/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 6.96/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_785,plain,
% 6.96/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK2))
% 6.96/1.49      | ~ v1_relat_1(sK2) ),
% 6.96/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_786,plain,
% 6.96/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK2)) = iProver_top
% 6.96/1.49      | v1_relat_1(sK2) != iProver_top ),
% 6.96/1.49      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_213,plain,
% 6.96/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.96/1.49      theory(equality) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_708,plain,
% 6.96/1.49      ( r1_tarski(X0,X1)
% 6.96/1.49      | ~ r1_tarski(k1_relat_1(k7_relat_1(X2,X3)),k1_relat_1(X2))
% 6.96/1.49      | X1 != k1_relat_1(X2)
% 6.96/1.49      | X0 != k1_relat_1(k7_relat_1(X2,X3)) ),
% 6.96/1.49      inference(instantiation,[status(thm)],[c_213]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_767,plain,
% 6.96/1.49      ( r1_tarski(X0,k1_relat_1(sK1))
% 6.96/1.49      | ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,X1)),k1_relat_1(sK2))
% 6.96/1.49      | X0 != k1_relat_1(k7_relat_1(sK2,X1))
% 6.96/1.49      | k1_relat_1(sK1) != k1_relat_1(sK2) ),
% 6.96/1.49      inference(instantiation,[status(thm)],[c_708]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_928,plain,
% 6.96/1.49      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK2))
% 6.96/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK1))
% 6.96/1.49      | k1_relat_1(k7_relat_1(sK2,X0)) != k1_relat_1(k7_relat_1(sK2,X0))
% 6.96/1.49      | k1_relat_1(sK1) != k1_relat_1(sK2) ),
% 6.96/1.49      inference(instantiation,[status(thm)],[c_767]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_930,plain,
% 6.96/1.49      ( k1_relat_1(k7_relat_1(sK2,X0)) != k1_relat_1(k7_relat_1(sK2,X0))
% 6.96/1.49      | k1_relat_1(sK1) != k1_relat_1(sK2)
% 6.96/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK2)) != iProver_top
% 6.96/1.49      | r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK1)) = iProver_top ),
% 6.96/1.49      inference(predicate_to_equality,[status(thm)],[c_928]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_204,plain,( X0 = X0 ),theory(equality) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_773,plain,
% 6.96/1.49      ( k1_relat_1(X0) = k1_relat_1(X0) ),
% 6.96/1.49      inference(instantiation,[status(thm)],[c_204]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_929,plain,
% 6.96/1.49      ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 6.96/1.49      inference(instantiation,[status(thm)],[c_773]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_1304,plain,
% 6.96/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK1)) = iProver_top ),
% 6.96/1.49      inference(global_propositional_subsumption,
% 6.96/1.49                [status(thm)],
% 6.96/1.49                [c_1058,c_24,c_17,c_786,c_930,c_929]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_2492,plain,
% 6.96/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1)) = iProver_top ),
% 6.96/1.49      inference(demodulation,[status(thm)],[c_2465,c_1304]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_13,plain,
% 6.96/1.49      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 6.96/1.49      | ~ r1_tarski(X0,k1_relat_1(X2))
% 6.96/1.49      | r2_hidden(sK0(X2,X1,X0),X0)
% 6.96/1.49      | ~ v1_funct_1(X1)
% 6.96/1.49      | ~ v1_funct_1(X2)
% 6.96/1.49      | ~ v1_relat_1(X1)
% 6.96/1.49      | ~ v1_relat_1(X2)
% 6.96/1.49      | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
% 6.96/1.49      inference(cnf_transformation,[],[f49]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_530,plain,
% 6.96/1.49      ( k7_relat_1(X0,X1) = k7_relat_1(X2,X1)
% 6.96/1.49      | r1_tarski(X1,k1_relat_1(X2)) != iProver_top
% 6.96/1.49      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 6.96/1.49      | r2_hidden(sK0(X0,X2,X1),X1) = iProver_top
% 6.96/1.49      | v1_funct_1(X2) != iProver_top
% 6.96/1.49      | v1_funct_1(X0) != iProver_top
% 6.96/1.49      | v1_relat_1(X2) != iProver_top
% 6.96/1.49      | v1_relat_1(X0) != iProver_top ),
% 6.96/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_6,plain,
% 6.96/1.49      ( r2_hidden(X0,X1)
% 6.96/1.49      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 6.96/1.49      | ~ v1_relat_1(X2) ),
% 6.96/1.49      inference(cnf_transformation,[],[f40]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_537,plain,
% 6.96/1.49      ( r2_hidden(X0,X1) = iProver_top
% 6.96/1.49      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
% 6.96/1.49      | v1_relat_1(X2) != iProver_top ),
% 6.96/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_2131,plain,
% 6.96/1.49      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X3,k1_relat_1(k7_relat_1(X1,X2)))
% 6.96/1.49      | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X3)) != iProver_top
% 6.96/1.49      | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X0)) != iProver_top
% 6.96/1.49      | r2_hidden(sK0(X3,X0,k1_relat_1(k7_relat_1(X1,X2))),X2) = iProver_top
% 6.96/1.49      | v1_funct_1(X3) != iProver_top
% 6.96/1.49      | v1_funct_1(X0) != iProver_top
% 6.96/1.49      | v1_relat_1(X1) != iProver_top
% 6.96/1.49      | v1_relat_1(X3) != iProver_top
% 6.96/1.49      | v1_relat_1(X0) != iProver_top ),
% 6.96/1.49      inference(superposition,[status(thm)],[c_530,c_537]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_16,negated_conjecture,
% 6.96/1.49      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ),
% 6.96/1.49      inference(cnf_transformation,[],[f56]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_528,plain,
% 6.96/1.49      ( k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
% 6.96/1.49      | r2_hidden(X0,sK3) != iProver_top ),
% 6.96/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.96/1.49  
% 6.96/1.49  cnf(c_19307,plain,
% 6.96/1.49      ( k1_funct_1(sK2,sK0(X0,X1,k1_relat_1(k7_relat_1(X2,sK3)))) = k1_funct_1(sK1,sK0(X0,X1,k1_relat_1(k7_relat_1(X2,sK3))))
% 6.96/1.50      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X2,sK3))) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,sK3)))
% 6.96/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X2,sK3)),k1_relat_1(X0)) != iProver_top
% 6.96/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X2,sK3)),k1_relat_1(X1)) != iProver_top
% 6.96/1.50      | v1_funct_1(X0) != iProver_top
% 6.96/1.50      | v1_funct_1(X1) != iProver_top
% 6.96/1.50      | v1_relat_1(X2) != iProver_top
% 6.96/1.50      | v1_relat_1(X0) != iProver_top
% 6.96/1.50      | v1_relat_1(X1) != iProver_top ),
% 6.96/1.50      inference(superposition,[status(thm)],[c_2131,c_528]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_20730,plain,
% 6.96/1.50      ( k1_funct_1(sK1,sK0(sK2,X0,k1_relat_1(k7_relat_1(X1,sK3)))) = k1_funct_1(sK2,sK0(sK2,X0,k1_relat_1(k7_relat_1(X1,sK3))))
% 6.96/1.50      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK3))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(X1,sK3)))
% 6.96/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK3)),k1_relat_1(X0)) != iProver_top
% 6.96/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK3)),k1_relat_1(sK1)) != iProver_top
% 6.96/1.50      | v1_funct_1(X0) != iProver_top
% 6.96/1.50      | v1_funct_1(sK2) != iProver_top
% 6.96/1.50      | v1_relat_1(X0) != iProver_top
% 6.96/1.50      | v1_relat_1(X1) != iProver_top
% 6.96/1.50      | v1_relat_1(sK2) != iProver_top ),
% 6.96/1.50      inference(superposition,[status(thm)],[c_17,c_19307]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_18,negated_conjecture,
% 6.96/1.50      ( v1_funct_1(sK2) ),
% 6.96/1.50      inference(cnf_transformation,[],[f54]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_25,plain,
% 6.96/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 6.96/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_21240,plain,
% 6.96/1.50      ( v1_relat_1(X1) != iProver_top
% 6.96/1.50      | v1_relat_1(X0) != iProver_top
% 6.96/1.50      | k1_funct_1(sK1,sK0(sK2,X0,k1_relat_1(k7_relat_1(X1,sK3)))) = k1_funct_1(sK2,sK0(sK2,X0,k1_relat_1(k7_relat_1(X1,sK3))))
% 6.96/1.50      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK3))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(X1,sK3)))
% 6.96/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK3)),k1_relat_1(X0)) != iProver_top
% 6.96/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK3)),k1_relat_1(sK1)) != iProver_top
% 6.96/1.50      | v1_funct_1(X0) != iProver_top ),
% 6.96/1.50      inference(global_propositional_subsumption,
% 6.96/1.50                [status(thm)],
% 6.96/1.50                [c_20730,c_24,c_25]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_21241,plain,
% 6.96/1.50      ( k1_funct_1(sK1,sK0(sK2,X0,k1_relat_1(k7_relat_1(X1,sK3)))) = k1_funct_1(sK2,sK0(sK2,X0,k1_relat_1(k7_relat_1(X1,sK3))))
% 6.96/1.50      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK3))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(X1,sK3)))
% 6.96/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK3)),k1_relat_1(X0)) != iProver_top
% 6.96/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK3)),k1_relat_1(sK1)) != iProver_top
% 6.96/1.50      | v1_funct_1(X0) != iProver_top
% 6.96/1.50      | v1_relat_1(X1) != iProver_top
% 6.96/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.96/1.50      inference(renaming,[status(thm)],[c_21240]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_21255,plain,
% 6.96/1.50      ( k1_funct_1(sK2,sK0(sK2,sK1,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK2,sK1,k1_relat_1(k7_relat_1(sK1,sK3))))
% 6.96/1.50      | k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
% 6.96/1.50      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
% 6.96/1.50      | v1_funct_1(sK1) != iProver_top
% 6.96/1.50      | v1_relat_1(sK1) != iProver_top ),
% 6.96/1.50      inference(superposition,[status(thm)],[c_2492,c_21241]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_11,plain,
% 6.96/1.50      ( v1_relat_1(k6_relat_1(X0)) ),
% 6.96/1.50      inference(cnf_transformation,[],[f46]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_532,plain,
% 6.96/1.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 6.96/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_1,plain,
% 6.96/1.50      ( ~ v1_relat_1(X0)
% 6.96/1.50      | ~ v1_relat_1(X1)
% 6.96/1.50      | k7_relat_1(X1,k1_relat_1(k7_relat_1(X0,k1_relat_1(X1)))) = k7_relat_1(X1,k1_relat_1(X0)) ),
% 6.96/1.50      inference(cnf_transformation,[],[f37]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_540,plain,
% 6.96/1.50      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1))
% 6.96/1.50      | v1_relat_1(X0) != iProver_top
% 6.96/1.50      | v1_relat_1(X1) != iProver_top ),
% 6.96/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_5597,plain,
% 6.96/1.50      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
% 6.96/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.96/1.50      inference(superposition,[status(thm)],[c_532,c_540]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_3,plain,
% 6.96/1.50      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 6.96/1.50      inference(cnf_transformation,[],[f38]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_5610,plain,
% 6.96/1.50      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(X0)))) = k7_relat_1(X0,X1)
% 6.96/1.50      | v1_relat_1(X0) != iProver_top ),
% 6.96/1.50      inference(demodulation,[status(thm)],[c_5597,c_3]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_5787,plain,
% 6.96/1.50      ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)))) = k7_relat_1(sK1,X0) ),
% 6.96/1.50      inference(superposition,[status(thm)],[c_524,c_5610]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_0,plain,
% 6.96/1.50      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
% 6.96/1.50      inference(cnf_transformation,[],[f59]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_1417,plain,
% 6.96/1.50      ( k1_setfam_1(k1_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 6.96/1.50      inference(superposition,[status(thm)],[c_532,c_535]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_1426,plain,
% 6.96/1.50      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 6.96/1.50      inference(light_normalisation,[status(thm)],[c_1417,c_3]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_1440,plain,
% 6.96/1.50      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 6.96/1.50      inference(superposition,[status(thm)],[c_0,c_1426]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_2472,plain,
% 6.96/1.50      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 6.96/1.50      inference(superposition,[status(thm)],[c_1419,c_1440]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_5789,plain,
% 6.96/1.50      ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
% 6.96/1.50      inference(light_normalisation,[status(thm)],[c_5787,c_2472]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_5786,plain,
% 6.96/1.50      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2)))) = k7_relat_1(sK2,X0) ),
% 6.96/1.50      inference(superposition,[status(thm)],[c_526,c_5610]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_5792,plain,
% 6.96/1.50      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK2,X0) ),
% 6.96/1.50      inference(light_normalisation,[status(thm)],[c_5786,c_17,c_2472]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_21571,plain,
% 6.96/1.50      ( k1_funct_1(sK2,sK0(sK2,sK1,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK2,sK1,k1_relat_1(k7_relat_1(sK1,sK3))))
% 6.96/1.50      | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 6.96/1.50      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
% 6.96/1.50      | v1_funct_1(sK1) != iProver_top
% 6.96/1.50      | v1_relat_1(sK1) != iProver_top ),
% 6.96/1.50      inference(demodulation,[status(thm)],[c_21255,c_5789,c_5792]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_22,plain,
% 6.96/1.50      ( v1_relat_1(sK1) = iProver_top ),
% 6.96/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_20,negated_conjecture,
% 6.96/1.50      ( v1_funct_1(sK1) ),
% 6.96/1.50      inference(cnf_transformation,[],[f52]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_23,plain,
% 6.96/1.50      ( v1_funct_1(sK1) = iProver_top ),
% 6.96/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_21966,plain,
% 6.96/1.50      ( k1_funct_1(sK2,sK0(sK2,sK1,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK2,sK1,k1_relat_1(k7_relat_1(sK1,sK3))))
% 6.96/1.50      | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 6.96/1.50      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top ),
% 6.96/1.50      inference(global_propositional_subsumption,
% 6.96/1.50                [status(thm)],
% 6.96/1.50                [c_21571,c_22,c_23]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_21973,plain,
% 6.96/1.50      ( k1_funct_1(sK2,sK0(sK2,sK1,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK2,sK1,k1_relat_1(k7_relat_1(sK1,sK3))))
% 6.96/1.50      | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3) ),
% 6.96/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_21966,c_2492]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_12,plain,
% 6.96/1.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 6.96/1.50      | ~ r1_tarski(X0,k1_relat_1(X2))
% 6.96/1.50      | ~ v1_funct_1(X1)
% 6.96/1.50      | ~ v1_funct_1(X2)
% 6.96/1.50      | ~ v1_relat_1(X1)
% 6.96/1.50      | ~ v1_relat_1(X2)
% 6.96/1.50      | k1_funct_1(X1,sK0(X2,X1,X0)) != k1_funct_1(X2,sK0(X2,X1,X0))
% 6.96/1.50      | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
% 6.96/1.50      inference(cnf_transformation,[],[f50]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_531,plain,
% 6.96/1.50      ( k1_funct_1(X0,sK0(X1,X0,X2)) != k1_funct_1(X1,sK0(X1,X0,X2))
% 6.96/1.50      | k7_relat_1(X1,X2) = k7_relat_1(X0,X2)
% 6.96/1.50      | r1_tarski(X2,k1_relat_1(X0)) != iProver_top
% 6.96/1.50      | r1_tarski(X2,k1_relat_1(X1)) != iProver_top
% 6.96/1.50      | v1_funct_1(X0) != iProver_top
% 6.96/1.50      | v1_funct_1(X1) != iProver_top
% 6.96/1.50      | v1_relat_1(X0) != iProver_top
% 6.96/1.50      | v1_relat_1(X1) != iProver_top ),
% 6.96/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_21974,plain,
% 6.96/1.50      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
% 6.96/1.50      | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 6.96/1.50      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK2)) != iProver_top
% 6.96/1.50      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
% 6.96/1.50      | v1_funct_1(sK2) != iProver_top
% 6.96/1.50      | v1_funct_1(sK1) != iProver_top
% 6.96/1.50      | v1_relat_1(sK2) != iProver_top
% 6.96/1.50      | v1_relat_1(sK1) != iProver_top ),
% 6.96/1.50      inference(superposition,[status(thm)],[c_21973,c_531]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_21975,plain,
% 6.96/1.50      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
% 6.96/1.50      | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 6.96/1.50      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
% 6.96/1.50      | v1_funct_1(sK2) != iProver_top
% 6.96/1.50      | v1_funct_1(sK1) != iProver_top
% 6.96/1.50      | v1_relat_1(sK2) != iProver_top
% 6.96/1.50      | v1_relat_1(sK1) != iProver_top ),
% 6.96/1.50      inference(light_normalisation,[status(thm)],[c_21974,c_17]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_21976,plain,
% 6.96/1.50      ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 6.96/1.50      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
% 6.96/1.50      | v1_funct_1(sK2) != iProver_top
% 6.96/1.50      | v1_funct_1(sK1) != iProver_top
% 6.96/1.50      | v1_relat_1(sK2) != iProver_top
% 6.96/1.50      | v1_relat_1(sK1) != iProver_top ),
% 6.96/1.50      inference(demodulation,[status(thm)],[c_21975,c_5789,c_5792]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_21979,plain,
% 6.96/1.50      ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 6.96/1.50      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top ),
% 6.96/1.50      inference(global_propositional_subsumption,
% 6.96/1.50                [status(thm)],
% 6.96/1.50                [c_21976,c_22,c_23,c_24,c_25]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_21985,plain,
% 6.96/1.50      ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3) ),
% 6.96/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_21979,c_2492]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_15,negated_conjecture,
% 6.96/1.50      ( k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
% 6.96/1.50      inference(cnf_transformation,[],[f57]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_21988,plain,
% 6.96/1.50      ( k7_relat_1(sK1,sK3) != k7_relat_1(sK1,sK3) ),
% 6.96/1.50      inference(demodulation,[status(thm)],[c_21985,c_15]) ).
% 6.96/1.50  
% 6.96/1.50  cnf(c_21989,plain,
% 6.96/1.50      ( $false ),
% 6.96/1.50      inference(equality_resolution_simp,[status(thm)],[c_21988]) ).
% 6.96/1.50  
% 6.96/1.50  
% 6.96/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 6.96/1.50  
% 6.96/1.50  ------                               Statistics
% 6.96/1.50  
% 6.96/1.50  ------ General
% 6.96/1.50  
% 6.96/1.50  abstr_ref_over_cycles:                  0
% 6.96/1.50  abstr_ref_under_cycles:                 0
% 6.96/1.50  gc_basic_clause_elim:                   0
% 6.96/1.50  forced_gc_time:                         0
% 6.96/1.50  parsing_time:                           0.011
% 6.96/1.50  unif_index_cands_time:                  0.
% 6.96/1.50  unif_index_add_time:                    0.
% 6.96/1.50  orderings_time:                         0.
% 6.96/1.50  out_proof_time:                         0.009
% 6.96/1.50  total_time:                             0.66
% 6.96/1.50  num_of_symbols:                         46
% 6.96/1.50  num_of_terms:                           20444
% 6.96/1.50  
% 6.96/1.50  ------ Preprocessing
% 6.96/1.50  
% 6.96/1.50  num_of_splits:                          0
% 6.96/1.50  num_of_split_atoms:                     0
% 6.96/1.50  num_of_reused_defs:                     0
% 6.96/1.50  num_eq_ax_congr_red:                    10
% 6.96/1.50  num_of_sem_filtered_clauses:            1
% 6.96/1.50  num_of_subtypes:                        0
% 6.96/1.50  monotx_restored_types:                  0
% 6.96/1.50  sat_num_of_epr_types:                   0
% 6.96/1.50  sat_num_of_non_cyclic_types:            0
% 6.96/1.50  sat_guarded_non_collapsed_types:        0
% 6.96/1.50  num_pure_diseq_elim:                    0
% 6.96/1.50  simp_replaced_by:                       0
% 6.96/1.50  res_preprocessed:                       91
% 6.96/1.50  prep_upred:                             0
% 6.96/1.50  prep_unflattend:                        0
% 6.96/1.50  smt_new_axioms:                         0
% 6.96/1.50  pred_elim_cands:                        4
% 6.96/1.50  pred_elim:                              0
% 6.96/1.50  pred_elim_cl:                           0
% 6.96/1.50  pred_elim_cycles:                       1
% 6.96/1.50  merged_defs:                            0
% 6.96/1.50  merged_defs_ncl:                        0
% 6.96/1.50  bin_hyper_res:                          0
% 6.96/1.50  prep_cycles:                            3
% 6.96/1.50  pred_elim_time:                         0.
% 6.96/1.50  splitting_time:                         0.
% 6.96/1.50  sem_filter_time:                        0.
% 6.96/1.50  monotx_time:                            0.001
% 6.96/1.50  subtype_inf_time:                       0.
% 6.96/1.50  
% 6.96/1.50  ------ Problem properties
% 6.96/1.50  
% 6.96/1.50  clauses:                                22
% 6.96/1.50  conjectures:                            7
% 6.96/1.50  epr:                                    4
% 6.96/1.50  horn:                                   21
% 6.96/1.50  ground:                                 6
% 6.96/1.50  unary:                                  11
% 6.96/1.50  binary:                                 3
% 6.96/1.50  lits:                                   58
% 6.96/1.50  lits_eq:                                14
% 6.96/1.50  fd_pure:                                0
% 6.96/1.50  fd_pseudo:                              0
% 6.96/1.50  fd_cond:                                0
% 6.96/1.50  fd_pseudo_cond:                         0
% 6.96/1.50  ac_symbols:                             0
% 6.96/1.50  
% 6.96/1.50  ------ Propositional Solver
% 6.96/1.50  
% 6.96/1.50  prop_solver_calls:                      25
% 6.96/1.50  prop_fast_solver_calls:                 1352
% 6.96/1.50  smt_solver_calls:                       0
% 6.96/1.50  smt_fast_solver_calls:                  0
% 6.96/1.50  prop_num_of_clauses:                    5845
% 6.96/1.50  prop_preprocess_simplified:             11685
% 6.96/1.50  prop_fo_subsumed:                       68
% 6.96/1.50  prop_solver_time:                       0.
% 6.96/1.50  smt_solver_time:                        0.
% 6.96/1.50  smt_fast_solver_time:                   0.
% 6.96/1.50  prop_fast_solver_time:                  0.
% 6.96/1.50  prop_unsat_core_time:                   0.
% 6.96/1.50  
% 6.96/1.50  ------ QBF
% 6.96/1.50  
% 6.96/1.50  qbf_q_res:                              0
% 6.96/1.50  qbf_num_tautologies:                    0
% 6.96/1.50  qbf_prep_cycles:                        0
% 6.96/1.50  
% 6.96/1.50  ------ BMC1
% 6.96/1.50  
% 6.96/1.50  bmc1_current_bound:                     -1
% 6.96/1.50  bmc1_last_solved_bound:                 -1
% 6.96/1.50  bmc1_unsat_core_size:                   -1
% 6.96/1.50  bmc1_unsat_core_parents_size:           -1
% 6.96/1.50  bmc1_merge_next_fun:                    0
% 6.96/1.50  bmc1_unsat_core_clauses_time:           0.
% 6.96/1.50  
% 6.96/1.50  ------ Instantiation
% 6.96/1.50  
% 6.96/1.50  inst_num_of_clauses:                    1920
% 6.96/1.50  inst_num_in_passive:                    492
% 6.96/1.50  inst_num_in_active:                     734
% 6.96/1.50  inst_num_in_unprocessed:                694
% 6.96/1.50  inst_num_of_loops:                      760
% 6.96/1.50  inst_num_of_learning_restarts:          0
% 6.96/1.50  inst_num_moves_active_passive:          24
% 6.96/1.50  inst_lit_activity:                      0
% 6.96/1.50  inst_lit_activity_moves:                0
% 6.96/1.50  inst_num_tautologies:                   0
% 6.96/1.50  inst_num_prop_implied:                  0
% 6.96/1.50  inst_num_existing_simplified:           0
% 6.96/1.50  inst_num_eq_res_simplified:             0
% 6.96/1.50  inst_num_child_elim:                    0
% 6.96/1.50  inst_num_of_dismatching_blockings:      3836
% 6.96/1.50  inst_num_of_non_proper_insts:           3136
% 6.96/1.50  inst_num_of_duplicates:                 0
% 6.96/1.50  inst_inst_num_from_inst_to_res:         0
% 6.96/1.50  inst_dismatching_checking_time:         0.
% 6.96/1.50  
% 6.96/1.50  ------ Resolution
% 6.96/1.50  
% 6.96/1.50  res_num_of_clauses:                     0
% 6.96/1.50  res_num_in_passive:                     0
% 6.96/1.50  res_num_in_active:                      0
% 6.96/1.50  res_num_of_loops:                       94
% 6.96/1.50  res_forward_subset_subsumed:            325
% 6.96/1.50  res_backward_subset_subsumed:           0
% 6.96/1.50  res_forward_subsumed:                   0
% 6.96/1.50  res_backward_subsumed:                  0
% 6.96/1.50  res_forward_subsumption_resolution:     0
% 6.96/1.50  res_backward_subsumption_resolution:    0
% 6.96/1.50  res_clause_to_clause_subsumption:       1684
% 6.96/1.50  res_orphan_elimination:                 0
% 6.96/1.50  res_tautology_del:                      271
% 6.96/1.50  res_num_eq_res_simplified:              0
% 6.96/1.50  res_num_sel_changes:                    0
% 6.96/1.50  res_moves_from_active_to_pass:          0
% 6.96/1.50  
% 6.96/1.50  ------ Superposition
% 6.96/1.50  
% 6.96/1.50  sup_time_total:                         0.
% 6.96/1.50  sup_time_generating:                    0.
% 6.96/1.50  sup_time_sim_full:                      0.
% 6.96/1.50  sup_time_sim_immed:                     0.
% 6.96/1.50  
% 6.96/1.50  sup_num_of_clauses:                     369
% 6.96/1.50  sup_num_in_active:                      134
% 6.96/1.50  sup_num_in_passive:                     235
% 6.96/1.50  sup_num_of_loops:                       151
% 6.96/1.50  sup_fw_superposition:                   588
% 6.96/1.50  sup_bw_superposition:                   407
% 6.96/1.50  sup_immediate_simplified:               379
% 6.96/1.50  sup_given_eliminated:                   1
% 6.96/1.50  comparisons_done:                       0
% 6.96/1.50  comparisons_avoided:                    38
% 6.96/1.50  
% 6.96/1.50  ------ Simplifications
% 6.96/1.50  
% 6.96/1.50  
% 6.96/1.50  sim_fw_subset_subsumed:                 19
% 6.96/1.50  sim_bw_subset_subsumed:                 9
% 6.96/1.50  sim_fw_subsumed:                        74
% 6.96/1.50  sim_bw_subsumed:                        4
% 6.96/1.50  sim_fw_subsumption_res:                 34
% 6.96/1.50  sim_bw_subsumption_res:                 2
% 6.96/1.50  sim_tautology_del:                      64
% 6.96/1.50  sim_eq_tautology_del:                   39
% 6.96/1.50  sim_eq_res_simp:                        0
% 6.96/1.50  sim_fw_demodulated:                     163
% 6.96/1.50  sim_bw_demodulated:                     17
% 6.96/1.50  sim_light_normalised:                   226
% 6.96/1.50  sim_joinable_taut:                      0
% 6.96/1.50  sim_joinable_simp:                      0
% 6.96/1.50  sim_ac_normalised:                      0
% 6.96/1.50  sim_smt_subsumption:                    0
% 6.96/1.50  
%------------------------------------------------------------------------------
