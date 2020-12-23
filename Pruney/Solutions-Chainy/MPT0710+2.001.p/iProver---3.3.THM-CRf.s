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
% DateTime   : Thu Dec  3 11:52:41 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  157 (6699 expanded)
%              Number of clauses        :  108 (1647 expanded)
%              Number of leaves         :   16 (1843 expanded)
%              Depth                    :   36
%              Number of atoms          :  585 (54077 expanded)
%              Number of equality atoms :  319 (19143 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <~> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <~> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
              & ( ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
              & ( ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
              & ( ! [X4] :
                    ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                    | ~ r2_hidden(X4,X2) )
                | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK4) != k1_funct_1(X1,sK4)
        & r2_hidden(sK4,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                & r2_hidden(X3,X2) )
            | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
          & ( ! [X4] :
                ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                | ~ r2_hidden(X4,X2) )
            | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
          & r1_tarski(X2,k1_relat_1(X1))
          & r1_tarski(X2,k1_relat_1(X0)) )
     => ( ( ? [X3] :
              ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
              & r2_hidden(X3,sK3) )
          | k7_relat_1(X0,sK3) != k7_relat_1(X1,sK3) )
        & ( ! [X4] :
              ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
              | ~ r2_hidden(X4,sK3) )
          | k7_relat_1(X0,sK3) = k7_relat_1(X1,sK3) )
        & r1_tarski(sK3,k1_relat_1(X1))
        & r1_tarski(sK3,k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
              & ( ! [X4] :
                    ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                    | ~ r2_hidden(X4,X2) )
                | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( k1_funct_1(sK2,X3) != k1_funct_1(X0,X3)
                  & r2_hidden(X3,X2) )
              | k7_relat_1(sK2,X2) != k7_relat_1(X0,X2) )
            & ( ! [X4] :
                  ( k1_funct_1(sK2,X4) = k1_funct_1(X0,X4)
                  | ~ r2_hidden(X4,X2) )
              | k7_relat_1(sK2,X2) = k7_relat_1(X0,X2) )
            & r1_tarski(X2,k1_relat_1(sK2))
            & r1_tarski(X2,k1_relat_1(X0)) )
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
                & r1_tarski(X2,k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k1_funct_1(sK1,X3) != k1_funct_1(X1,X3)
                    & r2_hidden(X3,X2) )
                | k7_relat_1(sK1,X2) != k7_relat_1(X1,X2) )
              & ( ! [X4] :
                    ( k1_funct_1(sK1,X4) = k1_funct_1(X1,X4)
                    | ~ r2_hidden(X4,X2) )
                | k7_relat_1(sK1,X2) = k7_relat_1(X1,X2) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(sK1)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ( k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4)
        & r2_hidden(sK4,sK3) )
      | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) )
    & ( ! [X4] :
          ( k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
          | ~ r2_hidden(X4,sK3) )
      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) )
    & r1_tarski(sK3,k1_relat_1(sK2))
    & r1_tarski(sK3,k1_relat_1(sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f28,f27,f26,f25])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    r1_tarski(sK3,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & k3_xboole_0(k1_relat_1(X2),X0) = k1_relat_1(X1) )
           => k7_relat_1(X2,X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ? [X3] :
              ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
              & r2_hidden(X3,k1_relat_1(X1)) )
          | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ? [X3] :
              ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
              & r2_hidden(X3,k1_relat_1(X1)) )
          | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f20,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2))
        & r2_hidden(sK0(X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ( k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2))
            & r2_hidden(sK0(X1,X2),k1_relat_1(X1)) )
          | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f20])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = X1
      | r2_hidden(sK0(X1,X2),k1_relat_1(X1))
      | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = X1
      | r2_hidden(sK0(X1,X2),k1_relat_1(X1))
      | k1_setfam_1(k2_tarski(k1_relat_1(X2),X0)) != k1_relat_1(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f35,f30])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
      | ~ r2_hidden(X4,sK3)
      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = X1
      | k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2))
      | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = X1
      | k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2))
      | k1_setfam_1(k2_tarski(k1_relat_1(X2),X0)) != k1_relat_1(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f36,f30])).

fof(f45,plain,
    ( r2_hidden(sK4,sK3)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,
    ( k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_139,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_459,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_139])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK3,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_141,negated_conjecture,
    ( r1_tarski(sK3,k1_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_457,plain,
    ( r1_tarski(sK3,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_141])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_150,plain,
    ( ~ r1_tarski(X0_43,k1_relat_1(X0_42))
    | ~ v1_relat_1(X0_42)
    | k1_relat_1(k7_relat_1(X0_42,X0_43)) = X0_43 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_449,plain,
    ( k1_relat_1(k7_relat_1(X0_42,X0_43)) = X0_43
    | r1_tarski(X0_43,k1_relat_1(X0_42)) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_150])).

cnf(c_880,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK3)) = sK3
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_457,c_449])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1025,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_880,c_18])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_140,negated_conjecture,
    ( r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_458,plain,
    ( r1_tarski(sK3,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_881,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK3)) = sK3
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_458,c_449])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_189,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(sK1,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_1105,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_881,c_15,c_11,c_189])).

cnf(c_136,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_462,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_136])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_151,plain,
    ( ~ v1_relat_1(X0_42)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0_42),X0_43)) = k1_relat_1(k7_relat_1(X0_42,X0_43)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_448,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(X0_42),X0_43)) = k1_relat_1(k7_relat_1(X0_42,X0_43))
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_151])).

cnf(c_776,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0_43)) = k1_relat_1(k7_relat_1(sK1,X0_43)) ),
    inference(superposition,[status(thm)],[c_462,c_448])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X2) = X0
    | k1_setfam_1(k2_tarski(k1_relat_1(X1),X2)) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_146,plain,
    ( r2_hidden(sK0(X0_42,X1_42),k1_relat_1(X0_42))
    | ~ v1_funct_1(X0_42)
    | ~ v1_funct_1(X1_42)
    | ~ v1_relat_1(X0_42)
    | ~ v1_relat_1(X1_42)
    | k1_setfam_1(k2_tarski(k1_relat_1(X1_42),X0_43)) != k1_relat_1(X0_42)
    | k7_relat_1(X1_42,X0_43) = X0_42 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_453,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(X0_42),X0_43)) != k1_relat_1(X1_42)
    | k7_relat_1(X0_42,X0_43) = X1_42
    | r2_hidden(sK0(X1_42,X0_42),k1_relat_1(X1_42)) = iProver_top
    | v1_funct_1(X1_42) != iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_146])).

cnf(c_1490,plain,
    ( k1_relat_1(k7_relat_1(sK1,X0_43)) != k1_relat_1(X0_42)
    | k7_relat_1(sK1,X0_43) = X0_42
    | r2_hidden(sK0(X0_42,sK1),k1_relat_1(X0_42)) = iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_776,c_453])).

cnf(c_16,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3896,plain,
    ( v1_relat_1(X0_42) != iProver_top
    | k1_relat_1(k7_relat_1(sK1,X0_43)) != k1_relat_1(X0_42)
    | k7_relat_1(sK1,X0_43) = X0_42
    | r2_hidden(sK0(X0_42,sK1),k1_relat_1(X0_42)) = iProver_top
    | v1_funct_1(X0_42) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1490,c_16,c_17])).

cnf(c_3897,plain,
    ( k1_relat_1(k7_relat_1(sK1,X0_43)) != k1_relat_1(X0_42)
    | k7_relat_1(sK1,X0_43) = X0_42
    | r2_hidden(sK0(X0_42,sK1),k1_relat_1(X0_42)) = iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(renaming,[status(thm)],[c_3896])).

cnf(c_3905,plain,
    ( k1_relat_1(X0_42) != sK3
    | k7_relat_1(sK1,sK3) = X0_42
    | r2_hidden(sK0(X0_42,sK1),k1_relat_1(X0_42)) = iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_3897])).

cnf(c_4802,plain,
    ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),k1_relat_1(k7_relat_1(sK2,sK3))) = iProver_top
    | v1_funct_1(k7_relat_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_3905])).

cnf(c_4844,plain,
    ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),sK3) = iProver_top
    | v1_funct_1(k7_relat_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4802,c_1025])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_149,plain,
    ( ~ v1_funct_1(X0_42)
    | v1_funct_1(k7_relat_1(X0_42,X0_43))
    | ~ v1_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_192,plain,
    ( v1_funct_1(k7_relat_1(sK1,sK3))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_148,plain,
    ( ~ v1_funct_1(X0_42)
    | ~ v1_relat_1(X0_42)
    | v1_relat_1(k7_relat_1(X0_42,X0_43)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_195,plain,
    ( ~ v1_funct_1(sK1)
    | v1_relat_1(k7_relat_1(sK1,sK3))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_138,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_460,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_138])).

cnf(c_775,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0_43)) = k1_relat_1(k7_relat_1(sK2,X0_43)) ),
    inference(superposition,[status(thm)],[c_460,c_448])).

cnf(c_1489,plain,
    ( k1_relat_1(k7_relat_1(sK2,X0_43)) != k1_relat_1(X0_42)
    | k7_relat_1(sK2,X0_43) = X0_42
    | r2_hidden(sK0(X0_42,sK2),k1_relat_1(X0_42)) = iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_775,c_453])).

cnf(c_19,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2049,plain,
    ( v1_relat_1(X0_42) != iProver_top
    | k1_relat_1(k7_relat_1(sK2,X0_43)) != k1_relat_1(X0_42)
    | k7_relat_1(sK2,X0_43) = X0_42
    | r2_hidden(sK0(X0_42,sK2),k1_relat_1(X0_42)) = iProver_top
    | v1_funct_1(X0_42) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1489,c_18,c_19])).

cnf(c_2050,plain,
    ( k1_relat_1(k7_relat_1(sK2,X0_43)) != k1_relat_1(X0_42)
    | k7_relat_1(sK2,X0_43) = X0_42
    | r2_hidden(sK0(X0_42,sK2),k1_relat_1(X0_42)) = iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(renaming,[status(thm)],[c_2049])).

cnf(c_2060,plain,
    ( k1_relat_1(X0_42) != sK3
    | k7_relat_1(sK2,sK3) = X0_42
    | r2_hidden(sK0(X0_42,sK2),k1_relat_1(X0_42)) = iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_2050])).

cnf(c_2124,plain,
    ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | r2_hidden(sK0(k7_relat_1(sK1,sK3),sK2),k1_relat_1(k7_relat_1(sK1,sK3))) = iProver_top
    | v1_funct_1(k7_relat_1(sK1,sK3)) != iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_2060])).

cnf(c_2154,plain,
    ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | r2_hidden(sK0(k7_relat_1(sK1,sK3),sK2),sK3) = iProver_top
    | v1_funct_1(k7_relat_1(sK1,sK3)) != iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2124,c_1105])).

cnf(c_191,plain,
    ( v1_funct_1(X0_42) != iProver_top
    | v1_funct_1(k7_relat_1(X0_42,X0_43)) = iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_149])).

cnf(c_193,plain,
    ( v1_funct_1(k7_relat_1(sK1,sK3)) = iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_191])).

cnf(c_194,plain,
    ( v1_funct_1(X0_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(k7_relat_1(X0_42,X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_148])).

cnf(c_196,plain,
    ( v1_funct_1(sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK3)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_2303,plain,
    ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | r2_hidden(sK0(k7_relat_1(sK1,sK3),sK2),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2154,c_16,c_17,c_193,c_196])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_142,negated_conjecture,
    ( ~ r2_hidden(X0_44,sK3)
    | k1_funct_1(sK1,X0_44) = k1_funct_1(sK2,X0_44)
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_456,plain,
    ( k1_funct_1(sK1,X0_44) = k1_funct_1(sK2,X0_44)
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)
    | r2_hidden(X0_44,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_142])).

cnf(c_2309,plain,
    ( k1_funct_1(sK2,sK0(k7_relat_1(sK1,sK3),sK2)) = k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2))
    | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_2303,c_456])).

cnf(c_137,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_461,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_137])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_145,plain,
    ( ~ r2_hidden(X0_44,X0_43)
    | ~ v1_funct_1(X0_42)
    | ~ v1_relat_1(X0_42)
    | k1_funct_1(k7_relat_1(X0_42,X0_43),X0_44) = k1_funct_1(X0_42,X0_44) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_454,plain,
    ( k1_funct_1(k7_relat_1(X0_42,X0_43),X0_44) = k1_funct_1(X0_42,X0_44)
    | r2_hidden(X0_44,X0_43) != iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_145])).

cnf(c_2310,plain,
    ( k1_funct_1(k7_relat_1(X0_42,sK3),sK0(k7_relat_1(sK1,sK3),sK2)) = k1_funct_1(X0_42,sK0(k7_relat_1(sK1,sK3),sK2))
    | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | v1_funct_1(X0_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_2303,c_454])).

cnf(c_4137,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),sK0(k7_relat_1(sK1,sK3),sK2)) = k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2))
    | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_461,c_2310])).

cnf(c_2324,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),sK0(k7_relat_1(sK1,sK3),sK2)) = k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2))
    | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2310])).

cnf(c_4302,plain,
    ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | k1_funct_1(k7_relat_1(sK1,sK3),sK0(k7_relat_1(sK1,sK3),sK2)) = k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4137,c_16,c_17,c_2324])).

cnf(c_4303,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),sK0(k7_relat_1(sK1,sK3),sK2)) = k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2))
    | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3) ),
    inference(renaming,[status(thm)],[c_4302])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
    | k7_relat_1(X1,X2) = X0
    | k1_setfam_1(k2_tarski(k1_relat_1(X1),X2)) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_147,plain,
    ( ~ v1_funct_1(X0_42)
    | ~ v1_funct_1(X1_42)
    | ~ v1_relat_1(X0_42)
    | ~ v1_relat_1(X1_42)
    | k1_funct_1(X1_42,sK0(X0_42,X1_42)) != k1_funct_1(X0_42,sK0(X0_42,X1_42))
    | k1_setfam_1(k2_tarski(k1_relat_1(X1_42),X0_43)) != k1_relat_1(X0_42)
    | k7_relat_1(X1_42,X0_43) = X0_42 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_452,plain,
    ( k1_funct_1(X0_42,sK0(X1_42,X0_42)) != k1_funct_1(X1_42,sK0(X1_42,X0_42))
    | k1_setfam_1(k2_tarski(k1_relat_1(X0_42),X0_43)) != k1_relat_1(X1_42)
    | k7_relat_1(X0_42,X0_43) = X1_42
    | v1_funct_1(X1_42) != iProver_top
    | v1_funct_1(X0_42) != iProver_top
    | v1_relat_1(X1_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_147])).

cnf(c_4306,plain,
    ( k1_funct_1(sK2,sK0(k7_relat_1(sK1,sK3),sK2)) != k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2))
    | k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0_43)) != k1_relat_1(k7_relat_1(sK1,sK3))
    | k7_relat_1(sK2,X0_43) = k7_relat_1(sK1,sK3)
    | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | v1_funct_1(k7_relat_1(sK1,sK3)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK3)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4303,c_452])).

cnf(c_4307,plain,
    ( k1_funct_1(sK2,sK0(k7_relat_1(sK1,sK3),sK2)) != k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2))
    | k1_relat_1(k7_relat_1(sK2,X0_43)) != sK3
    | k7_relat_1(sK2,X0_43) = k7_relat_1(sK1,sK3)
    | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
    | v1_funct_1(k7_relat_1(sK1,sK3)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK3)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4306,c_775,c_1105])).

cnf(c_4308,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k7_relat_1(sK1,sK3))
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0(k7_relat_1(sK1,sK3),sK2)) != k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2))
    | k1_relat_1(k7_relat_1(sK2,X0_43)) != sK3
    | k7_relat_1(sK2,X0_43) = k7_relat_1(sK1,sK3)
    | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4307])).

cnf(c_4310,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k7_relat_1(sK1,sK3))
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0(k7_relat_1(sK1,sK3),sK2)) != k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2))
    | k1_relat_1(k7_relat_1(sK2,sK3)) != sK3
    | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_4308])).

cnf(c_4995,plain,
    ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4844,c_15,c_14,c_13,c_18,c_12,c_192,c_195,c_880,c_2309,c_4310])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(sK4,sK3)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_143,negated_conjecture,
    ( r2_hidden(sK4,sK3)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_455,plain,
    ( k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3)
    | r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_143])).

cnf(c_5008,plain,
    ( k7_relat_1(sK1,sK3) != k7_relat_1(sK1,sK3)
    | r2_hidden(sK4,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4995,c_455])).

cnf(c_5013,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5008])).

cnf(c_5249,plain,
    ( k1_funct_1(k7_relat_1(X0_42,sK3),sK4) = k1_funct_1(X0_42,sK4)
    | v1_funct_1(X0_42) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_5013,c_454])).

cnf(c_5573,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK3),sK4) = k1_funct_1(sK2,sK4)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_459,c_5249])).

cnf(c_5595,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) = k1_funct_1(sK2,sK4)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5573,c_4995])).

cnf(c_5796,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) = k1_funct_1(sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5595,c_18])).

cnf(c_5574,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) = k1_funct_1(sK1,sK4)
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_461,c_5249])).

cnf(c_164,plain,
    ( X0_43 != X1_43
    | X0_42 != X1_42
    | k7_relat_1(X0_42,X0_43) = k7_relat_1(X1_42,X1_43) ),
    theory(equality)).

cnf(c_173,plain,
    ( sK3 != sK3
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK1,sK3)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_153,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_180,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_154,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_181,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_154])).

cnf(c_204,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(k7_relat_1(sK1,sK3),sK4) = k1_funct_1(sK1,sK4) ),
    inference(instantiation,[status(thm)],[c_145])).

cnf(c_158,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_631,plain,
    ( k7_relat_1(sK2,sK3) != X0_42
    | k7_relat_1(sK1,sK3) != X0_42
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_672,plain,
    ( k7_relat_1(sK2,sK3) != k7_relat_1(sK1,sK3)
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_5605,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) = k1_funct_1(sK1,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5574,c_15,c_14,c_13,c_18,c_12,c_173,c_180,c_181,c_192,c_195,c_204,c_143,c_672,c_880,c_2309,c_4310])).

cnf(c_5798,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK1,sK4) ),
    inference(light_normalisation,[status(thm)],[c_5796,c_5605])).

cnf(c_7,negated_conjecture,
    ( k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_144,negated_conjecture,
    ( k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_5009,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK1,sK3) ),
    inference(demodulation,[status(thm)],[c_4995,c_144])).

cnf(c_5010,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_5009])).

cnf(c_5800,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5798,c_5010])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.93/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.03  
% 3.93/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.93/1.03  
% 3.93/1.03  ------  iProver source info
% 3.93/1.03  
% 3.93/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.93/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.93/1.03  git: non_committed_changes: false
% 3.93/1.03  git: last_make_outside_of_git: false
% 3.93/1.03  
% 3.93/1.03  ------ 
% 3.93/1.03  ------ Parsing...
% 3.93/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.93/1.03  
% 3.93/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.93/1.03  
% 3.93/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.93/1.03  
% 3.93/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.93/1.03  ------ Proving...
% 3.93/1.03  ------ Problem Properties 
% 3.93/1.03  
% 3.93/1.03  
% 3.93/1.03  clauses                                 16
% 3.93/1.03  conjectures                             9
% 3.93/1.03  EPR                                     4
% 3.93/1.03  Horn                                    14
% 3.93/1.03  unary                                   6
% 3.93/1.03  binary                                  3
% 3.93/1.03  lits                                    42
% 3.93/1.03  lits eq                                 13
% 3.93/1.03  fd_pure                                 0
% 3.93/1.03  fd_pseudo                               0
% 3.93/1.03  fd_cond                                 0
% 3.93/1.03  fd_pseudo_cond                          2
% 3.93/1.03  AC symbols                              0
% 3.93/1.03  
% 3.93/1.03  ------ Input Options Time Limit: Unbounded
% 3.93/1.03  
% 3.93/1.03  
% 3.93/1.03  ------ 
% 3.93/1.03  Current options:
% 3.93/1.03  ------ 
% 3.93/1.03  
% 3.93/1.03  
% 3.93/1.03  
% 3.93/1.03  
% 3.93/1.03  ------ Proving...
% 3.93/1.03  
% 3.93/1.03  
% 3.93/1.03  % SZS status Theorem for theBenchmark.p
% 3.93/1.03  
% 3.93/1.03   Resolution empty clause
% 3.93/1.03  
% 3.93/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.93/1.03  
% 3.93/1.03  fof(f7,conjecture,(
% 3.93/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 3.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.03  
% 3.93/1.03  fof(f8,negated_conjecture,(
% 3.93/1.03    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 3.93/1.03    inference(negated_conjecture,[],[f7])).
% 3.93/1.03  
% 3.93/1.03  fof(f18,plain,(
% 3.93/1.03    ? [X0] : (? [X1] : (? [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <~> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) & (r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.93/1.03    inference(ennf_transformation,[],[f8])).
% 3.93/1.03  
% 3.93/1.03  fof(f19,plain,(
% 3.93/1.03    ? [X0] : (? [X1] : (? [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <~> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.93/1.03    inference(flattening,[],[f18])).
% 3.93/1.03  
% 3.93/1.03  fof(f22,plain,(
% 3.93/1.03    ? [X0] : (? [X1] : (? [X2] : (((? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2)) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2))) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.93/1.03    inference(nnf_transformation,[],[f19])).
% 3.93/1.03  
% 3.93/1.03  fof(f23,plain,(
% 3.93/1.03    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2)) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.93/1.03    inference(flattening,[],[f22])).
% 3.93/1.03  
% 3.93/1.03  fof(f24,plain,(
% 3.93/1.03    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2)) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.93/1.03    inference(rectify,[],[f23])).
% 3.93/1.03  
% 3.93/1.03  fof(f28,plain,(
% 3.93/1.03    ( ! [X2,X0,X1] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK4) != k1_funct_1(X1,sK4) & r2_hidden(sK4,X2))) )),
% 3.93/1.03    introduced(choice_axiom,[])).
% 3.93/1.03  
% 3.93/1.03  fof(f27,plain,(
% 3.93/1.03    ( ! [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2)) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => ((? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,sK3)) | k7_relat_1(X0,sK3) != k7_relat_1(X1,sK3)) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,sK3)) | k7_relat_1(X0,sK3) = k7_relat_1(X1,sK3)) & r1_tarski(sK3,k1_relat_1(X1)) & r1_tarski(sK3,k1_relat_1(X0)))) )),
% 3.93/1.03    introduced(choice_axiom,[])).
% 3.93/1.03  
% 3.93/1.03  fof(f26,plain,(
% 3.93/1.03    ( ! [X0] : (? [X1] : (? [X2] : ((? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2)) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((? [X3] : (k1_funct_1(sK2,X3) != k1_funct_1(X0,X3) & r2_hidden(X3,X2)) | k7_relat_1(sK2,X2) != k7_relat_1(X0,X2)) & (! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(X0,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(sK2,X2) = k7_relat_1(X0,X2)) & r1_tarski(X2,k1_relat_1(sK2)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(sK2) & v1_relat_1(sK2))) )),
% 3.93/1.03    introduced(choice_axiom,[])).
% 3.93/1.03  
% 3.93/1.03  fof(f25,plain,(
% 3.93/1.03    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2)) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((? [X3] : (k1_funct_1(sK1,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) | k7_relat_1(sK1,X2) != k7_relat_1(X1,X2)) & (! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(sK1,X2) = k7_relat_1(X1,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK1))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 3.93/1.03    introduced(choice_axiom,[])).
% 3.93/1.03  
% 3.93/1.03  fof(f29,plain,(
% 3.93/1.03    ((((k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4) & r2_hidden(sK4,sK3)) | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3)) & (! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK3)) | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)) & r1_tarski(sK3,k1_relat_1(sK2)) & r1_tarski(sK3,k1_relat_1(sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 3.93/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f28,f27,f26,f25])).
% 3.93/1.03  
% 3.93/1.03  fof(f41,plain,(
% 3.93/1.03    v1_funct_1(sK2)),
% 3.93/1.03    inference(cnf_transformation,[],[f29])).
% 3.93/1.03  
% 3.93/1.03  fof(f43,plain,(
% 3.93/1.03    r1_tarski(sK3,k1_relat_1(sK2))),
% 3.93/1.03    inference(cnf_transformation,[],[f29])).
% 3.93/1.03  
% 3.93/1.03  fof(f3,axiom,(
% 3.93/1.03    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.03  
% 3.93/1.03  fof(f10,plain,(
% 3.93/1.03    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.93/1.03    inference(ennf_transformation,[],[f3])).
% 3.93/1.03  
% 3.93/1.03  fof(f11,plain,(
% 3.93/1.03    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.93/1.03    inference(flattening,[],[f10])).
% 3.93/1.03  
% 3.93/1.03  fof(f32,plain,(
% 3.93/1.03    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.93/1.03    inference(cnf_transformation,[],[f11])).
% 3.93/1.03  
% 3.93/1.03  fof(f40,plain,(
% 3.93/1.03    v1_relat_1(sK2)),
% 3.93/1.03    inference(cnf_transformation,[],[f29])).
% 3.93/1.03  
% 3.93/1.03  fof(f42,plain,(
% 3.93/1.03    r1_tarski(sK3,k1_relat_1(sK1))),
% 3.93/1.03    inference(cnf_transformation,[],[f29])).
% 3.93/1.03  
% 3.93/1.03  fof(f38,plain,(
% 3.93/1.03    v1_relat_1(sK1)),
% 3.93/1.03    inference(cnf_transformation,[],[f29])).
% 3.93/1.03  
% 3.93/1.03  fof(f2,axiom,(
% 3.93/1.03    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 3.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.03  
% 3.93/1.03  fof(f9,plain,(
% 3.93/1.03    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.93/1.03    inference(ennf_transformation,[],[f2])).
% 3.93/1.03  
% 3.93/1.03  fof(f31,plain,(
% 3.93/1.03    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.93/1.03    inference(cnf_transformation,[],[f9])).
% 3.93/1.03  
% 3.93/1.03  fof(f1,axiom,(
% 3.93/1.03    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.03  
% 3.93/1.03  fof(f30,plain,(
% 3.93/1.03    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.93/1.03    inference(cnf_transformation,[],[f1])).
% 3.93/1.03  
% 3.93/1.03  fof(f47,plain,(
% 3.93/1.03    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.93/1.03    inference(definition_unfolding,[],[f31,f30])).
% 3.93/1.03  
% 3.93/1.03  fof(f5,axiom,(
% 3.93/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)) & k3_xboole_0(k1_relat_1(X2),X0) = k1_relat_1(X1)) => k7_relat_1(X2,X0) = X1)))),
% 3.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.03  
% 3.93/1.03  fof(f14,plain,(
% 3.93/1.03    ! [X0,X1] : (! [X2] : ((k7_relat_1(X2,X0) = X1 | (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.93/1.03    inference(ennf_transformation,[],[f5])).
% 3.93/1.03  
% 3.93/1.03  fof(f15,plain,(
% 3.93/1.03    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | ? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.93/1.03    inference(flattening,[],[f14])).
% 3.93/1.03  
% 3.93/1.03  fof(f20,plain,(
% 3.93/1.03    ! [X2,X1] : (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2)) & r2_hidden(sK0(X1,X2),k1_relat_1(X1))))),
% 3.93/1.03    introduced(choice_axiom,[])).
% 3.93/1.03  
% 3.93/1.03  fof(f21,plain,(
% 3.93/1.03    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | (k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2)) & r2_hidden(sK0(X1,X2),k1_relat_1(X1))) | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.93/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f20])).
% 3.93/1.03  
% 3.93/1.03  fof(f35,plain,(
% 3.93/1.03    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = X1 | r2_hidden(sK0(X1,X2),k1_relat_1(X1)) | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.93/1.03    inference(cnf_transformation,[],[f21])).
% 3.93/1.03  
% 3.93/1.03  fof(f49,plain,(
% 3.93/1.03    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = X1 | r2_hidden(sK0(X1,X2),k1_relat_1(X1)) | k1_setfam_1(k2_tarski(k1_relat_1(X2),X0)) != k1_relat_1(X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.93/1.03    inference(definition_unfolding,[],[f35,f30])).
% 3.93/1.03  
% 3.93/1.03  fof(f39,plain,(
% 3.93/1.03    v1_funct_1(sK1)),
% 3.93/1.03    inference(cnf_transformation,[],[f29])).
% 3.93/1.03  
% 3.93/1.03  fof(f4,axiom,(
% 3.93/1.03    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 3.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.03  
% 3.93/1.03  fof(f12,plain,(
% 3.93/1.03    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.93/1.03    inference(ennf_transformation,[],[f4])).
% 3.93/1.03  
% 3.93/1.03  fof(f13,plain,(
% 3.93/1.03    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.93/1.03    inference(flattening,[],[f12])).
% 3.93/1.03  
% 3.93/1.03  fof(f34,plain,(
% 3.93/1.03    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.93/1.03    inference(cnf_transformation,[],[f13])).
% 3.93/1.03  
% 3.93/1.03  fof(f33,plain,(
% 3.93/1.03    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.93/1.03    inference(cnf_transformation,[],[f13])).
% 3.93/1.03  
% 3.93/1.03  fof(f44,plain,(
% 3.93/1.03    ( ! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK3) | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)) )),
% 3.93/1.03    inference(cnf_transformation,[],[f29])).
% 3.93/1.03  
% 3.93/1.03  fof(f6,axiom,(
% 3.93/1.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 3.93/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.93/1.03  
% 3.93/1.03  fof(f16,plain,(
% 3.93/1.03    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.93/1.03    inference(ennf_transformation,[],[f6])).
% 3.93/1.03  
% 3.93/1.03  fof(f17,plain,(
% 3.93/1.03    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.93/1.03    inference(flattening,[],[f16])).
% 3.93/1.03  
% 3.93/1.03  fof(f37,plain,(
% 3.93/1.03    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.93/1.03    inference(cnf_transformation,[],[f17])).
% 3.93/1.03  
% 3.93/1.03  fof(f36,plain,(
% 3.93/1.03    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = X1 | k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2)) | k3_xboole_0(k1_relat_1(X2),X0) != k1_relat_1(X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.93/1.03    inference(cnf_transformation,[],[f21])).
% 3.93/1.03  
% 3.93/1.03  fof(f48,plain,(
% 3.93/1.03    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = X1 | k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2)) | k1_setfam_1(k2_tarski(k1_relat_1(X2),X0)) != k1_relat_1(X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.93/1.03    inference(definition_unfolding,[],[f36,f30])).
% 3.93/1.03  
% 3.93/1.03  fof(f45,plain,(
% 3.93/1.03    r2_hidden(sK4,sK3) | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3)),
% 3.93/1.03    inference(cnf_transformation,[],[f29])).
% 3.93/1.03  
% 3.93/1.03  fof(f46,plain,(
% 3.93/1.03    k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4) | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3)),
% 3.93/1.03    inference(cnf_transformation,[],[f29])).
% 3.93/1.03  
% 3.93/1.03  cnf(c_12,negated_conjecture,
% 3.93/1.03      ( v1_funct_1(sK2) ),
% 3.93/1.03      inference(cnf_transformation,[],[f41]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_139,negated_conjecture,
% 3.93/1.03      ( v1_funct_1(sK2) ),
% 3.93/1.03      inference(subtyping,[status(esa)],[c_12]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_459,plain,
% 3.93/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_139]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_10,negated_conjecture,
% 3.93/1.03      ( r1_tarski(sK3,k1_relat_1(sK2)) ),
% 3.93/1.03      inference(cnf_transformation,[],[f43]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_141,negated_conjecture,
% 3.93/1.03      ( r1_tarski(sK3,k1_relat_1(sK2)) ),
% 3.93/1.03      inference(subtyping,[status(esa)],[c_10]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_457,plain,
% 3.93/1.03      ( r1_tarski(sK3,k1_relat_1(sK2)) = iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_141]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_1,plain,
% 3.93/1.03      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.93/1.03      | ~ v1_relat_1(X1)
% 3.93/1.03      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.93/1.03      inference(cnf_transformation,[],[f32]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_150,plain,
% 3.93/1.03      ( ~ r1_tarski(X0_43,k1_relat_1(X0_42))
% 3.93/1.03      | ~ v1_relat_1(X0_42)
% 3.93/1.03      | k1_relat_1(k7_relat_1(X0_42,X0_43)) = X0_43 ),
% 3.93/1.03      inference(subtyping,[status(esa)],[c_1]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_449,plain,
% 3.93/1.03      ( k1_relat_1(k7_relat_1(X0_42,X0_43)) = X0_43
% 3.93/1.03      | r1_tarski(X0_43,k1_relat_1(X0_42)) != iProver_top
% 3.93/1.03      | v1_relat_1(X0_42) != iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_150]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_880,plain,
% 3.93/1.03      ( k1_relat_1(k7_relat_1(sK2,sK3)) = sK3
% 3.93/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_457,c_449]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_13,negated_conjecture,
% 3.93/1.03      ( v1_relat_1(sK2) ),
% 3.93/1.03      inference(cnf_transformation,[],[f40]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_18,plain,
% 3.93/1.03      ( v1_relat_1(sK2) = iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_1025,plain,
% 3.93/1.03      ( k1_relat_1(k7_relat_1(sK2,sK3)) = sK3 ),
% 3.93/1.03      inference(global_propositional_subsumption,[status(thm)],[c_880,c_18]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_11,negated_conjecture,
% 3.93/1.03      ( r1_tarski(sK3,k1_relat_1(sK1)) ),
% 3.93/1.03      inference(cnf_transformation,[],[f42]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_140,negated_conjecture,
% 3.93/1.03      ( r1_tarski(sK3,k1_relat_1(sK1)) ),
% 3.93/1.03      inference(subtyping,[status(esa)],[c_11]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_458,plain,
% 3.93/1.03      ( r1_tarski(sK3,k1_relat_1(sK1)) = iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_140]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_881,plain,
% 3.93/1.03      ( k1_relat_1(k7_relat_1(sK1,sK3)) = sK3
% 3.93/1.03      | v1_relat_1(sK1) != iProver_top ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_458,c_449]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_15,negated_conjecture,
% 3.93/1.03      ( v1_relat_1(sK1) ),
% 3.93/1.03      inference(cnf_transformation,[],[f38]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_189,plain,
% 3.93/1.03      ( ~ r1_tarski(sK3,k1_relat_1(sK1))
% 3.93/1.03      | ~ v1_relat_1(sK1)
% 3.93/1.03      | k1_relat_1(k7_relat_1(sK1,sK3)) = sK3 ),
% 3.93/1.03      inference(instantiation,[status(thm)],[c_150]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_1105,plain,
% 3.93/1.03      ( k1_relat_1(k7_relat_1(sK1,sK3)) = sK3 ),
% 3.93/1.03      inference(global_propositional_subsumption,
% 3.93/1.03                [status(thm)],
% 3.93/1.03                [c_881,c_15,c_11,c_189]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_136,negated_conjecture,
% 3.93/1.03      ( v1_relat_1(sK1) ),
% 3.93/1.03      inference(subtyping,[status(esa)],[c_15]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_462,plain,
% 3.93/1.03      ( v1_relat_1(sK1) = iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_136]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_0,plain,
% 3.93/1.03      ( ~ v1_relat_1(X0)
% 3.93/1.03      | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 3.93/1.03      inference(cnf_transformation,[],[f47]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_151,plain,
% 3.93/1.03      ( ~ v1_relat_1(X0_42)
% 3.93/1.03      | k1_setfam_1(k2_tarski(k1_relat_1(X0_42),X0_43)) = k1_relat_1(k7_relat_1(X0_42,X0_43)) ),
% 3.93/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_448,plain,
% 3.93/1.03      ( k1_setfam_1(k2_tarski(k1_relat_1(X0_42),X0_43)) = k1_relat_1(k7_relat_1(X0_42,X0_43))
% 3.93/1.03      | v1_relat_1(X0_42) != iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_151]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_776,plain,
% 3.93/1.03      ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0_43)) = k1_relat_1(k7_relat_1(sK1,X0_43)) ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_462,c_448]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_5,plain,
% 3.93/1.03      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 3.93/1.03      | ~ v1_funct_1(X0)
% 3.93/1.03      | ~ v1_funct_1(X1)
% 3.93/1.03      | ~ v1_relat_1(X0)
% 3.93/1.03      | ~ v1_relat_1(X1)
% 3.93/1.03      | k7_relat_1(X1,X2) = X0
% 3.93/1.03      | k1_setfam_1(k2_tarski(k1_relat_1(X1),X2)) != k1_relat_1(X0) ),
% 3.93/1.03      inference(cnf_transformation,[],[f49]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_146,plain,
% 3.93/1.03      ( r2_hidden(sK0(X0_42,X1_42),k1_relat_1(X0_42))
% 3.93/1.03      | ~ v1_funct_1(X0_42)
% 3.93/1.03      | ~ v1_funct_1(X1_42)
% 3.93/1.03      | ~ v1_relat_1(X0_42)
% 3.93/1.03      | ~ v1_relat_1(X1_42)
% 3.93/1.03      | k1_setfam_1(k2_tarski(k1_relat_1(X1_42),X0_43)) != k1_relat_1(X0_42)
% 3.93/1.03      | k7_relat_1(X1_42,X0_43) = X0_42 ),
% 3.93/1.03      inference(subtyping,[status(esa)],[c_5]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_453,plain,
% 3.93/1.03      ( k1_setfam_1(k2_tarski(k1_relat_1(X0_42),X0_43)) != k1_relat_1(X1_42)
% 3.93/1.03      | k7_relat_1(X0_42,X0_43) = X1_42
% 3.93/1.03      | r2_hidden(sK0(X1_42,X0_42),k1_relat_1(X1_42)) = iProver_top
% 3.93/1.03      | v1_funct_1(X1_42) != iProver_top
% 3.93/1.03      | v1_funct_1(X0_42) != iProver_top
% 3.93/1.03      | v1_relat_1(X1_42) != iProver_top
% 3.93/1.03      | v1_relat_1(X0_42) != iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_146]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_1490,plain,
% 3.93/1.03      ( k1_relat_1(k7_relat_1(sK1,X0_43)) != k1_relat_1(X0_42)
% 3.93/1.03      | k7_relat_1(sK1,X0_43) = X0_42
% 3.93/1.03      | r2_hidden(sK0(X0_42,sK1),k1_relat_1(X0_42)) = iProver_top
% 3.93/1.03      | v1_funct_1(X0_42) != iProver_top
% 3.93/1.03      | v1_funct_1(sK1) != iProver_top
% 3.93/1.03      | v1_relat_1(X0_42) != iProver_top
% 3.93/1.03      | v1_relat_1(sK1) != iProver_top ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_776,c_453]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_16,plain,
% 3.93/1.03      ( v1_relat_1(sK1) = iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_14,negated_conjecture,
% 3.93/1.03      ( v1_funct_1(sK1) ),
% 3.93/1.03      inference(cnf_transformation,[],[f39]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_17,plain,
% 3.93/1.03      ( v1_funct_1(sK1) = iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_3896,plain,
% 3.93/1.03      ( v1_relat_1(X0_42) != iProver_top
% 3.93/1.03      | k1_relat_1(k7_relat_1(sK1,X0_43)) != k1_relat_1(X0_42)
% 3.93/1.03      | k7_relat_1(sK1,X0_43) = X0_42
% 3.93/1.03      | r2_hidden(sK0(X0_42,sK1),k1_relat_1(X0_42)) = iProver_top
% 3.93/1.03      | v1_funct_1(X0_42) != iProver_top ),
% 3.93/1.03      inference(global_propositional_subsumption,
% 3.93/1.03                [status(thm)],
% 3.93/1.03                [c_1490,c_16,c_17]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_3897,plain,
% 3.93/1.03      ( k1_relat_1(k7_relat_1(sK1,X0_43)) != k1_relat_1(X0_42)
% 3.93/1.03      | k7_relat_1(sK1,X0_43) = X0_42
% 3.93/1.03      | r2_hidden(sK0(X0_42,sK1),k1_relat_1(X0_42)) = iProver_top
% 3.93/1.03      | v1_funct_1(X0_42) != iProver_top
% 3.93/1.03      | v1_relat_1(X0_42) != iProver_top ),
% 3.93/1.03      inference(renaming,[status(thm)],[c_3896]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_3905,plain,
% 3.93/1.03      ( k1_relat_1(X0_42) != sK3
% 3.93/1.03      | k7_relat_1(sK1,sK3) = X0_42
% 3.93/1.03      | r2_hidden(sK0(X0_42,sK1),k1_relat_1(X0_42)) = iProver_top
% 3.93/1.03      | v1_funct_1(X0_42) != iProver_top
% 3.93/1.03      | v1_relat_1(X0_42) != iProver_top ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_1105,c_3897]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_4802,plain,
% 3.93/1.03      ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 3.93/1.03      | r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),k1_relat_1(k7_relat_1(sK2,sK3))) = iProver_top
% 3.93/1.03      | v1_funct_1(k7_relat_1(sK2,sK3)) != iProver_top
% 3.93/1.03      | v1_relat_1(k7_relat_1(sK2,sK3)) != iProver_top ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_1025,c_3905]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_4844,plain,
% 3.93/1.03      ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 3.93/1.03      | r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),sK3) = iProver_top
% 3.93/1.03      | v1_funct_1(k7_relat_1(sK2,sK3)) != iProver_top
% 3.93/1.03      | v1_relat_1(k7_relat_1(sK2,sK3)) != iProver_top ),
% 3.93/1.03      inference(light_normalisation,[status(thm)],[c_4802,c_1025]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_2,plain,
% 3.93/1.03      ( ~ v1_funct_1(X0) | v1_funct_1(k7_relat_1(X0,X1)) | ~ v1_relat_1(X0) ),
% 3.93/1.03      inference(cnf_transformation,[],[f34]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_149,plain,
% 3.93/1.03      ( ~ v1_funct_1(X0_42)
% 3.93/1.03      | v1_funct_1(k7_relat_1(X0_42,X0_43))
% 3.93/1.03      | ~ v1_relat_1(X0_42) ),
% 3.93/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_192,plain,
% 3.93/1.03      ( v1_funct_1(k7_relat_1(sK1,sK3))
% 3.93/1.03      | ~ v1_funct_1(sK1)
% 3.93/1.03      | ~ v1_relat_1(sK1) ),
% 3.93/1.03      inference(instantiation,[status(thm)],[c_149]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_3,plain,
% 3.93/1.03      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.93/1.03      inference(cnf_transformation,[],[f33]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_148,plain,
% 3.93/1.03      ( ~ v1_funct_1(X0_42)
% 3.93/1.03      | ~ v1_relat_1(X0_42)
% 3.93/1.03      | v1_relat_1(k7_relat_1(X0_42,X0_43)) ),
% 3.93/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_195,plain,
% 3.93/1.03      ( ~ v1_funct_1(sK1)
% 3.93/1.03      | v1_relat_1(k7_relat_1(sK1,sK3))
% 3.93/1.03      | ~ v1_relat_1(sK1) ),
% 3.93/1.03      inference(instantiation,[status(thm)],[c_148]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_138,negated_conjecture,
% 3.93/1.03      ( v1_relat_1(sK2) ),
% 3.93/1.03      inference(subtyping,[status(esa)],[c_13]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_460,plain,
% 3.93/1.03      ( v1_relat_1(sK2) = iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_138]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_775,plain,
% 3.93/1.03      ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0_43)) = k1_relat_1(k7_relat_1(sK2,X0_43)) ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_460,c_448]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_1489,plain,
% 3.93/1.03      ( k1_relat_1(k7_relat_1(sK2,X0_43)) != k1_relat_1(X0_42)
% 3.93/1.03      | k7_relat_1(sK2,X0_43) = X0_42
% 3.93/1.03      | r2_hidden(sK0(X0_42,sK2),k1_relat_1(X0_42)) = iProver_top
% 3.93/1.03      | v1_funct_1(X0_42) != iProver_top
% 3.93/1.03      | v1_funct_1(sK2) != iProver_top
% 3.93/1.03      | v1_relat_1(X0_42) != iProver_top
% 3.93/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_775,c_453]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_19,plain,
% 3.93/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_2049,plain,
% 3.93/1.03      ( v1_relat_1(X0_42) != iProver_top
% 3.93/1.03      | k1_relat_1(k7_relat_1(sK2,X0_43)) != k1_relat_1(X0_42)
% 3.93/1.03      | k7_relat_1(sK2,X0_43) = X0_42
% 3.93/1.03      | r2_hidden(sK0(X0_42,sK2),k1_relat_1(X0_42)) = iProver_top
% 3.93/1.03      | v1_funct_1(X0_42) != iProver_top ),
% 3.93/1.03      inference(global_propositional_subsumption,
% 3.93/1.03                [status(thm)],
% 3.93/1.03                [c_1489,c_18,c_19]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_2050,plain,
% 3.93/1.03      ( k1_relat_1(k7_relat_1(sK2,X0_43)) != k1_relat_1(X0_42)
% 3.93/1.03      | k7_relat_1(sK2,X0_43) = X0_42
% 3.93/1.03      | r2_hidden(sK0(X0_42,sK2),k1_relat_1(X0_42)) = iProver_top
% 3.93/1.03      | v1_funct_1(X0_42) != iProver_top
% 3.93/1.03      | v1_relat_1(X0_42) != iProver_top ),
% 3.93/1.03      inference(renaming,[status(thm)],[c_2049]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_2060,plain,
% 3.93/1.03      ( k1_relat_1(X0_42) != sK3
% 3.93/1.03      | k7_relat_1(sK2,sK3) = X0_42
% 3.93/1.03      | r2_hidden(sK0(X0_42,sK2),k1_relat_1(X0_42)) = iProver_top
% 3.93/1.03      | v1_funct_1(X0_42) != iProver_top
% 3.93/1.03      | v1_relat_1(X0_42) != iProver_top ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_1025,c_2050]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_2124,plain,
% 3.93/1.03      ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 3.93/1.03      | r2_hidden(sK0(k7_relat_1(sK1,sK3),sK2),k1_relat_1(k7_relat_1(sK1,sK3))) = iProver_top
% 3.93/1.03      | v1_funct_1(k7_relat_1(sK1,sK3)) != iProver_top
% 3.93/1.03      | v1_relat_1(k7_relat_1(sK1,sK3)) != iProver_top ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_1105,c_2060]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_2154,plain,
% 3.93/1.03      ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 3.93/1.03      | r2_hidden(sK0(k7_relat_1(sK1,sK3),sK2),sK3) = iProver_top
% 3.93/1.03      | v1_funct_1(k7_relat_1(sK1,sK3)) != iProver_top
% 3.93/1.03      | v1_relat_1(k7_relat_1(sK1,sK3)) != iProver_top ),
% 3.93/1.03      inference(light_normalisation,[status(thm)],[c_2124,c_1105]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_191,plain,
% 3.93/1.03      ( v1_funct_1(X0_42) != iProver_top
% 3.93/1.03      | v1_funct_1(k7_relat_1(X0_42,X0_43)) = iProver_top
% 3.93/1.03      | v1_relat_1(X0_42) != iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_149]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_193,plain,
% 3.93/1.03      ( v1_funct_1(k7_relat_1(sK1,sK3)) = iProver_top
% 3.93/1.03      | v1_funct_1(sK1) != iProver_top
% 3.93/1.03      | v1_relat_1(sK1) != iProver_top ),
% 3.93/1.03      inference(instantiation,[status(thm)],[c_191]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_194,plain,
% 3.93/1.03      ( v1_funct_1(X0_42) != iProver_top
% 3.93/1.03      | v1_relat_1(X0_42) != iProver_top
% 3.93/1.03      | v1_relat_1(k7_relat_1(X0_42,X0_43)) = iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_148]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_196,plain,
% 3.93/1.03      ( v1_funct_1(sK1) != iProver_top
% 3.93/1.03      | v1_relat_1(k7_relat_1(sK1,sK3)) = iProver_top
% 3.93/1.03      | v1_relat_1(sK1) != iProver_top ),
% 3.93/1.03      inference(instantiation,[status(thm)],[c_194]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_2303,plain,
% 3.93/1.03      ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 3.93/1.03      | r2_hidden(sK0(k7_relat_1(sK1,sK3),sK2),sK3) = iProver_top ),
% 3.93/1.03      inference(global_propositional_subsumption,
% 3.93/1.03                [status(thm)],
% 3.93/1.03                [c_2154,c_16,c_17,c_193,c_196]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_9,negated_conjecture,
% 3.93/1.03      ( ~ r2_hidden(X0,sK3)
% 3.93/1.03      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
% 3.93/1.03      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
% 3.93/1.03      inference(cnf_transformation,[],[f44]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_142,negated_conjecture,
% 3.93/1.03      ( ~ r2_hidden(X0_44,sK3)
% 3.93/1.03      | k1_funct_1(sK1,X0_44) = k1_funct_1(sK2,X0_44)
% 3.93/1.03      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
% 3.93/1.03      inference(subtyping,[status(esa)],[c_9]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_456,plain,
% 3.93/1.03      ( k1_funct_1(sK1,X0_44) = k1_funct_1(sK2,X0_44)
% 3.93/1.03      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)
% 3.93/1.03      | r2_hidden(X0_44,sK3) != iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_142]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_2309,plain,
% 3.93/1.03      ( k1_funct_1(sK2,sK0(k7_relat_1(sK1,sK3),sK2)) = k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2))
% 3.93/1.03      | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3) ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_2303,c_456]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_137,negated_conjecture,
% 3.93/1.03      ( v1_funct_1(sK1) ),
% 3.93/1.03      inference(subtyping,[status(esa)],[c_14]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_461,plain,
% 3.93/1.03      ( v1_funct_1(sK1) = iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_137]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_6,plain,
% 3.93/1.03      ( ~ r2_hidden(X0,X1)
% 3.93/1.03      | ~ v1_funct_1(X2)
% 3.93/1.03      | ~ v1_relat_1(X2)
% 3.93/1.03      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
% 3.93/1.03      inference(cnf_transformation,[],[f37]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_145,plain,
% 3.93/1.03      ( ~ r2_hidden(X0_44,X0_43)
% 3.93/1.03      | ~ v1_funct_1(X0_42)
% 3.93/1.03      | ~ v1_relat_1(X0_42)
% 3.93/1.03      | k1_funct_1(k7_relat_1(X0_42,X0_43),X0_44) = k1_funct_1(X0_42,X0_44) ),
% 3.93/1.03      inference(subtyping,[status(esa)],[c_6]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_454,plain,
% 3.93/1.03      ( k1_funct_1(k7_relat_1(X0_42,X0_43),X0_44) = k1_funct_1(X0_42,X0_44)
% 3.93/1.03      | r2_hidden(X0_44,X0_43) != iProver_top
% 3.93/1.03      | v1_funct_1(X0_42) != iProver_top
% 3.93/1.03      | v1_relat_1(X0_42) != iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_145]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_2310,plain,
% 3.93/1.03      ( k1_funct_1(k7_relat_1(X0_42,sK3),sK0(k7_relat_1(sK1,sK3),sK2)) = k1_funct_1(X0_42,sK0(k7_relat_1(sK1,sK3),sK2))
% 3.93/1.03      | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 3.93/1.03      | v1_funct_1(X0_42) != iProver_top
% 3.93/1.03      | v1_relat_1(X0_42) != iProver_top ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_2303,c_454]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_4137,plain,
% 3.93/1.03      ( k1_funct_1(k7_relat_1(sK1,sK3),sK0(k7_relat_1(sK1,sK3),sK2)) = k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2))
% 3.93/1.03      | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 3.93/1.03      | v1_relat_1(sK1) != iProver_top ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_461,c_2310]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_2324,plain,
% 3.93/1.03      ( k1_funct_1(k7_relat_1(sK1,sK3),sK0(k7_relat_1(sK1,sK3),sK2)) = k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2))
% 3.93/1.03      | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 3.93/1.03      | v1_funct_1(sK1) != iProver_top
% 3.93/1.03      | v1_relat_1(sK1) != iProver_top ),
% 3.93/1.03      inference(instantiation,[status(thm)],[c_2310]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_4302,plain,
% 3.93/1.03      ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 3.93/1.03      | k1_funct_1(k7_relat_1(sK1,sK3),sK0(k7_relat_1(sK1,sK3),sK2)) = k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2)) ),
% 3.93/1.03      inference(global_propositional_subsumption,
% 3.93/1.03                [status(thm)],
% 3.93/1.03                [c_4137,c_16,c_17,c_2324]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_4303,plain,
% 3.93/1.03      ( k1_funct_1(k7_relat_1(sK1,sK3),sK0(k7_relat_1(sK1,sK3),sK2)) = k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2))
% 3.93/1.03      | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3) ),
% 3.93/1.03      inference(renaming,[status(thm)],[c_4302]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_4,plain,
% 3.93/1.03      ( ~ v1_funct_1(X0)
% 3.93/1.03      | ~ v1_funct_1(X1)
% 3.93/1.03      | ~ v1_relat_1(X0)
% 3.93/1.03      | ~ v1_relat_1(X1)
% 3.93/1.03      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
% 3.93/1.03      | k7_relat_1(X1,X2) = X0
% 3.93/1.03      | k1_setfam_1(k2_tarski(k1_relat_1(X1),X2)) != k1_relat_1(X0) ),
% 3.93/1.03      inference(cnf_transformation,[],[f48]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_147,plain,
% 3.93/1.03      ( ~ v1_funct_1(X0_42)
% 3.93/1.03      | ~ v1_funct_1(X1_42)
% 3.93/1.03      | ~ v1_relat_1(X0_42)
% 3.93/1.03      | ~ v1_relat_1(X1_42)
% 3.93/1.03      | k1_funct_1(X1_42,sK0(X0_42,X1_42)) != k1_funct_1(X0_42,sK0(X0_42,X1_42))
% 3.93/1.03      | k1_setfam_1(k2_tarski(k1_relat_1(X1_42),X0_43)) != k1_relat_1(X0_42)
% 3.93/1.03      | k7_relat_1(X1_42,X0_43) = X0_42 ),
% 3.93/1.03      inference(subtyping,[status(esa)],[c_4]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_452,plain,
% 3.93/1.03      ( k1_funct_1(X0_42,sK0(X1_42,X0_42)) != k1_funct_1(X1_42,sK0(X1_42,X0_42))
% 3.93/1.03      | k1_setfam_1(k2_tarski(k1_relat_1(X0_42),X0_43)) != k1_relat_1(X1_42)
% 3.93/1.03      | k7_relat_1(X0_42,X0_43) = X1_42
% 3.93/1.03      | v1_funct_1(X1_42) != iProver_top
% 3.93/1.03      | v1_funct_1(X0_42) != iProver_top
% 3.93/1.03      | v1_relat_1(X1_42) != iProver_top
% 3.93/1.03      | v1_relat_1(X0_42) != iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_147]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_4306,plain,
% 3.93/1.03      ( k1_funct_1(sK2,sK0(k7_relat_1(sK1,sK3),sK2)) != k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2))
% 3.93/1.03      | k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0_43)) != k1_relat_1(k7_relat_1(sK1,sK3))
% 3.93/1.03      | k7_relat_1(sK2,X0_43) = k7_relat_1(sK1,sK3)
% 3.93/1.03      | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 3.93/1.03      | v1_funct_1(k7_relat_1(sK1,sK3)) != iProver_top
% 3.93/1.03      | v1_funct_1(sK2) != iProver_top
% 3.93/1.03      | v1_relat_1(k7_relat_1(sK1,sK3)) != iProver_top
% 3.93/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_4303,c_452]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_4307,plain,
% 3.93/1.03      ( k1_funct_1(sK2,sK0(k7_relat_1(sK1,sK3),sK2)) != k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2))
% 3.93/1.03      | k1_relat_1(k7_relat_1(sK2,X0_43)) != sK3
% 3.93/1.03      | k7_relat_1(sK2,X0_43) = k7_relat_1(sK1,sK3)
% 3.93/1.03      | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3)
% 3.93/1.03      | v1_funct_1(k7_relat_1(sK1,sK3)) != iProver_top
% 3.93/1.03      | v1_funct_1(sK2) != iProver_top
% 3.93/1.03      | v1_relat_1(k7_relat_1(sK1,sK3)) != iProver_top
% 3.93/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.03      inference(light_normalisation,[status(thm)],[c_4306,c_775,c_1105]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_4308,plain,
% 3.93/1.03      ( ~ v1_funct_1(k7_relat_1(sK1,sK3))
% 3.93/1.03      | ~ v1_funct_1(sK2)
% 3.93/1.03      | ~ v1_relat_1(k7_relat_1(sK1,sK3))
% 3.93/1.03      | ~ v1_relat_1(sK2)
% 3.93/1.03      | k1_funct_1(sK2,sK0(k7_relat_1(sK1,sK3),sK2)) != k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2))
% 3.93/1.03      | k1_relat_1(k7_relat_1(sK2,X0_43)) != sK3
% 3.93/1.03      | k7_relat_1(sK2,X0_43) = k7_relat_1(sK1,sK3)
% 3.93/1.03      | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3) ),
% 3.93/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_4307]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_4310,plain,
% 3.93/1.03      ( ~ v1_funct_1(k7_relat_1(sK1,sK3))
% 3.93/1.03      | ~ v1_funct_1(sK2)
% 3.93/1.03      | ~ v1_relat_1(k7_relat_1(sK1,sK3))
% 3.93/1.03      | ~ v1_relat_1(sK2)
% 3.93/1.03      | k1_funct_1(sK2,sK0(k7_relat_1(sK1,sK3),sK2)) != k1_funct_1(sK1,sK0(k7_relat_1(sK1,sK3),sK2))
% 3.93/1.03      | k1_relat_1(k7_relat_1(sK2,sK3)) != sK3
% 3.93/1.03      | k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3) ),
% 3.93/1.03      inference(instantiation,[status(thm)],[c_4308]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_4995,plain,
% 3.93/1.03      ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3) ),
% 3.93/1.03      inference(global_propositional_subsumption,
% 3.93/1.03                [status(thm)],
% 3.93/1.03                [c_4844,c_15,c_14,c_13,c_18,c_12,c_192,c_195,c_880,c_2309,
% 3.93/1.03                 c_4310]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_8,negated_conjecture,
% 3.93/1.03      ( r2_hidden(sK4,sK3) | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
% 3.93/1.03      inference(cnf_transformation,[],[f45]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_143,negated_conjecture,
% 3.93/1.03      ( r2_hidden(sK4,sK3) | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
% 3.93/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_455,plain,
% 3.93/1.03      ( k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3)
% 3.93/1.03      | r2_hidden(sK4,sK3) = iProver_top ),
% 3.93/1.03      inference(predicate_to_equality,[status(thm)],[c_143]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_5008,plain,
% 3.93/1.03      ( k7_relat_1(sK1,sK3) != k7_relat_1(sK1,sK3)
% 3.93/1.03      | r2_hidden(sK4,sK3) = iProver_top ),
% 3.93/1.03      inference(demodulation,[status(thm)],[c_4995,c_455]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_5013,plain,
% 3.93/1.03      ( r2_hidden(sK4,sK3) = iProver_top ),
% 3.93/1.03      inference(equality_resolution_simp,[status(thm)],[c_5008]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_5249,plain,
% 3.93/1.03      ( k1_funct_1(k7_relat_1(X0_42,sK3),sK4) = k1_funct_1(X0_42,sK4)
% 3.93/1.03      | v1_funct_1(X0_42) != iProver_top
% 3.93/1.03      | v1_relat_1(X0_42) != iProver_top ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_5013,c_454]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_5573,plain,
% 3.93/1.03      ( k1_funct_1(k7_relat_1(sK2,sK3),sK4) = k1_funct_1(sK2,sK4)
% 3.93/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_459,c_5249]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_5595,plain,
% 3.93/1.03      ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) = k1_funct_1(sK2,sK4)
% 3.93/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.93/1.03      inference(light_normalisation,[status(thm)],[c_5573,c_4995]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_5796,plain,
% 3.93/1.03      ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) = k1_funct_1(sK2,sK4) ),
% 3.93/1.03      inference(global_propositional_subsumption,[status(thm)],[c_5595,c_18]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_5574,plain,
% 3.93/1.03      ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) = k1_funct_1(sK1,sK4)
% 3.93/1.03      | v1_relat_1(sK1) != iProver_top ),
% 3.93/1.03      inference(superposition,[status(thm)],[c_461,c_5249]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_164,plain,
% 3.93/1.03      ( X0_43 != X1_43
% 3.93/1.03      | X0_42 != X1_42
% 3.93/1.03      | k7_relat_1(X0_42,X0_43) = k7_relat_1(X1_42,X1_43) ),
% 3.93/1.03      theory(equality) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_173,plain,
% 3.93/1.03      ( sK3 != sK3 | k7_relat_1(sK1,sK3) = k7_relat_1(sK1,sK3) | sK1 != sK1 ),
% 3.93/1.03      inference(instantiation,[status(thm)],[c_164]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_153,plain,( X0_42 = X0_42 ),theory(equality) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_180,plain,
% 3.93/1.03      ( sK1 = sK1 ),
% 3.93/1.03      inference(instantiation,[status(thm)],[c_153]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_154,plain,( X0_43 = X0_43 ),theory(equality) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_181,plain,
% 3.93/1.03      ( sK3 = sK3 ),
% 3.93/1.03      inference(instantiation,[status(thm)],[c_154]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_204,plain,
% 3.93/1.03      ( ~ r2_hidden(sK4,sK3)
% 3.93/1.03      | ~ v1_funct_1(sK1)
% 3.93/1.03      | ~ v1_relat_1(sK1)
% 3.93/1.03      | k1_funct_1(k7_relat_1(sK1,sK3),sK4) = k1_funct_1(sK1,sK4) ),
% 3.93/1.03      inference(instantiation,[status(thm)],[c_145]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_158,plain,
% 3.93/1.03      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 3.93/1.03      theory(equality) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_631,plain,
% 3.93/1.03      ( k7_relat_1(sK2,sK3) != X0_42
% 3.93/1.03      | k7_relat_1(sK1,sK3) != X0_42
% 3.93/1.03      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
% 3.93/1.03      inference(instantiation,[status(thm)],[c_158]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_672,plain,
% 3.93/1.03      ( k7_relat_1(sK2,sK3) != k7_relat_1(sK1,sK3)
% 3.93/1.03      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)
% 3.93/1.03      | k7_relat_1(sK1,sK3) != k7_relat_1(sK1,sK3) ),
% 3.93/1.03      inference(instantiation,[status(thm)],[c_631]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_5605,plain,
% 3.93/1.03      ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) = k1_funct_1(sK1,sK4) ),
% 3.93/1.03      inference(global_propositional_subsumption,
% 3.93/1.03                [status(thm)],
% 3.93/1.03                [c_5574,c_15,c_14,c_13,c_18,c_12,c_173,c_180,c_181,c_192,
% 3.93/1.03                 c_195,c_204,c_143,c_672,c_880,c_2309,c_4310]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_5798,plain,
% 3.93/1.03      ( k1_funct_1(sK2,sK4) = k1_funct_1(sK1,sK4) ),
% 3.93/1.03      inference(light_normalisation,[status(thm)],[c_5796,c_5605]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_7,negated_conjecture,
% 3.93/1.03      ( k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4)
% 3.93/1.03      | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
% 3.93/1.03      inference(cnf_transformation,[],[f46]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_144,negated_conjecture,
% 3.93/1.03      ( k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4)
% 3.93/1.03      | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
% 3.93/1.03      inference(subtyping,[status(esa)],[c_7]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_5009,plain,
% 3.93/1.03      ( k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
% 3.93/1.03      | k7_relat_1(sK1,sK3) != k7_relat_1(sK1,sK3) ),
% 3.93/1.03      inference(demodulation,[status(thm)],[c_4995,c_144]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_5010,plain,
% 3.93/1.03      ( k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4) ),
% 3.93/1.03      inference(equality_resolution_simp,[status(thm)],[c_5009]) ).
% 3.93/1.03  
% 3.93/1.03  cnf(c_5800,plain,
% 3.93/1.03      ( $false ),
% 3.93/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_5798,c_5010]) ).
% 3.93/1.03  
% 3.93/1.03  
% 3.93/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.93/1.03  
% 3.93/1.03  ------                               Statistics
% 3.93/1.03  
% 3.93/1.03  ------ Selected
% 3.93/1.03  
% 3.93/1.03  total_time:                             0.2
% 3.93/1.03  
%------------------------------------------------------------------------------
