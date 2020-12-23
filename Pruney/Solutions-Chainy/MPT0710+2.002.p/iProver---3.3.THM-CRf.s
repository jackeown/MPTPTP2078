%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:41 EST 2020

% Result     : Theorem 11.74s
% Output     : CNFRefutation 11.74s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 633 expanded)
%              Number of clauses        :  121 ( 202 expanded)
%              Number of leaves         :   18 ( 172 expanded)
%              Depth                    :   20
%              Number of atoms          :  622 (4915 expanded)
%              Number of equality atoms :  352 (1825 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
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

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f17])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f18])).

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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK4) != k1_funct_1(X1,sK4)
        & r2_hidden(sK4,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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

fof(f25,plain,(
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

fof(f24,plain,
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

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f27,f26,f25,f24])).

fof(f42,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
      | ~ r2_hidden(X4,sK3)
      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    r1_tarski(sK3,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0) )
           => k7_relat_1(X2,X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ? [X3] :
              ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
              & r2_hidden(X3,k1_relat_1(X1)) )
          | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ? [X3] :
              ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
              & r2_hidden(X3,k1_relat_1(X1)) )
          | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f19,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2))
        & r2_hidden(sK0(X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ( k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2))
            & r2_hidden(sK0(X1,X2),k1_relat_1(X1)) )
          | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f19])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = X1
      | r2_hidden(sK0(X1,X2),k1_relat_1(X1))
      | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = X1
      | k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2))
      | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,
    ( r2_hidden(sK4,sK3)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,
    ( k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_547,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_997,plain,
    ( X0_44 != X1_44
    | k1_funct_1(sK2,sK4) != X1_44
    | k1_funct_1(sK2,sK4) = X0_44 ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_17607,plain,
    ( X0_44 != k1_funct_1(k7_relat_1(sK2,X0_42),sK4)
    | k1_funct_1(sK2,sK4) = X0_44
    | k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(sK2,X0_42),sK4) ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_22082,plain,
    ( k1_funct_1(X0_41,X0_43) != k1_funct_1(k7_relat_1(sK2,X0_42),sK4)
    | k1_funct_1(sK2,sK4) = k1_funct_1(X0_41,X0_43)
    | k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(sK2,X0_42),sK4) ),
    inference(instantiation,[status(thm)],[c_17607])).

cnf(c_45017,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),X0_43) != k1_funct_1(k7_relat_1(sK2,sK3),sK4)
    | k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(sK2,sK3),sK4)
    | k1_funct_1(sK2,sK4) = k1_funct_1(k7_relat_1(sK1,sK3),X0_43) ),
    inference(instantiation,[status(thm)],[c_22082])).

cnf(c_45018,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) != k1_funct_1(k7_relat_1(sK2,sK3),sK4)
    | k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(sK2,sK3),sK4)
    | k1_funct_1(sK2,sK4) = k1_funct_1(k7_relat_1(sK1,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_45017])).

cnf(c_553,plain,
    ( k1_funct_1(X0_41,X0_43) = k1_funct_1(X1_41,X1_43)
    | X0_43 != X1_43
    | X0_41 != X1_41 ),
    theory(equality)).

cnf(c_22083,plain,
    ( k1_funct_1(X0_41,X0_43) = k1_funct_1(k7_relat_1(sK2,X0_42),sK4)
    | X0_43 != sK4
    | X0_41 != k7_relat_1(sK2,X0_42) ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(c_32242,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),X0_43) = k1_funct_1(k7_relat_1(sK2,sK3),sK4)
    | X0_43 != sK4
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_22083])).

cnf(c_32243,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) = k1_funct_1(k7_relat_1(sK2,sK3),sK4)
    | sK4 != sK4
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_32242])).

cnf(c_4183,plain,
    ( X0_44 != X1_44
    | X0_44 = k1_funct_1(X0_41,X0_43)
    | k1_funct_1(X0_41,X0_43) != X1_44 ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_8682,plain,
    ( X0_44 != k1_funct_1(X0_41,X0_43)
    | X0_44 = k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43)
    | k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43) != k1_funct_1(X0_41,X0_43) ),
    inference(instantiation,[status(thm)],[c_4183])).

cnf(c_13740,plain,
    ( k1_funct_1(X0_41,X0_43) != k1_funct_1(X1_41,X1_43)
    | k1_funct_1(X0_41,X0_43) = k1_funct_1(k7_relat_1(X1_41,X0_42),X1_43)
    | k1_funct_1(k7_relat_1(X1_41,X0_42),X1_43) != k1_funct_1(X1_41,X1_43) ),
    inference(instantiation,[status(thm)],[c_8682])).

cnf(c_21752,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1)) != k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1))
    | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1))
    | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) != k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1)) ),
    inference(instantiation,[status(thm)],[c_13740])).

cnf(c_965,plain,
    ( k1_funct_1(sK2,sK4) != X0_44
    | k1_funct_1(sK1,sK4) != X0_44
    | k1_funct_1(sK1,sK4) = k1_funct_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_998,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(X0_41,X0_43)
    | k1_funct_1(sK1,sK4) != k1_funct_1(X0_41,X0_43)
    | k1_funct_1(sK1,sK4) = k1_funct_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_21744,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43)
    | k1_funct_1(sK1,sK4) != k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43)
    | k1_funct_1(sK1,sK4) = k1_funct_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_21746,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(sK1,sK3),sK4)
    | k1_funct_1(sK1,sK4) != k1_funct_1(k7_relat_1(sK1,sK3),sK4)
    | k1_funct_1(sK1,sK4) = k1_funct_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_21744])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_531,negated_conjecture,
    ( ~ r2_hidden(X0_43,sK3)
    | k1_funct_1(sK1,X0_43) = k1_funct_1(sK2,X0_43)
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_14389,plain,
    ( ~ r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),sK3)
    | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1))
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_531])).

cnf(c_14392,plain,
    ( k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1))
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14389])).

cnf(c_2404,plain,
    ( X0_44 != X1_44
    | k1_funct_1(sK1,sK4) != X1_44
    | k1_funct_1(sK1,sK4) = X0_44 ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_3839,plain,
    ( X0_44 != k1_funct_1(sK1,sK4)
    | k1_funct_1(sK1,sK4) = X0_44
    | k1_funct_1(sK1,sK4) != k1_funct_1(sK1,sK4) ),
    inference(instantiation,[status(thm)],[c_2404])).

cnf(c_8218,plain,
    ( k1_funct_1(k7_relat_1(sK1,X0_42),sK4) != k1_funct_1(sK1,sK4)
    | k1_funct_1(sK1,sK4) = k1_funct_1(k7_relat_1(sK1,X0_42),sK4)
    | k1_funct_1(sK1,sK4) != k1_funct_1(sK1,sK4) ),
    inference(instantiation,[status(thm)],[c_3839])).

cnf(c_8220,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) != k1_funct_1(sK1,sK4)
    | k1_funct_1(sK1,sK4) = k1_funct_1(k7_relat_1(sK1,sK3),sK4)
    | k1_funct_1(sK1,sK4) != k1_funct_1(sK1,sK4) ),
    inference(instantiation,[status(thm)],[c_8218])).

cnf(c_1037,plain,
    ( X0_44 != k1_funct_1(sK2,sK4)
    | k1_funct_1(sK2,sK4) = X0_44
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_1116,plain,
    ( k1_funct_1(X0_41,X0_43) != k1_funct_1(sK2,sK4)
    | k1_funct_1(sK2,sK4) = k1_funct_1(X0_41,X0_43)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1037])).

cnf(c_5788,plain,
    ( k1_funct_1(k7_relat_1(sK2,X0_42),sK4) != k1_funct_1(sK2,sK4)
    | k1_funct_1(sK2,sK4) = k1_funct_1(k7_relat_1(sK2,X0_42),sK4)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1116])).

cnf(c_5793,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK3),sK4) != k1_funct_1(sK2,sK4)
    | k1_funct_1(sK2,sK4) = k1_funct_1(k7_relat_1(sK2,sK3),sK4)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_5788])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK3,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_165,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_relat_1(sK2)
    | k1_relat_1(k7_relat_1(X0,X1)) = X1
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_166,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_relat_1(sK2)
    | k1_relat_1(k7_relat_1(X0,sK3)) = sK3 ),
    inference(unflattening,[status(thm)],[c_165])).

cnf(c_526,plain,
    ( ~ v1_relat_1(X0_41)
    | k1_relat_1(X0_41) != k1_relat_1(sK2)
    | k1_relat_1(k7_relat_1(X0_41,sK3)) = sK3 ),
    inference(subtyping,[status(esa)],[c_166])).

cnf(c_836,plain,
    ( k1_relat_1(X0_41) != k1_relat_1(sK2)
    | k1_relat_1(k7_relat_1(X0_41,sK3)) = sK3
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_1028,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK3)) = sK3
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_836])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1393,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1028,c_18])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_527,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_835,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_539,plain,
    ( ~ v1_relat_1(X0_41)
    | k3_xboole_0(k1_relat_1(X0_41),X0_42) = k1_relat_1(k7_relat_1(X0_41,X0_42)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_824,plain,
    ( k3_xboole_0(k1_relat_1(X0_41),X0_42) = k1_relat_1(k7_relat_1(X0_41,X0_42))
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_1077,plain,
    ( k3_xboole_0(k1_relat_1(sK1),X0_42) = k1_relat_1(k7_relat_1(sK1,X0_42)) ),
    inference(superposition,[status(thm)],[c_835,c_824])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k3_xboole_0(k1_relat_1(X1),X2) != k1_relat_1(X0)
    | k7_relat_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_535,plain,
    ( r2_hidden(sK0(X0_41,X1_41),k1_relat_1(X0_41))
    | ~ v1_funct_1(X1_41)
    | ~ v1_funct_1(X0_41)
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | k3_xboole_0(k1_relat_1(X1_41),X0_42) != k1_relat_1(X0_41)
    | k7_relat_1(X1_41,X0_42) = X0_41 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_828,plain,
    ( k3_xboole_0(k1_relat_1(X0_41),X0_42) != k1_relat_1(X1_41)
    | k7_relat_1(X0_41,X0_42) = X1_41
    | r2_hidden(sK0(X1_41,X0_41),k1_relat_1(X1_41)) = iProver_top
    | v1_funct_1(X1_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v1_relat_1(X1_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_1308,plain,
    ( k1_relat_1(k7_relat_1(sK1,X0_42)) != k1_relat_1(X0_41)
    | k7_relat_1(sK1,X0_42) = X0_41
    | r2_hidden(sK0(X0_41,sK1),k1_relat_1(X0_41)) = iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1077,c_828])).

cnf(c_16,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3966,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | k1_relat_1(k7_relat_1(sK1,X0_42)) != k1_relat_1(X0_41)
    | k7_relat_1(sK1,X0_42) = X0_41
    | r2_hidden(sK0(X0_41,sK1),k1_relat_1(X0_41)) = iProver_top
    | v1_funct_1(X0_41) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1308,c_16,c_17])).

cnf(c_3967,plain,
    ( k1_relat_1(k7_relat_1(sK1,X0_42)) != k1_relat_1(X0_41)
    | k7_relat_1(sK1,X0_42) = X0_41
    | r2_hidden(sK0(X0_41,sK1),k1_relat_1(X0_41)) = iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(renaming,[status(thm)],[c_3966])).

cnf(c_3977,plain,
    ( k1_relat_1(k7_relat_1(sK1,X0_42)) != sK3
    | k7_relat_1(sK1,X0_42) = k7_relat_1(sK2,sK3)
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),k1_relat_1(k7_relat_1(sK2,sK3))) = iProver_top
    | v1_funct_1(k7_relat_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1393,c_3967])).

cnf(c_4032,plain,
    ( k1_relat_1(k7_relat_1(sK1,X0_42)) != sK3
    | k7_relat_1(sK1,X0_42) = k7_relat_1(sK2,sK3)
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),sK3) = iProver_top
    | v1_funct_1(k7_relat_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3977,c_1393])).

cnf(c_4075,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK3)) != sK3
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)
    | r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),sK3) = iProver_top
    | v1_funct_1(k7_relat_1(sK2,sK3)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4032])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK3,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_180,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(X0,X1)) = X1
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_181,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(X0,sK3)) = sK3 ),
    inference(unflattening,[status(thm)],[c_180])).

cnf(c_525,plain,
    ( ~ v1_relat_1(X0_41)
    | k1_relat_1(X0_41) != k1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(X0_41,sK3)) = sK3 ),
    inference(subtyping,[status(esa)],[c_181])).

cnf(c_837,plain,
    ( k1_relat_1(X0_41) != k1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(X0_41,sK3)) = sK3
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_1316,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK3)) = sK3
    | v1_relat_1(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_837])).

cnf(c_549,plain,
    ( k1_relat_1(X0_41) = k1_relat_1(X1_41)
    | X0_41 != X1_41 ),
    theory(equality)).

cnf(c_556,plain,
    ( k1_relat_1(sK1) = k1_relat_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_541,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_563,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_597,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(sK1,sK3)) = sK3
    | k1_relat_1(sK1) != k1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_1443,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1316,c_15,c_556,c_563,c_597])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k7_relat_1(X1,X2),X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_534,plain,
    ( ~ r2_hidden(X0_43,k1_relat_1(k7_relat_1(X0_41,X0_42)))
    | ~ v1_funct_1(X0_41)
    | ~ v1_relat_1(X0_41)
    | k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43) = k1_funct_1(X0_41,X0_43) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_829,plain,
    ( k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43) = k1_funct_1(X0_41,X0_43)
    | r2_hidden(X0_43,k1_relat_1(k7_relat_1(X0_41,X0_42))) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_1449,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),X0_43) = k1_funct_1(sK1,X0_43)
    | r2_hidden(X0_43,sK3) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1443,c_829])).

cnf(c_2848,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK3),X0_43) = k1_funct_1(sK1,X0_43)
    | r2_hidden(X0_43,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1449,c_16,c_17])).

cnf(c_2850,plain,
    ( ~ r2_hidden(X0_43,sK3)
    | k1_funct_1(k7_relat_1(sK1,sK3),X0_43) = k1_funct_1(sK1,X0_43) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2848])).

cnf(c_2852,plain,
    ( ~ r2_hidden(sK4,sK3)
    | k1_funct_1(k7_relat_1(sK1,sK3),sK4) = k1_funct_1(sK1,sK4) ),
    inference(instantiation,[status(thm)],[c_2850])).

cnf(c_1399,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK3),X0_43) = k1_funct_1(sK2,X0_43)
    | r2_hidden(X0_43,sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1393,c_829])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2839,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK3),X0_43) = k1_funct_1(sK2,X0_43)
    | r2_hidden(X0_43,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1399,c_18,c_19])).

cnf(c_2841,plain,
    ( ~ r2_hidden(X0_43,sK3)
    | k1_funct_1(k7_relat_1(sK2,sK3),X0_43) = k1_funct_1(sK2,X0_43) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2839])).

cnf(c_2843,plain,
    ( ~ r2_hidden(sK4,sK3)
    | k1_funct_1(k7_relat_1(sK2,sK3),sK4) = k1_funct_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_2841])).

cnf(c_546,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_1005,plain,
    ( X0_42 != X1_42
    | k1_relat_1(X0_41) != X1_42
    | k1_relat_1(X0_41) = X0_42 ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_1069,plain,
    ( X0_42 != X1_42
    | k1_relat_1(k7_relat_1(X0_41,sK3)) != X1_42
    | k1_relat_1(k7_relat_1(X0_41,sK3)) = X0_42 ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_1302,plain,
    ( k1_relat_1(k7_relat_1(X0_41,sK3)) != X0_42
    | k1_relat_1(k7_relat_1(X1_41,sK3)) != X0_42
    | k1_relat_1(k7_relat_1(X1_41,sK3)) = k1_relat_1(k7_relat_1(X0_41,sK3)) ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_2624,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK3)) != X0_42
    | k1_relat_1(k7_relat_1(sK2,sK3)) = k1_relat_1(k7_relat_1(sK1,sK3))
    | k1_relat_1(k7_relat_1(sK1,sK3)) != X0_42 ),
    inference(instantiation,[status(thm)],[c_1302])).

cnf(c_2625,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK3)) = k1_relat_1(k7_relat_1(sK1,sK3))
    | k1_relat_1(k7_relat_1(sK2,sK3)) != sK3
    | k1_relat_1(k7_relat_1(sK1,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_2624])).

cnf(c_974,plain,
    ( k3_xboole_0(k1_relat_1(X0_41),X0_42) != X1_42
    | k3_xboole_0(k1_relat_1(X0_41),X0_42) = k1_relat_1(X1_41)
    | k1_relat_1(X1_41) != X1_42 ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_1006,plain,
    ( k3_xboole_0(k1_relat_1(X0_41),X0_42) != k1_relat_1(X1_41)
    | k3_xboole_0(k1_relat_1(X0_41),X0_42) = k1_relat_1(X2_41)
    | k1_relat_1(X2_41) != k1_relat_1(X1_41) ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_1062,plain,
    ( k3_xboole_0(k1_relat_1(X0_41),X0_42) = k1_relat_1(X1_41)
    | k3_xboole_0(k1_relat_1(X0_41),X0_42) != k1_relat_1(k7_relat_1(X0_41,X0_42))
    | k1_relat_1(X1_41) != k1_relat_1(k7_relat_1(X0_41,X0_42)) ),
    inference(instantiation,[status(thm)],[c_1006])).

cnf(c_1191,plain,
    ( k3_xboole_0(k1_relat_1(X0_41),X0_42) != k1_relat_1(k7_relat_1(X0_41,X0_42))
    | k3_xboole_0(k1_relat_1(X0_41),X0_42) = k1_relat_1(k7_relat_1(X1_41,sK3))
    | k1_relat_1(k7_relat_1(X1_41,sK3)) != k1_relat_1(k7_relat_1(X0_41,X0_42)) ),
    inference(instantiation,[status(thm)],[c_1062])).

cnf(c_2013,plain,
    ( k3_xboole_0(k1_relat_1(sK1),sK3) = k1_relat_1(k7_relat_1(sK2,sK3))
    | k3_xboole_0(k1_relat_1(sK1),sK3) != k1_relat_1(k7_relat_1(sK1,sK3))
    | k1_relat_1(k7_relat_1(sK2,sK3)) != k1_relat_1(k7_relat_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1191])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_537,plain,
    ( ~ v1_funct_1(X0_41)
    | ~ v1_relat_1(X0_41)
    | v1_relat_1(k7_relat_1(X0_41,X0_42)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1513,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k7_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_1514,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1513])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_538,plain,
    ( ~ v1_funct_1(X0_41)
    | v1_funct_1(k7_relat_1(X0_41,X0_42))
    | ~ v1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1207,plain,
    ( v1_funct_1(k7_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_1208,plain,
    ( v1_funct_1(k7_relat_1(sK2,sK3)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1207])).

cnf(c_1194,plain,
    ( ~ r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),k1_relat_1(k7_relat_1(sK2,sK3)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1)) ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
    | k3_xboole_0(k1_relat_1(X1),X2) != k1_relat_1(X0)
    | k7_relat_1(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_536,plain,
    ( ~ v1_funct_1(X0_41)
    | ~ v1_funct_1(X1_41)
    | ~ v1_relat_1(X1_41)
    | ~ v1_relat_1(X0_41)
    | k1_funct_1(X1_41,sK0(X0_41,X1_41)) != k1_funct_1(X0_41,sK0(X0_41,X1_41))
    | k3_xboole_0(k1_relat_1(X1_41),X0_42) != k1_relat_1(X0_41)
    | k7_relat_1(X1_41,X0_42) = X0_41 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1049,plain,
    ( ~ v1_funct_1(X0_41)
    | ~ v1_funct_1(k7_relat_1(X1_41,sK3))
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(k7_relat_1(X1_41,sK3))
    | k1_funct_1(X0_41,sK0(k7_relat_1(X1_41,sK3),X0_41)) != k1_funct_1(k7_relat_1(X1_41,sK3),sK0(k7_relat_1(X1_41,sK3),X0_41))
    | k3_xboole_0(k1_relat_1(X0_41),X0_42) != k1_relat_1(k7_relat_1(X1_41,sK3))
    | k7_relat_1(X0_41,X0_42) = k7_relat_1(X1_41,sK3) ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_1143,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) != k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1))
    | k3_xboole_0(k1_relat_1(sK1),sK3) != k1_relat_1(k7_relat_1(sK2,sK3))
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_1050,plain,
    ( r2_hidden(sK0(k7_relat_1(X0_41,sK3),X1_41),k1_relat_1(k7_relat_1(X0_41,sK3)))
    | ~ v1_funct_1(X1_41)
    | ~ v1_funct_1(k7_relat_1(X0_41,sK3))
    | ~ v1_relat_1(X1_41)
    | ~ v1_relat_1(k7_relat_1(X0_41,sK3))
    | k3_xboole_0(k1_relat_1(X1_41),X0_42) != k1_relat_1(k7_relat_1(X0_41,sK3))
    | k7_relat_1(X1_41,X0_42) = k7_relat_1(X0_41,sK3) ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_1128,plain,
    ( r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),k1_relat_1(k7_relat_1(sK2,sK3)))
    | ~ v1_funct_1(k7_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK1)
    | k3_xboole_0(k1_relat_1(sK1),sK3) != k1_relat_1(k7_relat_1(sK2,sK3))
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_544,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_1038,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(sK4,sK3)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_532,negated_conjecture,
    ( r2_hidden(sK4,sK3)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_7,negated_conjecture,
    ( k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_533,negated_conjecture,
    ( k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_568,plain,
    ( ~ v1_relat_1(sK1)
    | k3_xboole_0(k1_relat_1(sK1),sK3) = k1_relat_1(k7_relat_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_543,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_565,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_560,plain,
    ( k1_funct_1(sK1,sK4) = k1_funct_1(sK1,sK4)
    | sK4 != sK4
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_45018,c_32243,c_21752,c_21746,c_14392,c_8220,c_5793,c_4075,c_2852,c_2843,c_2625,c_2013,c_1514,c_1513,c_1208,c_1207,c_1194,c_1143,c_1128,c_1038,c_1028,c_597,c_532,c_533,c_568,c_565,c_563,c_560,c_556,c_19,c_12,c_18,c_13,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:57:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.74/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.74/1.98  
% 11.74/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.74/1.98  
% 11.74/1.98  ------  iProver source info
% 11.74/1.98  
% 11.74/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.74/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.74/1.98  git: non_committed_changes: false
% 11.74/1.98  git: last_make_outside_of_git: false
% 11.74/1.98  
% 11.74/1.98  ------ 
% 11.74/1.98  
% 11.74/1.98  ------ Input Options
% 11.74/1.98  
% 11.74/1.98  --out_options                           all
% 11.74/1.98  --tptp_safe_out                         true
% 11.74/1.98  --problem_path                          ""
% 11.74/1.98  --include_path                          ""
% 11.74/1.98  --clausifier                            res/vclausify_rel
% 11.74/1.98  --clausifier_options                    --mode clausify
% 11.74/1.98  --stdin                                 false
% 11.74/1.98  --stats_out                             all
% 11.74/1.98  
% 11.74/1.98  ------ General Options
% 11.74/1.98  
% 11.74/1.98  --fof                                   false
% 11.74/1.98  --time_out_real                         305.
% 11.74/1.98  --time_out_virtual                      -1.
% 11.74/1.98  --symbol_type_check                     false
% 11.74/1.98  --clausify_out                          false
% 11.74/1.98  --sig_cnt_out                           false
% 11.74/1.98  --trig_cnt_out                          false
% 11.74/1.98  --trig_cnt_out_tolerance                1.
% 11.74/1.98  --trig_cnt_out_sk_spl                   false
% 11.74/1.98  --abstr_cl_out                          false
% 11.74/1.98  
% 11.74/1.98  ------ Global Options
% 11.74/1.98  
% 11.74/1.98  --schedule                              default
% 11.74/1.98  --add_important_lit                     false
% 11.74/1.98  --prop_solver_per_cl                    1000
% 11.74/1.98  --min_unsat_core                        false
% 11.74/1.98  --soft_assumptions                      false
% 11.74/1.98  --soft_lemma_size                       3
% 11.74/1.98  --prop_impl_unit_size                   0
% 11.74/1.98  --prop_impl_unit                        []
% 11.74/1.98  --share_sel_clauses                     true
% 11.74/1.98  --reset_solvers                         false
% 11.74/1.98  --bc_imp_inh                            [conj_cone]
% 11.74/1.98  --conj_cone_tolerance                   3.
% 11.74/1.98  --extra_neg_conj                        none
% 11.74/1.98  --large_theory_mode                     true
% 11.74/1.98  --prolific_symb_bound                   200
% 11.74/1.98  --lt_threshold                          2000
% 11.74/1.98  --clause_weak_htbl                      true
% 11.74/1.98  --gc_record_bc_elim                     false
% 11.74/1.98  
% 11.74/1.98  ------ Preprocessing Options
% 11.74/1.98  
% 11.74/1.98  --preprocessing_flag                    true
% 11.74/1.98  --time_out_prep_mult                    0.1
% 11.74/1.98  --splitting_mode                        input
% 11.74/1.98  --splitting_grd                         true
% 11.74/1.98  --splitting_cvd                         false
% 11.74/1.98  --splitting_cvd_svl                     false
% 11.74/1.98  --splitting_nvd                         32
% 11.74/1.98  --sub_typing                            true
% 11.74/1.98  --prep_gs_sim                           true
% 11.74/1.98  --prep_unflatten                        true
% 11.74/1.98  --prep_res_sim                          true
% 11.74/1.98  --prep_upred                            true
% 11.74/1.98  --prep_sem_filter                       exhaustive
% 11.74/1.98  --prep_sem_filter_out                   false
% 11.74/1.98  --pred_elim                             true
% 11.74/1.98  --res_sim_input                         true
% 11.74/1.98  --eq_ax_congr_red                       true
% 11.74/1.98  --pure_diseq_elim                       true
% 11.74/1.98  --brand_transform                       false
% 11.74/1.98  --non_eq_to_eq                          false
% 11.74/1.98  --prep_def_merge                        true
% 11.74/1.98  --prep_def_merge_prop_impl              false
% 11.74/1.98  --prep_def_merge_mbd                    true
% 11.74/1.98  --prep_def_merge_tr_red                 false
% 11.74/1.98  --prep_def_merge_tr_cl                  false
% 11.74/1.98  --smt_preprocessing                     true
% 11.74/1.98  --smt_ac_axioms                         fast
% 11.74/1.98  --preprocessed_out                      false
% 11.74/1.98  --preprocessed_stats                    false
% 11.74/1.98  
% 11.74/1.98  ------ Abstraction refinement Options
% 11.74/1.98  
% 11.74/1.98  --abstr_ref                             []
% 11.74/1.98  --abstr_ref_prep                        false
% 11.74/1.98  --abstr_ref_until_sat                   false
% 11.74/1.98  --abstr_ref_sig_restrict                funpre
% 11.74/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.74/1.98  --abstr_ref_under                       []
% 11.74/1.98  
% 11.74/1.98  ------ SAT Options
% 11.74/1.98  
% 11.74/1.98  --sat_mode                              false
% 11.74/1.98  --sat_fm_restart_options                ""
% 11.74/1.98  --sat_gr_def                            false
% 11.74/1.98  --sat_epr_types                         true
% 11.74/1.98  --sat_non_cyclic_types                  false
% 11.74/1.98  --sat_finite_models                     false
% 11.74/1.98  --sat_fm_lemmas                         false
% 11.74/1.98  --sat_fm_prep                           false
% 11.74/1.98  --sat_fm_uc_incr                        true
% 11.74/1.98  --sat_out_model                         small
% 11.74/1.98  --sat_out_clauses                       false
% 11.74/1.98  
% 11.74/1.98  ------ QBF Options
% 11.74/1.98  
% 11.74/1.98  --qbf_mode                              false
% 11.74/1.98  --qbf_elim_univ                         false
% 11.74/1.98  --qbf_dom_inst                          none
% 11.74/1.98  --qbf_dom_pre_inst                      false
% 11.74/1.98  --qbf_sk_in                             false
% 11.74/1.98  --qbf_pred_elim                         true
% 11.74/1.98  --qbf_split                             512
% 11.74/1.98  
% 11.74/1.98  ------ BMC1 Options
% 11.74/1.98  
% 11.74/1.98  --bmc1_incremental                      false
% 11.74/1.98  --bmc1_axioms                           reachable_all
% 11.74/1.98  --bmc1_min_bound                        0
% 11.74/1.98  --bmc1_max_bound                        -1
% 11.74/1.98  --bmc1_max_bound_default                -1
% 11.74/1.98  --bmc1_symbol_reachability              true
% 11.74/1.98  --bmc1_property_lemmas                  false
% 11.74/1.98  --bmc1_k_induction                      false
% 11.74/1.98  --bmc1_non_equiv_states                 false
% 11.74/1.98  --bmc1_deadlock                         false
% 11.74/1.98  --bmc1_ucm                              false
% 11.74/1.98  --bmc1_add_unsat_core                   none
% 11.74/1.98  --bmc1_unsat_core_children              false
% 11.74/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.74/1.98  --bmc1_out_stat                         full
% 11.74/1.98  --bmc1_ground_init                      false
% 11.74/1.98  --bmc1_pre_inst_next_state              false
% 11.74/1.98  --bmc1_pre_inst_state                   false
% 11.74/1.98  --bmc1_pre_inst_reach_state             false
% 11.74/1.98  --bmc1_out_unsat_core                   false
% 11.74/1.98  --bmc1_aig_witness_out                  false
% 11.74/1.98  --bmc1_verbose                          false
% 11.74/1.98  --bmc1_dump_clauses_tptp                false
% 11.74/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.74/1.98  --bmc1_dump_file                        -
% 11.74/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.74/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.74/1.98  --bmc1_ucm_extend_mode                  1
% 11.74/1.98  --bmc1_ucm_init_mode                    2
% 11.74/1.98  --bmc1_ucm_cone_mode                    none
% 11.74/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.74/1.98  --bmc1_ucm_relax_model                  4
% 11.74/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.74/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.74/1.98  --bmc1_ucm_layered_model                none
% 11.74/1.98  --bmc1_ucm_max_lemma_size               10
% 11.74/1.98  
% 11.74/1.98  ------ AIG Options
% 11.74/1.98  
% 11.74/1.98  --aig_mode                              false
% 11.74/1.98  
% 11.74/1.98  ------ Instantiation Options
% 11.74/1.98  
% 11.74/1.98  --instantiation_flag                    true
% 11.74/1.98  --inst_sos_flag                         false
% 11.74/1.98  --inst_sos_phase                        true
% 11.74/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.74/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.74/1.98  --inst_lit_sel_side                     num_symb
% 11.74/1.98  --inst_solver_per_active                1400
% 11.74/1.98  --inst_solver_calls_frac                1.
% 11.74/1.98  --inst_passive_queue_type               priority_queues
% 11.74/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.74/1.98  --inst_passive_queues_freq              [25;2]
% 11.74/1.98  --inst_dismatching                      true
% 11.74/1.98  --inst_eager_unprocessed_to_passive     true
% 11.74/1.98  --inst_prop_sim_given                   true
% 11.74/1.98  --inst_prop_sim_new                     false
% 11.74/1.98  --inst_subs_new                         false
% 11.74/1.98  --inst_eq_res_simp                      false
% 11.74/1.98  --inst_subs_given                       false
% 11.74/1.98  --inst_orphan_elimination               true
% 11.74/1.98  --inst_learning_loop_flag               true
% 11.74/1.98  --inst_learning_start                   3000
% 11.74/1.98  --inst_learning_factor                  2
% 11.74/1.98  --inst_start_prop_sim_after_learn       3
% 11.74/1.98  --inst_sel_renew                        solver
% 11.74/1.98  --inst_lit_activity_flag                true
% 11.74/1.98  --inst_restr_to_given                   false
% 11.74/1.98  --inst_activity_threshold               500
% 11.74/1.98  --inst_out_proof                        true
% 11.74/1.98  
% 11.74/1.98  ------ Resolution Options
% 11.74/1.98  
% 11.74/1.98  --resolution_flag                       true
% 11.74/1.98  --res_lit_sel                           adaptive
% 11.74/1.98  --res_lit_sel_side                      none
% 11.74/1.98  --res_ordering                          kbo
% 11.74/1.98  --res_to_prop_solver                    active
% 11.74/1.98  --res_prop_simpl_new                    false
% 11.74/1.98  --res_prop_simpl_given                  true
% 11.74/1.98  --res_passive_queue_type                priority_queues
% 11.74/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.74/1.98  --res_passive_queues_freq               [15;5]
% 11.74/1.98  --res_forward_subs                      full
% 11.74/1.98  --res_backward_subs                     full
% 11.74/1.98  --res_forward_subs_resolution           true
% 11.74/1.98  --res_backward_subs_resolution          true
% 11.74/1.98  --res_orphan_elimination                true
% 11.74/1.98  --res_time_limit                        2.
% 11.74/1.98  --res_out_proof                         true
% 11.74/1.98  
% 11.74/1.98  ------ Superposition Options
% 11.74/1.98  
% 11.74/1.98  --superposition_flag                    true
% 11.74/1.98  --sup_passive_queue_type                priority_queues
% 11.74/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.74/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.74/1.98  --demod_completeness_check              fast
% 11.74/1.98  --demod_use_ground                      true
% 11.74/1.98  --sup_to_prop_solver                    passive
% 11.74/1.98  --sup_prop_simpl_new                    true
% 11.74/1.98  --sup_prop_simpl_given                  true
% 11.74/1.98  --sup_fun_splitting                     false
% 11.74/1.98  --sup_smt_interval                      50000
% 11.74/1.98  
% 11.74/1.98  ------ Superposition Simplification Setup
% 11.74/1.98  
% 11.74/1.98  --sup_indices_passive                   []
% 11.74/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.74/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.74/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.74/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.74/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.74/1.98  --sup_full_bw                           [BwDemod]
% 11.74/1.98  --sup_immed_triv                        [TrivRules]
% 11.74/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.74/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.74/1.98  --sup_immed_bw_main                     []
% 11.74/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.74/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.74/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.74/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.74/1.98  
% 11.74/1.98  ------ Combination Options
% 11.74/1.98  
% 11.74/1.98  --comb_res_mult                         3
% 11.74/1.98  --comb_sup_mult                         2
% 11.74/1.98  --comb_inst_mult                        10
% 11.74/1.98  
% 11.74/1.98  ------ Debug Options
% 11.74/1.98  
% 11.74/1.98  --dbg_backtrace                         false
% 11.74/1.98  --dbg_dump_prop_clauses                 false
% 11.74/1.98  --dbg_dump_prop_clauses_file            -
% 11.74/1.98  --dbg_out_stat                          false
% 11.74/1.98  ------ Parsing...
% 11.74/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.74/1.98  
% 11.74/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.74/1.98  
% 11.74/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.74/1.98  
% 11.74/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.74/1.98  ------ Proving...
% 11.74/1.98  ------ Problem Properties 
% 11.74/1.98  
% 11.74/1.98  
% 11.74/1.98  clauses                                 15
% 11.74/1.98  conjectures                             7
% 11.74/1.98  EPR                                     4
% 11.74/1.98  Horn                                    13
% 11.74/1.98  unary                                   4
% 11.74/1.98  binary                                  3
% 11.74/1.98  lits                                    43
% 11.74/1.98  lits eq                                 16
% 11.74/1.98  fd_pure                                 0
% 11.74/1.98  fd_pseudo                               0
% 11.74/1.98  fd_cond                                 0
% 11.74/1.98  fd_pseudo_cond                          2
% 11.74/1.98  AC symbols                              0
% 11.74/1.98  
% 11.74/1.98  ------ Schedule dynamic 5 is on 
% 11.74/1.98  
% 11.74/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.74/1.98  
% 11.74/1.98  
% 11.74/1.98  ------ 
% 11.74/1.98  Current options:
% 11.74/1.98  ------ 
% 11.74/1.98  
% 11.74/1.98  ------ Input Options
% 11.74/1.98  
% 11.74/1.98  --out_options                           all
% 11.74/1.98  --tptp_safe_out                         true
% 11.74/1.98  --problem_path                          ""
% 11.74/1.98  --include_path                          ""
% 11.74/1.98  --clausifier                            res/vclausify_rel
% 11.74/1.98  --clausifier_options                    --mode clausify
% 11.74/1.98  --stdin                                 false
% 11.74/1.98  --stats_out                             all
% 11.74/1.98  
% 11.74/1.98  ------ General Options
% 11.74/1.98  
% 11.74/1.98  --fof                                   false
% 11.74/1.98  --time_out_real                         305.
% 11.74/1.98  --time_out_virtual                      -1.
% 11.74/1.98  --symbol_type_check                     false
% 11.74/1.98  --clausify_out                          false
% 11.74/1.98  --sig_cnt_out                           false
% 11.74/1.98  --trig_cnt_out                          false
% 11.74/1.98  --trig_cnt_out_tolerance                1.
% 11.74/1.98  --trig_cnt_out_sk_spl                   false
% 11.74/1.98  --abstr_cl_out                          false
% 11.74/1.98  
% 11.74/1.98  ------ Global Options
% 11.74/1.98  
% 11.74/1.98  --schedule                              default
% 11.74/1.98  --add_important_lit                     false
% 11.74/1.98  --prop_solver_per_cl                    1000
% 11.74/1.98  --min_unsat_core                        false
% 11.74/1.98  --soft_assumptions                      false
% 11.74/1.98  --soft_lemma_size                       3
% 11.74/1.98  --prop_impl_unit_size                   0
% 11.74/1.98  --prop_impl_unit                        []
% 11.74/1.98  --share_sel_clauses                     true
% 11.74/1.98  --reset_solvers                         false
% 11.74/1.98  --bc_imp_inh                            [conj_cone]
% 11.74/1.98  --conj_cone_tolerance                   3.
% 11.74/1.98  --extra_neg_conj                        none
% 11.74/1.98  --large_theory_mode                     true
% 11.74/1.98  --prolific_symb_bound                   200
% 11.74/1.98  --lt_threshold                          2000
% 11.74/1.98  --clause_weak_htbl                      true
% 11.74/1.98  --gc_record_bc_elim                     false
% 11.74/1.98  
% 11.74/1.98  ------ Preprocessing Options
% 11.74/1.98  
% 11.74/1.98  --preprocessing_flag                    true
% 11.74/1.98  --time_out_prep_mult                    0.1
% 11.74/1.98  --splitting_mode                        input
% 11.74/1.98  --splitting_grd                         true
% 11.74/1.98  --splitting_cvd                         false
% 11.74/1.98  --splitting_cvd_svl                     false
% 11.74/1.98  --splitting_nvd                         32
% 11.74/1.98  --sub_typing                            true
% 11.74/1.98  --prep_gs_sim                           true
% 11.74/1.98  --prep_unflatten                        true
% 11.74/1.98  --prep_res_sim                          true
% 11.74/1.98  --prep_upred                            true
% 11.74/1.98  --prep_sem_filter                       exhaustive
% 11.74/1.98  --prep_sem_filter_out                   false
% 11.74/1.98  --pred_elim                             true
% 11.74/1.98  --res_sim_input                         true
% 11.74/1.98  --eq_ax_congr_red                       true
% 11.74/1.98  --pure_diseq_elim                       true
% 11.74/1.98  --brand_transform                       false
% 11.74/1.98  --non_eq_to_eq                          false
% 11.74/1.98  --prep_def_merge                        true
% 11.74/1.98  --prep_def_merge_prop_impl              false
% 11.74/1.98  --prep_def_merge_mbd                    true
% 11.74/1.98  --prep_def_merge_tr_red                 false
% 11.74/1.98  --prep_def_merge_tr_cl                  false
% 11.74/1.98  --smt_preprocessing                     true
% 11.74/1.98  --smt_ac_axioms                         fast
% 11.74/1.98  --preprocessed_out                      false
% 11.74/1.98  --preprocessed_stats                    false
% 11.74/1.98  
% 11.74/1.98  ------ Abstraction refinement Options
% 11.74/1.98  
% 11.74/1.98  --abstr_ref                             []
% 11.74/1.98  --abstr_ref_prep                        false
% 11.74/1.98  --abstr_ref_until_sat                   false
% 11.74/1.98  --abstr_ref_sig_restrict                funpre
% 11.74/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.74/1.98  --abstr_ref_under                       []
% 11.74/1.98  
% 11.74/1.98  ------ SAT Options
% 11.74/1.98  
% 11.74/1.98  --sat_mode                              false
% 11.74/1.98  --sat_fm_restart_options                ""
% 11.74/1.98  --sat_gr_def                            false
% 11.74/1.98  --sat_epr_types                         true
% 11.74/1.98  --sat_non_cyclic_types                  false
% 11.74/1.98  --sat_finite_models                     false
% 11.74/1.98  --sat_fm_lemmas                         false
% 11.74/1.98  --sat_fm_prep                           false
% 11.74/1.98  --sat_fm_uc_incr                        true
% 11.74/1.98  --sat_out_model                         small
% 11.74/1.98  --sat_out_clauses                       false
% 11.74/1.98  
% 11.74/1.98  ------ QBF Options
% 11.74/1.98  
% 11.74/1.98  --qbf_mode                              false
% 11.74/1.98  --qbf_elim_univ                         false
% 11.74/1.98  --qbf_dom_inst                          none
% 11.74/1.98  --qbf_dom_pre_inst                      false
% 11.74/1.98  --qbf_sk_in                             false
% 11.74/1.98  --qbf_pred_elim                         true
% 11.74/1.98  --qbf_split                             512
% 11.74/1.98  
% 11.74/1.98  ------ BMC1 Options
% 11.74/1.98  
% 11.74/1.98  --bmc1_incremental                      false
% 11.74/1.98  --bmc1_axioms                           reachable_all
% 11.74/1.98  --bmc1_min_bound                        0
% 11.74/1.98  --bmc1_max_bound                        -1
% 11.74/1.98  --bmc1_max_bound_default                -1
% 11.74/1.98  --bmc1_symbol_reachability              true
% 11.74/1.98  --bmc1_property_lemmas                  false
% 11.74/1.98  --bmc1_k_induction                      false
% 11.74/1.98  --bmc1_non_equiv_states                 false
% 11.74/1.98  --bmc1_deadlock                         false
% 11.74/1.98  --bmc1_ucm                              false
% 11.74/1.98  --bmc1_add_unsat_core                   none
% 11.74/1.98  --bmc1_unsat_core_children              false
% 11.74/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.74/1.98  --bmc1_out_stat                         full
% 11.74/1.98  --bmc1_ground_init                      false
% 11.74/1.98  --bmc1_pre_inst_next_state              false
% 11.74/1.98  --bmc1_pre_inst_state                   false
% 11.74/1.98  --bmc1_pre_inst_reach_state             false
% 11.74/1.98  --bmc1_out_unsat_core                   false
% 11.74/1.98  --bmc1_aig_witness_out                  false
% 11.74/1.98  --bmc1_verbose                          false
% 11.74/1.98  --bmc1_dump_clauses_tptp                false
% 11.74/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.74/1.98  --bmc1_dump_file                        -
% 11.74/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.74/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.74/1.98  --bmc1_ucm_extend_mode                  1
% 11.74/1.98  --bmc1_ucm_init_mode                    2
% 11.74/1.98  --bmc1_ucm_cone_mode                    none
% 11.74/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.74/1.98  --bmc1_ucm_relax_model                  4
% 11.74/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.74/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.74/1.98  --bmc1_ucm_layered_model                none
% 11.74/1.98  --bmc1_ucm_max_lemma_size               10
% 11.74/1.98  
% 11.74/1.98  ------ AIG Options
% 11.74/1.98  
% 11.74/1.98  --aig_mode                              false
% 11.74/1.98  
% 11.74/1.98  ------ Instantiation Options
% 11.74/1.98  
% 11.74/1.98  --instantiation_flag                    true
% 11.74/1.98  --inst_sos_flag                         false
% 11.74/1.98  --inst_sos_phase                        true
% 11.74/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.74/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.74/1.98  --inst_lit_sel_side                     none
% 11.74/1.98  --inst_solver_per_active                1400
% 11.74/1.98  --inst_solver_calls_frac                1.
% 11.74/1.98  --inst_passive_queue_type               priority_queues
% 11.74/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.74/1.98  --inst_passive_queues_freq              [25;2]
% 11.74/1.98  --inst_dismatching                      true
% 11.74/1.98  --inst_eager_unprocessed_to_passive     true
% 11.74/1.98  --inst_prop_sim_given                   true
% 11.74/1.98  --inst_prop_sim_new                     false
% 11.74/1.98  --inst_subs_new                         false
% 11.74/1.98  --inst_eq_res_simp                      false
% 11.74/1.98  --inst_subs_given                       false
% 11.74/1.98  --inst_orphan_elimination               true
% 11.74/1.98  --inst_learning_loop_flag               true
% 11.74/1.98  --inst_learning_start                   3000
% 11.74/1.98  --inst_learning_factor                  2
% 11.74/1.98  --inst_start_prop_sim_after_learn       3
% 11.74/1.98  --inst_sel_renew                        solver
% 11.74/1.98  --inst_lit_activity_flag                true
% 11.74/1.98  --inst_restr_to_given                   false
% 11.74/1.98  --inst_activity_threshold               500
% 11.74/1.98  --inst_out_proof                        true
% 11.74/1.98  
% 11.74/1.98  ------ Resolution Options
% 11.74/1.98  
% 11.74/1.98  --resolution_flag                       false
% 11.74/1.98  --res_lit_sel                           adaptive
% 11.74/1.98  --res_lit_sel_side                      none
% 11.74/1.98  --res_ordering                          kbo
% 11.74/1.98  --res_to_prop_solver                    active
% 11.74/1.98  --res_prop_simpl_new                    false
% 11.74/1.98  --res_prop_simpl_given                  true
% 11.74/1.98  --res_passive_queue_type                priority_queues
% 11.74/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.74/1.98  --res_passive_queues_freq               [15;5]
% 11.74/1.98  --res_forward_subs                      full
% 11.74/1.98  --res_backward_subs                     full
% 11.74/1.98  --res_forward_subs_resolution           true
% 11.74/1.98  --res_backward_subs_resolution          true
% 11.74/1.98  --res_orphan_elimination                true
% 11.74/1.98  --res_time_limit                        2.
% 11.74/1.98  --res_out_proof                         true
% 11.74/1.98  
% 11.74/1.98  ------ Superposition Options
% 11.74/1.98  
% 11.74/1.98  --superposition_flag                    true
% 11.74/1.98  --sup_passive_queue_type                priority_queues
% 11.74/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.74/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.74/1.98  --demod_completeness_check              fast
% 11.74/1.98  --demod_use_ground                      true
% 11.74/1.98  --sup_to_prop_solver                    passive
% 11.74/1.98  --sup_prop_simpl_new                    true
% 11.74/1.98  --sup_prop_simpl_given                  true
% 11.74/1.98  --sup_fun_splitting                     false
% 11.74/1.98  --sup_smt_interval                      50000
% 11.74/1.98  
% 11.74/1.98  ------ Superposition Simplification Setup
% 11.74/1.98  
% 11.74/1.98  --sup_indices_passive                   []
% 11.74/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.74/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.74/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.74/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.74/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.74/1.98  --sup_full_bw                           [BwDemod]
% 11.74/1.98  --sup_immed_triv                        [TrivRules]
% 11.74/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.74/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.74/1.98  --sup_immed_bw_main                     []
% 11.74/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.74/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.74/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.74/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.74/1.98  
% 11.74/1.98  ------ Combination Options
% 11.74/1.98  
% 11.74/1.98  --comb_res_mult                         3
% 11.74/1.98  --comb_sup_mult                         2
% 11.74/1.98  --comb_inst_mult                        10
% 11.74/1.98  
% 11.74/1.98  ------ Debug Options
% 11.74/1.98  
% 11.74/1.98  --dbg_backtrace                         false
% 11.74/1.98  --dbg_dump_prop_clauses                 false
% 11.74/1.98  --dbg_dump_prop_clauses_file            -
% 11.74/1.98  --dbg_out_stat                          false
% 11.74/1.98  
% 11.74/1.98  
% 11.74/1.98  
% 11.74/1.98  
% 11.74/1.98  ------ Proving...
% 11.74/1.98  
% 11.74/1.98  
% 11.74/1.98  % SZS status Theorem for theBenchmark.p
% 11.74/1.98  
% 11.74/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.74/1.98  
% 11.74/1.98  fof(f6,conjecture,(
% 11.74/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 11.74/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.98  
% 11.74/1.98  fof(f7,negated_conjecture,(
% 11.74/1.98    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 11.74/1.98    inference(negated_conjecture,[],[f6])).
% 11.74/1.98  
% 11.74/1.98  fof(f17,plain,(
% 11.74/1.98    ? [X0] : (? [X1] : (? [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <~> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) & (r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 11.74/1.98    inference(ennf_transformation,[],[f7])).
% 11.74/1.98  
% 11.74/1.98  fof(f18,plain,(
% 11.74/1.98    ? [X0] : (? [X1] : (? [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <~> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 11.74/1.98    inference(flattening,[],[f17])).
% 11.74/1.98  
% 11.74/1.98  fof(f21,plain,(
% 11.74/1.98    ? [X0] : (? [X1] : (? [X2] : (((? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2)) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2))) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 11.74/1.98    inference(nnf_transformation,[],[f18])).
% 11.74/1.98  
% 11.74/1.98  fof(f22,plain,(
% 11.74/1.98    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2)) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 11.74/1.98    inference(flattening,[],[f21])).
% 11.74/1.98  
% 11.74/1.98  fof(f23,plain,(
% 11.74/1.98    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2)) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 11.74/1.98    inference(rectify,[],[f22])).
% 11.74/1.98  
% 11.74/1.98  fof(f27,plain,(
% 11.74/1.98    ( ! [X2,X0,X1] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK4) != k1_funct_1(X1,sK4) & r2_hidden(sK4,X2))) )),
% 11.74/1.98    introduced(choice_axiom,[])).
% 11.74/1.98  
% 11.74/1.98  fof(f26,plain,(
% 11.74/1.98    ( ! [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2)) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => ((? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,sK3)) | k7_relat_1(X0,sK3) != k7_relat_1(X1,sK3)) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,sK3)) | k7_relat_1(X0,sK3) = k7_relat_1(X1,sK3)) & r1_tarski(sK3,k1_relat_1(X1)) & r1_tarski(sK3,k1_relat_1(X0)))) )),
% 11.74/1.98    introduced(choice_axiom,[])).
% 11.74/1.98  
% 11.74/1.98  fof(f25,plain,(
% 11.74/1.98    ( ! [X0] : (? [X1] : (? [X2] : ((? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2)) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((? [X3] : (k1_funct_1(sK2,X3) != k1_funct_1(X0,X3) & r2_hidden(X3,X2)) | k7_relat_1(sK2,X2) != k7_relat_1(X0,X2)) & (! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(X0,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(sK2,X2) = k7_relat_1(X0,X2)) & r1_tarski(X2,k1_relat_1(sK2)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(sK2) & v1_relat_1(sK2))) )),
% 11.74/1.98    introduced(choice_axiom,[])).
% 11.74/1.98  
% 11.74/1.98  fof(f24,plain,(
% 11.74/1.98    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2)) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((? [X3] : (k1_funct_1(sK1,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) | k7_relat_1(sK1,X2) != k7_relat_1(X1,X2)) & (! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(sK1,X2) = k7_relat_1(X1,X2)) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK1))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 11.74/1.98    introduced(choice_axiom,[])).
% 11.74/1.98  
% 11.74/1.98  fof(f28,plain,(
% 11.74/1.98    ((((k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4) & r2_hidden(sK4,sK3)) | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3)) & (! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK3)) | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)) & r1_tarski(sK3,k1_relat_1(sK2)) & r1_tarski(sK3,k1_relat_1(sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 11.74/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f27,f26,f25,f24])).
% 11.74/1.98  
% 11.74/1.98  fof(f42,plain,(
% 11.74/1.98    ( ! [X4] : (k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK3) | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)) )),
% 11.74/1.98    inference(cnf_transformation,[],[f28])).
% 11.74/1.98  
% 11.74/1.98  fof(f2,axiom,(
% 11.74/1.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 11.74/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.98  
% 11.74/1.98  fof(f9,plain,(
% 11.74/1.98    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 11.74/1.98    inference(ennf_transformation,[],[f2])).
% 11.74/1.98  
% 11.74/1.98  fof(f10,plain,(
% 11.74/1.98    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.74/1.98    inference(flattening,[],[f9])).
% 11.74/1.98  
% 11.74/1.98  fof(f30,plain,(
% 11.74/1.98    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.74/1.98    inference(cnf_transformation,[],[f10])).
% 11.74/1.98  
% 11.74/1.98  fof(f41,plain,(
% 11.74/1.98    r1_tarski(sK3,k1_relat_1(sK2))),
% 11.74/1.98    inference(cnf_transformation,[],[f28])).
% 11.74/1.98  
% 11.74/1.98  fof(f38,plain,(
% 11.74/1.98    v1_relat_1(sK2)),
% 11.74/1.98    inference(cnf_transformation,[],[f28])).
% 11.74/1.98  
% 11.74/1.98  fof(f36,plain,(
% 11.74/1.98    v1_relat_1(sK1)),
% 11.74/1.98    inference(cnf_transformation,[],[f28])).
% 11.74/1.98  
% 11.74/1.98  fof(f1,axiom,(
% 11.74/1.98    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 11.74/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.98  
% 11.74/1.98  fof(f8,plain,(
% 11.74/1.98    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 11.74/1.98    inference(ennf_transformation,[],[f1])).
% 11.74/1.98  
% 11.74/1.98  fof(f29,plain,(
% 11.74/1.98    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.74/1.98    inference(cnf_transformation,[],[f8])).
% 11.74/1.98  
% 11.74/1.98  fof(f4,axiom,(
% 11.74/1.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)) & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)) => k7_relat_1(X2,X0) = X1)))),
% 11.74/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.98  
% 11.74/1.98  fof(f13,plain,(
% 11.74/1.98    ! [X0,X1] : (! [X2] : ((k7_relat_1(X2,X0) = X1 | (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.74/1.98    inference(ennf_transformation,[],[f4])).
% 11.74/1.98  
% 11.74/1.98  fof(f14,plain,(
% 11.74/1.98    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | ? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.74/1.98    inference(flattening,[],[f13])).
% 11.74/1.98  
% 11.74/1.98  fof(f19,plain,(
% 11.74/1.98    ! [X2,X1] : (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2)) & r2_hidden(sK0(X1,X2),k1_relat_1(X1))))),
% 11.74/1.98    introduced(choice_axiom,[])).
% 11.74/1.98  
% 11.74/1.98  fof(f20,plain,(
% 11.74/1.98    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | (k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2)) & r2_hidden(sK0(X1,X2),k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.74/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f19])).
% 11.74/1.98  
% 11.74/1.98  fof(f33,plain,(
% 11.74/1.98    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = X1 | r2_hidden(sK0(X1,X2),k1_relat_1(X1)) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.74/1.98    inference(cnf_transformation,[],[f20])).
% 11.74/1.98  
% 11.74/1.98  fof(f37,plain,(
% 11.74/1.98    v1_funct_1(sK1)),
% 11.74/1.98    inference(cnf_transformation,[],[f28])).
% 11.74/1.98  
% 11.74/1.98  fof(f40,plain,(
% 11.74/1.98    r1_tarski(sK3,k1_relat_1(sK1))),
% 11.74/1.98    inference(cnf_transformation,[],[f28])).
% 11.74/1.98  
% 11.74/1.98  fof(f5,axiom,(
% 11.74/1.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 11.74/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.98  
% 11.74/1.98  fof(f15,plain,(
% 11.74/1.98    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 11.74/1.98    inference(ennf_transformation,[],[f5])).
% 11.74/1.98  
% 11.74/1.98  fof(f16,plain,(
% 11.74/1.98    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.74/1.98    inference(flattening,[],[f15])).
% 11.74/1.98  
% 11.74/1.98  fof(f35,plain,(
% 11.74/1.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.74/1.98    inference(cnf_transformation,[],[f16])).
% 11.74/1.98  
% 11.74/1.98  fof(f39,plain,(
% 11.74/1.98    v1_funct_1(sK2)),
% 11.74/1.98    inference(cnf_transformation,[],[f28])).
% 11.74/1.98  
% 11.74/1.98  fof(f3,axiom,(
% 11.74/1.98    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 11.74/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.74/1.98  
% 11.74/1.98  fof(f11,plain,(
% 11.74/1.98    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.74/1.98    inference(ennf_transformation,[],[f3])).
% 11.74/1.98  
% 11.74/1.98  fof(f12,plain,(
% 11.74/1.98    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.74/1.98    inference(flattening,[],[f11])).
% 11.74/1.98  
% 11.74/1.98  fof(f31,plain,(
% 11.74/1.98    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.74/1.98    inference(cnf_transformation,[],[f12])).
% 11.74/1.98  
% 11.74/1.98  fof(f32,plain,(
% 11.74/1.98    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.74/1.98    inference(cnf_transformation,[],[f12])).
% 11.74/1.98  
% 11.74/1.98  fof(f34,plain,(
% 11.74/1.98    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = X1 | k1_funct_1(X1,sK0(X1,X2)) != k1_funct_1(X2,sK0(X1,X2)) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.74/1.98    inference(cnf_transformation,[],[f20])).
% 11.74/1.98  
% 11.74/1.98  fof(f43,plain,(
% 11.74/1.98    r2_hidden(sK4,sK3) | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3)),
% 11.74/1.98    inference(cnf_transformation,[],[f28])).
% 11.74/1.98  
% 11.74/1.98  fof(f44,plain,(
% 11.74/1.98    k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4) | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3)),
% 11.74/1.98    inference(cnf_transformation,[],[f28])).
% 11.74/1.98  
% 11.74/1.98  cnf(c_547,plain,
% 11.74/1.98      ( X0_44 != X1_44 | X2_44 != X1_44 | X2_44 = X0_44 ),
% 11.74/1.98      theory(equality) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_997,plain,
% 11.74/1.98      ( X0_44 != X1_44
% 11.74/1.98      | k1_funct_1(sK2,sK4) != X1_44
% 11.74/1.98      | k1_funct_1(sK2,sK4) = X0_44 ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_547]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_17607,plain,
% 11.74/1.98      ( X0_44 != k1_funct_1(k7_relat_1(sK2,X0_42),sK4)
% 11.74/1.98      | k1_funct_1(sK2,sK4) = X0_44
% 11.74/1.98      | k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(sK2,X0_42),sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_997]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_22082,plain,
% 11.74/1.98      ( k1_funct_1(X0_41,X0_43) != k1_funct_1(k7_relat_1(sK2,X0_42),sK4)
% 11.74/1.98      | k1_funct_1(sK2,sK4) = k1_funct_1(X0_41,X0_43)
% 11.74/1.98      | k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(sK2,X0_42),sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_17607]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_45017,plain,
% 11.74/1.98      ( k1_funct_1(k7_relat_1(sK1,sK3),X0_43) != k1_funct_1(k7_relat_1(sK2,sK3),sK4)
% 11.74/1.98      | k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(sK2,sK3),sK4)
% 11.74/1.98      | k1_funct_1(sK2,sK4) = k1_funct_1(k7_relat_1(sK1,sK3),X0_43) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_22082]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_45018,plain,
% 11.74/1.98      ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) != k1_funct_1(k7_relat_1(sK2,sK3),sK4)
% 11.74/1.98      | k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(sK2,sK3),sK4)
% 11.74/1.98      | k1_funct_1(sK2,sK4) = k1_funct_1(k7_relat_1(sK1,sK3),sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_45017]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_553,plain,
% 11.74/1.98      ( k1_funct_1(X0_41,X0_43) = k1_funct_1(X1_41,X1_43)
% 11.74/1.98      | X0_43 != X1_43
% 11.74/1.98      | X0_41 != X1_41 ),
% 11.74/1.98      theory(equality) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_22083,plain,
% 11.74/1.98      ( k1_funct_1(X0_41,X0_43) = k1_funct_1(k7_relat_1(sK2,X0_42),sK4)
% 11.74/1.98      | X0_43 != sK4
% 11.74/1.98      | X0_41 != k7_relat_1(sK2,X0_42) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_553]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_32242,plain,
% 11.74/1.98      ( k1_funct_1(k7_relat_1(sK1,sK3),X0_43) = k1_funct_1(k7_relat_1(sK2,sK3),sK4)
% 11.74/1.98      | X0_43 != sK4
% 11.74/1.98      | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_22083]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_32243,plain,
% 11.74/1.98      ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) = k1_funct_1(k7_relat_1(sK2,sK3),sK4)
% 11.74/1.98      | sK4 != sK4
% 11.74/1.98      | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_32242]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_4183,plain,
% 11.74/1.98      ( X0_44 != X1_44
% 11.74/1.98      | X0_44 = k1_funct_1(X0_41,X0_43)
% 11.74/1.98      | k1_funct_1(X0_41,X0_43) != X1_44 ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_547]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_8682,plain,
% 11.74/1.98      ( X0_44 != k1_funct_1(X0_41,X0_43)
% 11.74/1.98      | X0_44 = k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43)
% 11.74/1.98      | k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43) != k1_funct_1(X0_41,X0_43) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_4183]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_13740,plain,
% 11.74/1.98      ( k1_funct_1(X0_41,X0_43) != k1_funct_1(X1_41,X1_43)
% 11.74/1.98      | k1_funct_1(X0_41,X0_43) = k1_funct_1(k7_relat_1(X1_41,X0_42),X1_43)
% 11.74/1.98      | k1_funct_1(k7_relat_1(X1_41,X0_42),X1_43) != k1_funct_1(X1_41,X1_43) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_8682]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_21752,plain,
% 11.74/1.98      ( k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1)) != k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1))
% 11.74/1.98      | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1))
% 11.74/1.98      | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) != k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1)) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_13740]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_965,plain,
% 11.74/1.98      ( k1_funct_1(sK2,sK4) != X0_44
% 11.74/1.98      | k1_funct_1(sK1,sK4) != X0_44
% 11.74/1.98      | k1_funct_1(sK1,sK4) = k1_funct_1(sK2,sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_547]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_998,plain,
% 11.74/1.98      ( k1_funct_1(sK2,sK4) != k1_funct_1(X0_41,X0_43)
% 11.74/1.98      | k1_funct_1(sK1,sK4) != k1_funct_1(X0_41,X0_43)
% 11.74/1.98      | k1_funct_1(sK1,sK4) = k1_funct_1(sK2,sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_965]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_21744,plain,
% 11.74/1.98      ( k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43)
% 11.74/1.98      | k1_funct_1(sK1,sK4) != k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43)
% 11.74/1.98      | k1_funct_1(sK1,sK4) = k1_funct_1(sK2,sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_998]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_21746,plain,
% 11.74/1.98      ( k1_funct_1(sK2,sK4) != k1_funct_1(k7_relat_1(sK1,sK3),sK4)
% 11.74/1.98      | k1_funct_1(sK1,sK4) != k1_funct_1(k7_relat_1(sK1,sK3),sK4)
% 11.74/1.98      | k1_funct_1(sK1,sK4) = k1_funct_1(sK2,sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_21744]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_9,negated_conjecture,
% 11.74/1.98      ( ~ r2_hidden(X0,sK3)
% 11.74/1.98      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
% 11.74/1.98      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
% 11.74/1.98      inference(cnf_transformation,[],[f42]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_531,negated_conjecture,
% 11.74/1.98      ( ~ r2_hidden(X0_43,sK3)
% 11.74/1.98      | k1_funct_1(sK1,X0_43) = k1_funct_1(sK2,X0_43)
% 11.74/1.98      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
% 11.74/1.98      inference(subtyping,[status(esa)],[c_9]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_14389,plain,
% 11.74/1.98      ( ~ r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),sK3)
% 11.74/1.98      | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1))
% 11.74/1.98      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_531]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_14392,plain,
% 11.74/1.98      ( k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1))
% 11.74/1.98      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)
% 11.74/1.98      | r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),sK3) != iProver_top ),
% 11.74/1.98      inference(predicate_to_equality,[status(thm)],[c_14389]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_2404,plain,
% 11.74/1.98      ( X0_44 != X1_44
% 11.74/1.98      | k1_funct_1(sK1,sK4) != X1_44
% 11.74/1.98      | k1_funct_1(sK1,sK4) = X0_44 ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_547]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_3839,plain,
% 11.74/1.98      ( X0_44 != k1_funct_1(sK1,sK4)
% 11.74/1.98      | k1_funct_1(sK1,sK4) = X0_44
% 11.74/1.98      | k1_funct_1(sK1,sK4) != k1_funct_1(sK1,sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_2404]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_8218,plain,
% 11.74/1.98      ( k1_funct_1(k7_relat_1(sK1,X0_42),sK4) != k1_funct_1(sK1,sK4)
% 11.74/1.98      | k1_funct_1(sK1,sK4) = k1_funct_1(k7_relat_1(sK1,X0_42),sK4)
% 11.74/1.98      | k1_funct_1(sK1,sK4) != k1_funct_1(sK1,sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_3839]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_8220,plain,
% 11.74/1.98      ( k1_funct_1(k7_relat_1(sK1,sK3),sK4) != k1_funct_1(sK1,sK4)
% 11.74/1.98      | k1_funct_1(sK1,sK4) = k1_funct_1(k7_relat_1(sK1,sK3),sK4)
% 11.74/1.98      | k1_funct_1(sK1,sK4) != k1_funct_1(sK1,sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_8218]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1037,plain,
% 11.74/1.98      ( X0_44 != k1_funct_1(sK2,sK4)
% 11.74/1.98      | k1_funct_1(sK2,sK4) = X0_44
% 11.74/1.98      | k1_funct_1(sK2,sK4) != k1_funct_1(sK2,sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_997]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1116,plain,
% 11.74/1.98      ( k1_funct_1(X0_41,X0_43) != k1_funct_1(sK2,sK4)
% 11.74/1.98      | k1_funct_1(sK2,sK4) = k1_funct_1(X0_41,X0_43)
% 11.74/1.98      | k1_funct_1(sK2,sK4) != k1_funct_1(sK2,sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_1037]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_5788,plain,
% 11.74/1.98      ( k1_funct_1(k7_relat_1(sK2,X0_42),sK4) != k1_funct_1(sK2,sK4)
% 11.74/1.98      | k1_funct_1(sK2,sK4) = k1_funct_1(k7_relat_1(sK2,X0_42),sK4)
% 11.74/1.98      | k1_funct_1(sK2,sK4) != k1_funct_1(sK2,sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_1116]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_5793,plain,
% 11.74/1.98      ( k1_funct_1(k7_relat_1(sK2,sK3),sK4) != k1_funct_1(sK2,sK4)
% 11.74/1.98      | k1_funct_1(sK2,sK4) = k1_funct_1(k7_relat_1(sK2,sK3),sK4)
% 11.74/1.98      | k1_funct_1(sK2,sK4) != k1_funct_1(sK2,sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_5788]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1,plain,
% 11.74/1.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 11.74/1.98      | ~ v1_relat_1(X1)
% 11.74/1.98      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 11.74/1.98      inference(cnf_transformation,[],[f30]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_10,negated_conjecture,
% 11.74/1.98      ( r1_tarski(sK3,k1_relat_1(sK2)) ),
% 11.74/1.98      inference(cnf_transformation,[],[f41]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_165,plain,
% 11.74/1.98      ( ~ v1_relat_1(X0)
% 11.74/1.98      | k1_relat_1(X0) != k1_relat_1(sK2)
% 11.74/1.98      | k1_relat_1(k7_relat_1(X0,X1)) = X1
% 11.74/1.98      | sK3 != X1 ),
% 11.74/1.98      inference(resolution_lifted,[status(thm)],[c_1,c_10]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_166,plain,
% 11.74/1.98      ( ~ v1_relat_1(X0)
% 11.74/1.98      | k1_relat_1(X0) != k1_relat_1(sK2)
% 11.74/1.98      | k1_relat_1(k7_relat_1(X0,sK3)) = sK3 ),
% 11.74/1.98      inference(unflattening,[status(thm)],[c_165]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_526,plain,
% 11.74/1.98      ( ~ v1_relat_1(X0_41)
% 11.74/1.98      | k1_relat_1(X0_41) != k1_relat_1(sK2)
% 11.74/1.98      | k1_relat_1(k7_relat_1(X0_41,sK3)) = sK3 ),
% 11.74/1.98      inference(subtyping,[status(esa)],[c_166]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_836,plain,
% 11.74/1.98      ( k1_relat_1(X0_41) != k1_relat_1(sK2)
% 11.74/1.98      | k1_relat_1(k7_relat_1(X0_41,sK3)) = sK3
% 11.74/1.98      | v1_relat_1(X0_41) != iProver_top ),
% 11.74/1.98      inference(predicate_to_equality,[status(thm)],[c_526]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1028,plain,
% 11.74/1.98      ( k1_relat_1(k7_relat_1(sK2,sK3)) = sK3
% 11.74/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.74/1.98      inference(equality_resolution,[status(thm)],[c_836]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_13,negated_conjecture,
% 11.74/1.98      ( v1_relat_1(sK2) ),
% 11.74/1.98      inference(cnf_transformation,[],[f38]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_18,plain,
% 11.74/1.98      ( v1_relat_1(sK2) = iProver_top ),
% 11.74/1.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1393,plain,
% 11.74/1.98      ( k1_relat_1(k7_relat_1(sK2,sK3)) = sK3 ),
% 11.74/1.98      inference(global_propositional_subsumption,
% 11.74/1.98                [status(thm)],
% 11.74/1.98                [c_1028,c_18]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_15,negated_conjecture,
% 11.74/1.98      ( v1_relat_1(sK1) ),
% 11.74/1.98      inference(cnf_transformation,[],[f36]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_527,negated_conjecture,
% 11.74/1.98      ( v1_relat_1(sK1) ),
% 11.74/1.98      inference(subtyping,[status(esa)],[c_15]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_835,plain,
% 11.74/1.98      ( v1_relat_1(sK1) = iProver_top ),
% 11.74/1.98      inference(predicate_to_equality,[status(thm)],[c_527]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_0,plain,
% 11.74/1.98      ( ~ v1_relat_1(X0)
% 11.74/1.98      | k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 11.74/1.98      inference(cnf_transformation,[],[f29]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_539,plain,
% 11.74/1.98      ( ~ v1_relat_1(X0_41)
% 11.74/1.98      | k3_xboole_0(k1_relat_1(X0_41),X0_42) = k1_relat_1(k7_relat_1(X0_41,X0_42)) ),
% 11.74/1.98      inference(subtyping,[status(esa)],[c_0]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_824,plain,
% 11.74/1.98      ( k3_xboole_0(k1_relat_1(X0_41),X0_42) = k1_relat_1(k7_relat_1(X0_41,X0_42))
% 11.74/1.98      | v1_relat_1(X0_41) != iProver_top ),
% 11.74/1.98      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1077,plain,
% 11.74/1.98      ( k3_xboole_0(k1_relat_1(sK1),X0_42) = k1_relat_1(k7_relat_1(sK1,X0_42)) ),
% 11.74/1.98      inference(superposition,[status(thm)],[c_835,c_824]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_5,plain,
% 11.74/1.98      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 11.74/1.98      | ~ v1_funct_1(X0)
% 11.74/1.98      | ~ v1_funct_1(X1)
% 11.74/1.98      | ~ v1_relat_1(X0)
% 11.74/1.98      | ~ v1_relat_1(X1)
% 11.74/1.98      | k3_xboole_0(k1_relat_1(X1),X2) != k1_relat_1(X0)
% 11.74/1.98      | k7_relat_1(X1,X2) = X0 ),
% 11.74/1.98      inference(cnf_transformation,[],[f33]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_535,plain,
% 11.74/1.98      ( r2_hidden(sK0(X0_41,X1_41),k1_relat_1(X0_41))
% 11.74/1.98      | ~ v1_funct_1(X1_41)
% 11.74/1.98      | ~ v1_funct_1(X0_41)
% 11.74/1.98      | ~ v1_relat_1(X0_41)
% 11.74/1.98      | ~ v1_relat_1(X1_41)
% 11.74/1.98      | k3_xboole_0(k1_relat_1(X1_41),X0_42) != k1_relat_1(X0_41)
% 11.74/1.98      | k7_relat_1(X1_41,X0_42) = X0_41 ),
% 11.74/1.98      inference(subtyping,[status(esa)],[c_5]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_828,plain,
% 11.74/1.98      ( k3_xboole_0(k1_relat_1(X0_41),X0_42) != k1_relat_1(X1_41)
% 11.74/1.98      | k7_relat_1(X0_41,X0_42) = X1_41
% 11.74/1.98      | r2_hidden(sK0(X1_41,X0_41),k1_relat_1(X1_41)) = iProver_top
% 11.74/1.98      | v1_funct_1(X1_41) != iProver_top
% 11.74/1.98      | v1_funct_1(X0_41) != iProver_top
% 11.74/1.98      | v1_relat_1(X1_41) != iProver_top
% 11.74/1.98      | v1_relat_1(X0_41) != iProver_top ),
% 11.74/1.98      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1308,plain,
% 11.74/1.98      ( k1_relat_1(k7_relat_1(sK1,X0_42)) != k1_relat_1(X0_41)
% 11.74/1.98      | k7_relat_1(sK1,X0_42) = X0_41
% 11.74/1.98      | r2_hidden(sK0(X0_41,sK1),k1_relat_1(X0_41)) = iProver_top
% 11.74/1.98      | v1_funct_1(X0_41) != iProver_top
% 11.74/1.98      | v1_funct_1(sK1) != iProver_top
% 11.74/1.98      | v1_relat_1(X0_41) != iProver_top
% 11.74/1.98      | v1_relat_1(sK1) != iProver_top ),
% 11.74/1.98      inference(superposition,[status(thm)],[c_1077,c_828]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_16,plain,
% 11.74/1.98      ( v1_relat_1(sK1) = iProver_top ),
% 11.74/1.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_14,negated_conjecture,
% 11.74/1.98      ( v1_funct_1(sK1) ),
% 11.74/1.98      inference(cnf_transformation,[],[f37]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_17,plain,
% 11.74/1.98      ( v1_funct_1(sK1) = iProver_top ),
% 11.74/1.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_3966,plain,
% 11.74/1.98      ( v1_relat_1(X0_41) != iProver_top
% 11.74/1.98      | k1_relat_1(k7_relat_1(sK1,X0_42)) != k1_relat_1(X0_41)
% 11.74/1.98      | k7_relat_1(sK1,X0_42) = X0_41
% 11.74/1.98      | r2_hidden(sK0(X0_41,sK1),k1_relat_1(X0_41)) = iProver_top
% 11.74/1.98      | v1_funct_1(X0_41) != iProver_top ),
% 11.74/1.98      inference(global_propositional_subsumption,
% 11.74/1.98                [status(thm)],
% 11.74/1.98                [c_1308,c_16,c_17]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_3967,plain,
% 11.74/1.98      ( k1_relat_1(k7_relat_1(sK1,X0_42)) != k1_relat_1(X0_41)
% 11.74/1.98      | k7_relat_1(sK1,X0_42) = X0_41
% 11.74/1.98      | r2_hidden(sK0(X0_41,sK1),k1_relat_1(X0_41)) = iProver_top
% 11.74/1.98      | v1_funct_1(X0_41) != iProver_top
% 11.74/1.98      | v1_relat_1(X0_41) != iProver_top ),
% 11.74/1.98      inference(renaming,[status(thm)],[c_3966]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_3977,plain,
% 11.74/1.98      ( k1_relat_1(k7_relat_1(sK1,X0_42)) != sK3
% 11.74/1.98      | k7_relat_1(sK1,X0_42) = k7_relat_1(sK2,sK3)
% 11.74/1.98      | r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),k1_relat_1(k7_relat_1(sK2,sK3))) = iProver_top
% 11.74/1.98      | v1_funct_1(k7_relat_1(sK2,sK3)) != iProver_top
% 11.74/1.98      | v1_relat_1(k7_relat_1(sK2,sK3)) != iProver_top ),
% 11.74/1.98      inference(superposition,[status(thm)],[c_1393,c_3967]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_4032,plain,
% 11.74/1.98      ( k1_relat_1(k7_relat_1(sK1,X0_42)) != sK3
% 11.74/1.98      | k7_relat_1(sK1,X0_42) = k7_relat_1(sK2,sK3)
% 11.74/1.98      | r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),sK3) = iProver_top
% 11.74/1.98      | v1_funct_1(k7_relat_1(sK2,sK3)) != iProver_top
% 11.74/1.98      | v1_relat_1(k7_relat_1(sK2,sK3)) != iProver_top ),
% 11.74/1.98      inference(light_normalisation,[status(thm)],[c_3977,c_1393]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_4075,plain,
% 11.74/1.98      ( k1_relat_1(k7_relat_1(sK1,sK3)) != sK3
% 11.74/1.98      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)
% 11.74/1.98      | r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),sK3) = iProver_top
% 11.74/1.98      | v1_funct_1(k7_relat_1(sK2,sK3)) != iProver_top
% 11.74/1.98      | v1_relat_1(k7_relat_1(sK2,sK3)) != iProver_top ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_4032]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_11,negated_conjecture,
% 11.74/1.98      ( r1_tarski(sK3,k1_relat_1(sK1)) ),
% 11.74/1.98      inference(cnf_transformation,[],[f40]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_180,plain,
% 11.74/1.98      ( ~ v1_relat_1(X0)
% 11.74/1.98      | k1_relat_1(X0) != k1_relat_1(sK1)
% 11.74/1.98      | k1_relat_1(k7_relat_1(X0,X1)) = X1
% 11.74/1.98      | sK3 != X1 ),
% 11.74/1.98      inference(resolution_lifted,[status(thm)],[c_1,c_11]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_181,plain,
% 11.74/1.98      ( ~ v1_relat_1(X0)
% 11.74/1.98      | k1_relat_1(X0) != k1_relat_1(sK1)
% 11.74/1.98      | k1_relat_1(k7_relat_1(X0,sK3)) = sK3 ),
% 11.74/1.98      inference(unflattening,[status(thm)],[c_180]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_525,plain,
% 11.74/1.98      ( ~ v1_relat_1(X0_41)
% 11.74/1.98      | k1_relat_1(X0_41) != k1_relat_1(sK1)
% 11.74/1.98      | k1_relat_1(k7_relat_1(X0_41,sK3)) = sK3 ),
% 11.74/1.98      inference(subtyping,[status(esa)],[c_181]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_837,plain,
% 11.74/1.98      ( k1_relat_1(X0_41) != k1_relat_1(sK1)
% 11.74/1.98      | k1_relat_1(k7_relat_1(X0_41,sK3)) = sK3
% 11.74/1.98      | v1_relat_1(X0_41) != iProver_top ),
% 11.74/1.98      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1316,plain,
% 11.74/1.98      ( k1_relat_1(k7_relat_1(sK1,sK3)) = sK3
% 11.74/1.98      | v1_relat_1(sK1) != iProver_top ),
% 11.74/1.98      inference(equality_resolution,[status(thm)],[c_837]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_549,plain,
% 11.74/1.98      ( k1_relat_1(X0_41) = k1_relat_1(X1_41) | X0_41 != X1_41 ),
% 11.74/1.98      theory(equality) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_556,plain,
% 11.74/1.98      ( k1_relat_1(sK1) = k1_relat_1(sK1) | sK1 != sK1 ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_549]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_541,plain,( X0_41 = X0_41 ),theory(equality) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_563,plain,
% 11.74/1.98      ( sK1 = sK1 ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_541]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_597,plain,
% 11.74/1.98      ( ~ v1_relat_1(sK1)
% 11.74/1.98      | k1_relat_1(k7_relat_1(sK1,sK3)) = sK3
% 11.74/1.98      | k1_relat_1(sK1) != k1_relat_1(sK1) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_525]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1443,plain,
% 11.74/1.98      ( k1_relat_1(k7_relat_1(sK1,sK3)) = sK3 ),
% 11.74/1.98      inference(global_propositional_subsumption,
% 11.74/1.98                [status(thm)],
% 11.74/1.98                [c_1316,c_15,c_556,c_563,c_597]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_6,plain,
% 11.74/1.98      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
% 11.74/1.98      | ~ v1_funct_1(X1)
% 11.74/1.98      | ~ v1_relat_1(X1)
% 11.74/1.98      | k1_funct_1(k7_relat_1(X1,X2),X0) = k1_funct_1(X1,X0) ),
% 11.74/1.98      inference(cnf_transformation,[],[f35]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_534,plain,
% 11.74/1.98      ( ~ r2_hidden(X0_43,k1_relat_1(k7_relat_1(X0_41,X0_42)))
% 11.74/1.98      | ~ v1_funct_1(X0_41)
% 11.74/1.98      | ~ v1_relat_1(X0_41)
% 11.74/1.98      | k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43) = k1_funct_1(X0_41,X0_43) ),
% 11.74/1.98      inference(subtyping,[status(esa)],[c_6]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_829,plain,
% 11.74/1.98      ( k1_funct_1(k7_relat_1(X0_41,X0_42),X0_43) = k1_funct_1(X0_41,X0_43)
% 11.74/1.98      | r2_hidden(X0_43,k1_relat_1(k7_relat_1(X0_41,X0_42))) != iProver_top
% 11.74/1.98      | v1_funct_1(X0_41) != iProver_top
% 11.74/1.98      | v1_relat_1(X0_41) != iProver_top ),
% 11.74/1.98      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1449,plain,
% 11.74/1.98      ( k1_funct_1(k7_relat_1(sK1,sK3),X0_43) = k1_funct_1(sK1,X0_43)
% 11.74/1.98      | r2_hidden(X0_43,sK3) != iProver_top
% 11.74/1.98      | v1_funct_1(sK1) != iProver_top
% 11.74/1.98      | v1_relat_1(sK1) != iProver_top ),
% 11.74/1.98      inference(superposition,[status(thm)],[c_1443,c_829]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_2848,plain,
% 11.74/1.98      ( k1_funct_1(k7_relat_1(sK1,sK3),X0_43) = k1_funct_1(sK1,X0_43)
% 11.74/1.98      | r2_hidden(X0_43,sK3) != iProver_top ),
% 11.74/1.98      inference(global_propositional_subsumption,
% 11.74/1.98                [status(thm)],
% 11.74/1.98                [c_1449,c_16,c_17]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_2850,plain,
% 11.74/1.98      ( ~ r2_hidden(X0_43,sK3)
% 11.74/1.98      | k1_funct_1(k7_relat_1(sK1,sK3),X0_43) = k1_funct_1(sK1,X0_43) ),
% 11.74/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_2848]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_2852,plain,
% 11.74/1.98      ( ~ r2_hidden(sK4,sK3)
% 11.74/1.98      | k1_funct_1(k7_relat_1(sK1,sK3),sK4) = k1_funct_1(sK1,sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_2850]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1399,plain,
% 11.74/1.98      ( k1_funct_1(k7_relat_1(sK2,sK3),X0_43) = k1_funct_1(sK2,X0_43)
% 11.74/1.98      | r2_hidden(X0_43,sK3) != iProver_top
% 11.74/1.98      | v1_funct_1(sK2) != iProver_top
% 11.74/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.74/1.98      inference(superposition,[status(thm)],[c_1393,c_829]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_12,negated_conjecture,
% 11.74/1.98      ( v1_funct_1(sK2) ),
% 11.74/1.98      inference(cnf_transformation,[],[f39]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_19,plain,
% 11.74/1.98      ( v1_funct_1(sK2) = iProver_top ),
% 11.74/1.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_2839,plain,
% 11.74/1.98      ( k1_funct_1(k7_relat_1(sK2,sK3),X0_43) = k1_funct_1(sK2,X0_43)
% 11.74/1.98      | r2_hidden(X0_43,sK3) != iProver_top ),
% 11.74/1.98      inference(global_propositional_subsumption,
% 11.74/1.98                [status(thm)],
% 11.74/1.98                [c_1399,c_18,c_19]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_2841,plain,
% 11.74/1.98      ( ~ r2_hidden(X0_43,sK3)
% 11.74/1.98      | k1_funct_1(k7_relat_1(sK2,sK3),X0_43) = k1_funct_1(sK2,X0_43) ),
% 11.74/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_2839]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_2843,plain,
% 11.74/1.98      ( ~ r2_hidden(sK4,sK3)
% 11.74/1.98      | k1_funct_1(k7_relat_1(sK2,sK3),sK4) = k1_funct_1(sK2,sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_2841]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_546,plain,
% 11.74/1.98      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 11.74/1.98      theory(equality) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1005,plain,
% 11.74/1.98      ( X0_42 != X1_42
% 11.74/1.98      | k1_relat_1(X0_41) != X1_42
% 11.74/1.98      | k1_relat_1(X0_41) = X0_42 ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_546]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1069,plain,
% 11.74/1.98      ( X0_42 != X1_42
% 11.74/1.98      | k1_relat_1(k7_relat_1(X0_41,sK3)) != X1_42
% 11.74/1.98      | k1_relat_1(k7_relat_1(X0_41,sK3)) = X0_42 ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_1005]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1302,plain,
% 11.74/1.98      ( k1_relat_1(k7_relat_1(X0_41,sK3)) != X0_42
% 11.74/1.98      | k1_relat_1(k7_relat_1(X1_41,sK3)) != X0_42
% 11.74/1.98      | k1_relat_1(k7_relat_1(X1_41,sK3)) = k1_relat_1(k7_relat_1(X0_41,sK3)) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_1069]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_2624,plain,
% 11.74/1.98      ( k1_relat_1(k7_relat_1(sK2,sK3)) != X0_42
% 11.74/1.98      | k1_relat_1(k7_relat_1(sK2,sK3)) = k1_relat_1(k7_relat_1(sK1,sK3))
% 11.74/1.98      | k1_relat_1(k7_relat_1(sK1,sK3)) != X0_42 ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_1302]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_2625,plain,
% 11.74/1.98      ( k1_relat_1(k7_relat_1(sK2,sK3)) = k1_relat_1(k7_relat_1(sK1,sK3))
% 11.74/1.98      | k1_relat_1(k7_relat_1(sK2,sK3)) != sK3
% 11.74/1.98      | k1_relat_1(k7_relat_1(sK1,sK3)) != sK3 ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_2624]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_974,plain,
% 11.74/1.98      ( k3_xboole_0(k1_relat_1(X0_41),X0_42) != X1_42
% 11.74/1.98      | k3_xboole_0(k1_relat_1(X0_41),X0_42) = k1_relat_1(X1_41)
% 11.74/1.98      | k1_relat_1(X1_41) != X1_42 ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_546]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1006,plain,
% 11.74/1.98      ( k3_xboole_0(k1_relat_1(X0_41),X0_42) != k1_relat_1(X1_41)
% 11.74/1.98      | k3_xboole_0(k1_relat_1(X0_41),X0_42) = k1_relat_1(X2_41)
% 11.74/1.98      | k1_relat_1(X2_41) != k1_relat_1(X1_41) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_974]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1062,plain,
% 11.74/1.98      ( k3_xboole_0(k1_relat_1(X0_41),X0_42) = k1_relat_1(X1_41)
% 11.74/1.98      | k3_xboole_0(k1_relat_1(X0_41),X0_42) != k1_relat_1(k7_relat_1(X0_41,X0_42))
% 11.74/1.98      | k1_relat_1(X1_41) != k1_relat_1(k7_relat_1(X0_41,X0_42)) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_1006]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1191,plain,
% 11.74/1.98      ( k3_xboole_0(k1_relat_1(X0_41),X0_42) != k1_relat_1(k7_relat_1(X0_41,X0_42))
% 11.74/1.98      | k3_xboole_0(k1_relat_1(X0_41),X0_42) = k1_relat_1(k7_relat_1(X1_41,sK3))
% 11.74/1.98      | k1_relat_1(k7_relat_1(X1_41,sK3)) != k1_relat_1(k7_relat_1(X0_41,X0_42)) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_1062]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_2013,plain,
% 11.74/1.98      ( k3_xboole_0(k1_relat_1(sK1),sK3) = k1_relat_1(k7_relat_1(sK2,sK3))
% 11.74/1.98      | k3_xboole_0(k1_relat_1(sK1),sK3) != k1_relat_1(k7_relat_1(sK1,sK3))
% 11.74/1.98      | k1_relat_1(k7_relat_1(sK2,sK3)) != k1_relat_1(k7_relat_1(sK1,sK3)) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_1191]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_3,plain,
% 11.74/1.98      ( ~ v1_funct_1(X0)
% 11.74/1.98      | ~ v1_relat_1(X0)
% 11.74/1.98      | v1_relat_1(k7_relat_1(X0,X1)) ),
% 11.74/1.98      inference(cnf_transformation,[],[f31]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_537,plain,
% 11.74/1.98      ( ~ v1_funct_1(X0_41)
% 11.74/1.98      | ~ v1_relat_1(X0_41)
% 11.74/1.98      | v1_relat_1(k7_relat_1(X0_41,X0_42)) ),
% 11.74/1.98      inference(subtyping,[status(esa)],[c_3]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1513,plain,
% 11.74/1.98      ( ~ v1_funct_1(sK2)
% 11.74/1.98      | v1_relat_1(k7_relat_1(sK2,sK3))
% 11.74/1.98      | ~ v1_relat_1(sK2) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_537]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1514,plain,
% 11.74/1.98      ( v1_funct_1(sK2) != iProver_top
% 11.74/1.98      | v1_relat_1(k7_relat_1(sK2,sK3)) = iProver_top
% 11.74/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.74/1.98      inference(predicate_to_equality,[status(thm)],[c_1513]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_2,plain,
% 11.74/1.98      ( ~ v1_funct_1(X0)
% 11.74/1.98      | v1_funct_1(k7_relat_1(X0,X1))
% 11.74/1.98      | ~ v1_relat_1(X0) ),
% 11.74/1.98      inference(cnf_transformation,[],[f32]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_538,plain,
% 11.74/1.98      ( ~ v1_funct_1(X0_41)
% 11.74/1.98      | v1_funct_1(k7_relat_1(X0_41,X0_42))
% 11.74/1.98      | ~ v1_relat_1(X0_41) ),
% 11.74/1.98      inference(subtyping,[status(esa)],[c_2]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1207,plain,
% 11.74/1.98      ( v1_funct_1(k7_relat_1(sK2,sK3))
% 11.74/1.98      | ~ v1_funct_1(sK2)
% 11.74/1.98      | ~ v1_relat_1(sK2) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_538]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1208,plain,
% 11.74/1.98      ( v1_funct_1(k7_relat_1(sK2,sK3)) = iProver_top
% 11.74/1.98      | v1_funct_1(sK2) != iProver_top
% 11.74/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.74/1.98      inference(predicate_to_equality,[status(thm)],[c_1207]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1194,plain,
% 11.74/1.98      ( ~ r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),k1_relat_1(k7_relat_1(sK2,sK3)))
% 11.74/1.98      | ~ v1_funct_1(sK2)
% 11.74/1.98      | ~ v1_relat_1(sK2)
% 11.74/1.98      | k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1)) = k1_funct_1(sK2,sK0(k7_relat_1(sK2,sK3),sK1)) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_534]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_4,plain,
% 11.74/1.98      ( ~ v1_funct_1(X0)
% 11.74/1.98      | ~ v1_funct_1(X1)
% 11.74/1.98      | ~ v1_relat_1(X0)
% 11.74/1.98      | ~ v1_relat_1(X1)
% 11.74/1.98      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
% 11.74/1.98      | k3_xboole_0(k1_relat_1(X1),X2) != k1_relat_1(X0)
% 11.74/1.98      | k7_relat_1(X1,X2) = X0 ),
% 11.74/1.98      inference(cnf_transformation,[],[f34]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_536,plain,
% 11.74/1.98      ( ~ v1_funct_1(X0_41)
% 11.74/1.98      | ~ v1_funct_1(X1_41)
% 11.74/1.98      | ~ v1_relat_1(X1_41)
% 11.74/1.98      | ~ v1_relat_1(X0_41)
% 11.74/1.98      | k1_funct_1(X1_41,sK0(X0_41,X1_41)) != k1_funct_1(X0_41,sK0(X0_41,X1_41))
% 11.74/1.98      | k3_xboole_0(k1_relat_1(X1_41),X0_42) != k1_relat_1(X0_41)
% 11.74/1.98      | k7_relat_1(X1_41,X0_42) = X0_41 ),
% 11.74/1.98      inference(subtyping,[status(esa)],[c_4]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1049,plain,
% 11.74/1.98      ( ~ v1_funct_1(X0_41)
% 11.74/1.98      | ~ v1_funct_1(k7_relat_1(X1_41,sK3))
% 11.74/1.98      | ~ v1_relat_1(X0_41)
% 11.74/1.98      | ~ v1_relat_1(k7_relat_1(X1_41,sK3))
% 11.74/1.98      | k1_funct_1(X0_41,sK0(k7_relat_1(X1_41,sK3),X0_41)) != k1_funct_1(k7_relat_1(X1_41,sK3),sK0(k7_relat_1(X1_41,sK3),X0_41))
% 11.74/1.98      | k3_xboole_0(k1_relat_1(X0_41),X0_42) != k1_relat_1(k7_relat_1(X1_41,sK3))
% 11.74/1.98      | k7_relat_1(X0_41,X0_42) = k7_relat_1(X1_41,sK3) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_536]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1143,plain,
% 11.74/1.98      ( ~ v1_funct_1(k7_relat_1(sK2,sK3))
% 11.74/1.98      | ~ v1_funct_1(sK1)
% 11.74/1.98      | ~ v1_relat_1(k7_relat_1(sK2,sK3))
% 11.74/1.98      | ~ v1_relat_1(sK1)
% 11.74/1.98      | k1_funct_1(sK1,sK0(k7_relat_1(sK2,sK3),sK1)) != k1_funct_1(k7_relat_1(sK2,sK3),sK0(k7_relat_1(sK2,sK3),sK1))
% 11.74/1.98      | k3_xboole_0(k1_relat_1(sK1),sK3) != k1_relat_1(k7_relat_1(sK2,sK3))
% 11.74/1.98      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_1049]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1050,plain,
% 11.74/1.98      ( r2_hidden(sK0(k7_relat_1(X0_41,sK3),X1_41),k1_relat_1(k7_relat_1(X0_41,sK3)))
% 11.74/1.98      | ~ v1_funct_1(X1_41)
% 11.74/1.98      | ~ v1_funct_1(k7_relat_1(X0_41,sK3))
% 11.74/1.98      | ~ v1_relat_1(X1_41)
% 11.74/1.98      | ~ v1_relat_1(k7_relat_1(X0_41,sK3))
% 11.74/1.98      | k3_xboole_0(k1_relat_1(X1_41),X0_42) != k1_relat_1(k7_relat_1(X0_41,sK3))
% 11.74/1.98      | k7_relat_1(X1_41,X0_42) = k7_relat_1(X0_41,sK3) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_535]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1128,plain,
% 11.74/1.98      ( r2_hidden(sK0(k7_relat_1(sK2,sK3),sK1),k1_relat_1(k7_relat_1(sK2,sK3)))
% 11.74/1.98      | ~ v1_funct_1(k7_relat_1(sK2,sK3))
% 11.74/1.98      | ~ v1_funct_1(sK1)
% 11.74/1.98      | ~ v1_relat_1(k7_relat_1(sK2,sK3))
% 11.74/1.98      | ~ v1_relat_1(sK1)
% 11.74/1.98      | k3_xboole_0(k1_relat_1(sK1),sK3) != k1_relat_1(k7_relat_1(sK2,sK3))
% 11.74/1.98      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_1050]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_544,plain,( X0_44 = X0_44 ),theory(equality) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_1038,plain,
% 11.74/1.98      ( k1_funct_1(sK2,sK4) = k1_funct_1(sK2,sK4) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_544]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_8,negated_conjecture,
% 11.74/1.98      ( r2_hidden(sK4,sK3) | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
% 11.74/1.98      inference(cnf_transformation,[],[f43]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_532,negated_conjecture,
% 11.74/1.98      ( r2_hidden(sK4,sK3) | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
% 11.74/1.98      inference(subtyping,[status(esa)],[c_8]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_7,negated_conjecture,
% 11.74/1.98      ( k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4)
% 11.74/1.98      | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
% 11.74/1.98      inference(cnf_transformation,[],[f44]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_533,negated_conjecture,
% 11.74/1.98      ( k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4)
% 11.74/1.98      | k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
% 11.74/1.98      inference(subtyping,[status(esa)],[c_7]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_568,plain,
% 11.74/1.98      ( ~ v1_relat_1(sK1)
% 11.74/1.98      | k3_xboole_0(k1_relat_1(sK1),sK3) = k1_relat_1(k7_relat_1(sK1,sK3)) ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_539]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_543,plain,( X0_43 = X0_43 ),theory(equality) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_565,plain,
% 11.74/1.98      ( sK4 = sK4 ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_543]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(c_560,plain,
% 11.74/1.98      ( k1_funct_1(sK1,sK4) = k1_funct_1(sK1,sK4)
% 11.74/1.98      | sK4 != sK4
% 11.74/1.98      | sK1 != sK1 ),
% 11.74/1.98      inference(instantiation,[status(thm)],[c_553]) ).
% 11.74/1.98  
% 11.74/1.98  cnf(contradiction,plain,
% 11.74/1.98      ( $false ),
% 11.74/1.98      inference(minisat,
% 11.74/1.98                [status(thm)],
% 11.74/1.98                [c_45018,c_32243,c_21752,c_21746,c_14392,c_8220,c_5793,
% 11.74/1.98                 c_4075,c_2852,c_2843,c_2625,c_2013,c_1514,c_1513,c_1208,
% 11.74/1.98                 c_1207,c_1194,c_1143,c_1128,c_1038,c_1028,c_597,c_532,
% 11.74/1.98                 c_533,c_568,c_565,c_563,c_560,c_556,c_19,c_12,c_18,c_13,
% 11.74/1.98                 c_14,c_15]) ).
% 11.74/1.98  
% 11.74/1.98  
% 11.74/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.74/1.98  
% 11.74/1.98  ------                               Statistics
% 11.74/1.98  
% 11.74/1.98  ------ General
% 11.74/1.98  
% 11.74/1.98  abstr_ref_over_cycles:                  0
% 11.74/1.98  abstr_ref_under_cycles:                 0
% 11.74/1.98  gc_basic_clause_elim:                   0
% 11.74/1.98  forced_gc_time:                         0
% 11.74/1.98  parsing_time:                           0.007
% 11.74/1.98  unif_index_cands_time:                  0.
% 11.74/1.98  unif_index_add_time:                    0.
% 11.74/1.98  orderings_time:                         0.
% 11.74/1.98  out_proof_time:                         0.01
% 11.74/1.98  total_time:                             1.459
% 11.74/1.98  num_of_symbols:                         48
% 11.74/1.98  num_of_terms:                           27181
% 11.74/1.98  
% 11.74/1.98  ------ Preprocessing
% 11.74/1.98  
% 11.74/1.98  num_of_splits:                          0
% 11.74/1.98  num_of_split_atoms:                     0
% 11.74/1.98  num_of_reused_defs:                     0
% 11.74/1.98  num_eq_ax_congr_red:                    9
% 11.74/1.98  num_of_sem_filtered_clauses:            1
% 11.74/1.98  num_of_subtypes:                        4
% 11.74/1.98  monotx_restored_types:                  0
% 11.74/1.98  sat_num_of_epr_types:                   0
% 11.74/1.98  sat_num_of_non_cyclic_types:            0
% 11.74/1.98  sat_guarded_non_collapsed_types:        1
% 11.74/1.98  num_pure_diseq_elim:                    0
% 11.74/1.98  simp_replaced_by:                       0
% 11.74/1.98  res_preprocessed:                       90
% 11.74/1.98  prep_upred:                             0
% 11.74/1.98  prep_unflattend:                        10
% 11.74/1.98  smt_new_axioms:                         0
% 11.74/1.98  pred_elim_cands:                        3
% 11.74/1.98  pred_elim:                              1
% 11.74/1.98  pred_elim_cl:                           1
% 11.74/1.98  pred_elim_cycles:                       3
% 11.74/1.98  merged_defs:                            0
% 11.74/1.98  merged_defs_ncl:                        0
% 11.74/1.98  bin_hyper_res:                          0
% 11.74/1.98  prep_cycles:                            4
% 11.74/1.98  pred_elim_time:                         0.006
% 11.74/1.98  splitting_time:                         0.
% 11.74/1.98  sem_filter_time:                        0.
% 11.74/1.98  monotx_time:                            0.
% 11.74/1.98  subtype_inf_time:                       0.
% 11.74/1.98  
% 11.74/1.98  ------ Problem properties
% 11.74/1.98  
% 11.74/1.98  clauses:                                15
% 11.74/1.98  conjectures:                            7
% 11.74/1.98  epr:                                    4
% 11.74/1.98  horn:                                   13
% 11.74/1.98  ground:                                 6
% 11.74/1.98  unary:                                  4
% 11.74/1.98  binary:                                 3
% 11.74/1.98  lits:                                   43
% 11.74/1.98  lits_eq:                                16
% 11.74/1.98  fd_pure:                                0
% 11.74/1.98  fd_pseudo:                              0
% 11.74/1.98  fd_cond:                                0
% 11.74/1.98  fd_pseudo_cond:                         2
% 11.74/1.98  ac_symbols:                             0
% 11.74/1.98  
% 11.74/1.98  ------ Propositional Solver
% 11.74/1.98  
% 11.74/1.98  prop_solver_calls:                      35
% 11.74/1.98  prop_fast_solver_calls:                 1449
% 11.74/1.98  smt_solver_calls:                       0
% 11.74/1.98  smt_fast_solver_calls:                  0
% 11.74/1.98  prop_num_of_clauses:                    7431
% 11.74/1.98  prop_preprocess_simplified:             8538
% 11.74/1.98  prop_fo_subsumed:                       77
% 11.74/1.98  prop_solver_time:                       0.
% 11.74/1.98  smt_solver_time:                        0.
% 11.74/1.98  smt_fast_solver_time:                   0.
% 11.74/1.98  prop_fast_solver_time:                  0.
% 11.74/1.98  prop_unsat_core_time:                   0.001
% 11.74/1.98  
% 11.74/1.98  ------ QBF
% 11.74/1.98  
% 11.74/1.98  qbf_q_res:                              0
% 11.74/1.98  qbf_num_tautologies:                    0
% 11.74/1.98  qbf_prep_cycles:                        0
% 11.74/1.98  
% 11.74/1.98  ------ BMC1
% 11.74/1.98  
% 11.74/1.98  bmc1_current_bound:                     -1
% 11.74/1.98  bmc1_last_solved_bound:                 -1
% 11.74/1.98  bmc1_unsat_core_size:                   -1
% 11.74/1.98  bmc1_unsat_core_parents_size:           -1
% 11.74/1.98  bmc1_merge_next_fun:                    0
% 11.74/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.74/1.98  
% 11.74/1.98  ------ Instantiation
% 11.74/1.98  
% 11.74/1.98  inst_num_of_clauses:                    1680
% 11.74/1.98  inst_num_in_passive:                    653
% 11.74/1.98  inst_num_in_active:                     1026
% 11.74/1.98  inst_num_in_unprocessed:                0
% 11.74/1.98  inst_num_of_loops:                      1205
% 11.74/1.98  inst_num_of_learning_restarts:          0
% 11.74/1.98  inst_num_moves_active_passive:          169
% 11.74/1.98  inst_lit_activity:                      0
% 11.74/1.98  inst_lit_activity_moves:                0
% 11.74/1.98  inst_num_tautologies:                   0
% 11.74/1.98  inst_num_prop_implied:                  0
% 11.74/1.98  inst_num_existing_simplified:           0
% 11.74/1.98  inst_num_eq_res_simplified:             0
% 11.74/1.98  inst_num_child_elim:                    0
% 11.74/1.98  inst_num_of_dismatching_blockings:      5847
% 11.74/1.98  inst_num_of_non_proper_insts:           6347
% 11.74/1.98  inst_num_of_duplicates:                 0
% 11.74/1.98  inst_inst_num_from_inst_to_res:         0
% 11.74/1.98  inst_dismatching_checking_time:         0.
% 11.74/1.98  
% 11.74/1.98  ------ Resolution
% 11.74/1.98  
% 11.74/1.98  res_num_of_clauses:                     0
% 11.74/1.98  res_num_in_passive:                     0
% 11.74/1.98  res_num_in_active:                      0
% 11.74/1.98  res_num_of_loops:                       94
% 11.74/1.98  res_forward_subset_subsumed:            639
% 11.74/1.98  res_backward_subset_subsumed:           0
% 11.74/1.98  res_forward_subsumed:                   0
% 11.74/1.98  res_backward_subsumed:                  0
% 11.74/1.98  res_forward_subsumption_resolution:     0
% 11.74/1.98  res_backward_subsumption_resolution:    0
% 11.74/1.98  res_clause_to_clause_subsumption:       1852
% 11.74/1.98  res_orphan_elimination:                 0
% 11.74/1.98  res_tautology_del:                      984
% 11.74/1.98  res_num_eq_res_simplified:              0
% 11.74/1.98  res_num_sel_changes:                    0
% 11.74/1.98  res_moves_from_active_to_pass:          0
% 11.74/1.98  
% 11.74/1.98  ------ Superposition
% 11.74/1.98  
% 11.74/1.98  sup_time_total:                         0.
% 11.74/1.98  sup_time_generating:                    0.
% 11.74/1.98  sup_time_sim_full:                      0.
% 11.74/1.98  sup_time_sim_immed:                     0.
% 11.74/1.98  
% 11.74/1.98  sup_num_of_clauses:                     1214
% 11.74/1.98  sup_num_in_active:                      190
% 11.74/1.98  sup_num_in_passive:                     1024
% 11.74/1.98  sup_num_of_loops:                       240
% 11.74/1.98  sup_fw_superposition:                   687
% 11.74/1.98  sup_bw_superposition:                   593
% 11.74/1.98  sup_immediate_simplified:               818
% 11.74/1.98  sup_given_eliminated:                   0
% 11.74/1.98  comparisons_done:                       0
% 11.74/1.98  comparisons_avoided:                    2
% 11.74/1.98  
% 11.74/1.98  ------ Simplifications
% 11.74/1.98  
% 11.74/1.98  
% 11.74/1.98  sim_fw_subset_subsumed:                 1
% 11.74/1.98  sim_bw_subset_subsumed:                 2
% 11.74/1.98  sim_fw_subsumed:                        0
% 11.74/1.98  sim_bw_subsumed:                        0
% 11.74/1.98  sim_fw_subsumption_res:                 0
% 11.74/1.98  sim_bw_subsumption_res:                 0
% 11.74/1.98  sim_tautology_del:                      0
% 11.74/1.98  sim_eq_tautology_del:                   13
% 11.74/1.98  sim_eq_res_simp:                        0
% 11.74/1.98  sim_fw_demodulated:                     160
% 11.74/1.98  sim_bw_demodulated:                     50
% 11.74/1.98  sim_light_normalised:                   663
% 11.74/1.98  sim_joinable_taut:                      0
% 11.74/1.98  sim_joinable_simp:                      0
% 11.74/1.98  sim_ac_normalised:                      0
% 11.74/1.98  sim_smt_subsumption:                    0
% 11.74/1.98  
%------------------------------------------------------------------------------
