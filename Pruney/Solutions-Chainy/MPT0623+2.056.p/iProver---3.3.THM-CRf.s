%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:41 EST 2020

% Result     : Theorem 11.54s
% Output     : CNFRefutation 11.54s
% Verified   : 
% Statistics : Number of formulae       :  158 (10096 expanded)
%              Number of clauses        :  101 (3164 expanded)
%              Number of leaves         :   17 (2637 expanded)
%              Depth                    :   31
%              Number of atoms          :  608 (50184 expanded)
%              Number of equality atoms :  364 (22364 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f13])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( sK6(X0) != X1
        & k1_relat_1(sK6(X0)) = X0
        & k1_relat_1(X1) = X0
        & v1_funct_1(sK6(X0))
        & v1_relat_1(sK6(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( sK5(X0) != X2
            & k1_relat_1(X2) = X0
            & k1_relat_1(sK5(X0)) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(sK5(X0))
        & v1_relat_1(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( sK5(X0) != sK6(X0)
        & k1_relat_1(sK6(X0)) = X0
        & k1_relat_1(sK5(X0)) = X0
        & v1_funct_1(sK6(X0))
        & v1_relat_1(sK6(X0))
        & v1_funct_1(sK5(X0))
        & v1_relat_1(sK5(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f14,f30,f29])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(sK5(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f25,f24,f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | v1_relat_1(sK5(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | v1_funct_1(sK5(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK4(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK4(X0,X1)) = X0
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK4(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK4(X0,X1)) = X0
      & v1_funct_1(sK4(X0,X1))
      & v1_relat_1(sK4(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f27])).

fof(f46,plain,(
    ! [X0,X1] : k1_relat_1(sK4(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f17])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK8)
          | k1_relat_1(X2) != sK9
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK9
        | k1_xboole_0 != sK8 ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK8)
        | k1_relat_1(X2) != sK9
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK9
      | k1_xboole_0 != sK8 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f18,f34])).

fof(f58,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK8)
      | k1_relat_1(X2) != sK9
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    ! [X0,X1] : v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK4(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,X3) != sK1(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | sK5(X0) != sK6(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
            & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f16,f32])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK7(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(sK6(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | v1_relat_1(sK6(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | v1_funct_1(sK6(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,
    ( k1_xboole_0 = sK9
    | k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_14,plain,
    ( k1_relat_1(sK5(X0)) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_703,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2598,plain,
    ( k2_relat_1(sK5(X0)) = X1
    | k1_xboole_0 = X0
    | r2_hidden(sK2(sK5(X0),X1),X0) = iProver_top
    | r2_hidden(sK1(sK5(X0),X1),X1) = iProver_top
    | v1_relat_1(sK5(X0)) != iProver_top
    | v1_funct_1(sK5(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_703])).

cnf(c_18,plain,
    ( v1_relat_1(sK5(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_32,plain,
    ( k1_xboole_0 = X0
    | v1_relat_1(sK5(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( v1_funct_1(sK5(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_35,plain,
    ( k1_xboole_0 = X0
    | v1_funct_1(sK5(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4766,plain,
    ( k2_relat_1(sK5(X0)) = X1
    | k1_xboole_0 = X0
    | r2_hidden(sK2(sK5(X0),X1),X0) = iProver_top
    | r2_hidden(sK1(sK5(X0),X1),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2598,c_32,c_35])).

cnf(c_9,plain,
    ( k1_relat_1(sK4(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(X0),sK8)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) != sK9 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_223,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X2) != sK9
    | k2_relat_1(X2) != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_21])).

cnf(c_224,plain,
    ( r2_hidden(sK0(k2_relat_1(X0),sK8),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) != sK9 ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_690,plain,
    ( k1_relat_1(X0) != sK9
    | r2_hidden(sK0(k2_relat_1(X0),sK8),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_945,plain,
    ( sK9 != X0
    | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK8),k2_relat_1(sK4(X0,X1))) = iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_690])).

cnf(c_11,plain,
    ( v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_47,plain,
    ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_50,plain,
    ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1009,plain,
    ( sK9 != X0
    | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK8),k2_relat_1(sK4(X0,X1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_945,c_47,c_50])).

cnf(c_1017,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(sK9,X0)),sK8),k2_relat_1(sK4(sK9,X0))) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1009])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_700,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK4(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_699,plain,
    ( k1_funct_1(sK4(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2472,plain,
    ( k1_funct_1(sK4(k1_relat_1(X0),X1),sK3(X0,X2)) = X1
    | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_700,c_699])).

cnf(c_10174,plain,
    ( k1_funct_1(sK4(k1_relat_1(sK4(sK9,X0)),X1),sK3(sK4(sK9,X0),sK0(k2_relat_1(sK4(sK9,X0)),sK8))) = X1
    | v1_relat_1(sK4(sK9,X0)) != iProver_top
    | v1_funct_1(sK4(sK9,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1017,c_2472])).

cnf(c_10398,plain,
    ( k1_funct_1(sK4(sK9,X0),sK3(sK4(sK9,X1),sK0(k2_relat_1(sK4(sK9,X1)),sK8))) = X0
    | v1_relat_1(sK4(sK9,X1)) != iProver_top
    | v1_funct_1(sK4(sK9,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10174,c_9])).

cnf(c_698,plain,
    ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_697,plain,
    ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10505,plain,
    ( k1_funct_1(sK4(sK9,X0),sK3(sK4(sK9,X1),sK0(k2_relat_1(sK4(sK9,X1)),sK8))) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10398,c_698,c_697])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_701,plain,
    ( k1_funct_1(X0,sK3(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2271,plain,
    ( k1_funct_1(sK4(sK9,X0),sK3(sK4(sK9,X0),sK0(k2_relat_1(sK4(sK9,X0)),sK8))) = sK0(k2_relat_1(sK4(sK9,X0)),sK8)
    | v1_relat_1(sK4(sK9,X0)) != iProver_top
    | v1_funct_1(sK4(sK9,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1017,c_701])).

cnf(c_2305,plain,
    ( k1_funct_1(sK4(sK9,X0),sK3(sK4(sK9,X0),sK0(k2_relat_1(sK4(sK9,X0)),sK8))) = sK0(k2_relat_1(sK4(sK9,X0)),sK8) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2271,c_698,c_697])).

cnf(c_10507,plain,
    ( sK0(k2_relat_1(sK4(sK9,X0)),sK8) = X0 ),
    inference(demodulation,[status(thm)],[c_10505,c_2305])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_241,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X2) != sK9
    | k2_relat_1(X2) != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_242,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(X0),sK8),sK8)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) != sK9 ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_689,plain,
    ( k1_relat_1(X0) != sK9
    | r2_hidden(sK0(k2_relat_1(X0),sK8),sK8) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_242])).

cnf(c_946,plain,
    ( sK9 != X0
    | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK8),sK8) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_689])).

cnf(c_996,plain,
    ( sK9 != X0
    | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK8),sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_946,c_47,c_50])).

cnf(c_1004,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(sK9,X0)),sK8),sK8) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_996])).

cnf(c_11622,plain,
    ( r2_hidden(X0,sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10507,c_1004])).

cnf(c_11857,plain,
    ( k2_relat_1(sK5(sK8)) = X0
    | sK8 = k1_xboole_0
    | r2_hidden(sK1(sK5(sK8),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4766,c_11622])).

cnf(c_17640,plain,
    ( k1_funct_1(sK4(X0,X1),sK1(sK5(sK8),X0)) = X1
    | k2_relat_1(sK5(sK8)) = X0
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11857,c_699])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK1(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | sK1(X1,X2) != k1_funct_1(X1,X0)
    | k2_relat_1(X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_705,plain,
    ( sK1(X0,X1) != k1_funct_1(X0,X2)
    | k2_relat_1(X0) = X1
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_45527,plain,
    ( sK1(sK4(X0,X1),X2) != X1
    | k2_relat_1(sK4(X0,X1)) = X2
    | k2_relat_1(sK5(sK8)) = X0
    | sK8 = k1_xboole_0
    | r2_hidden(sK1(sK4(X0,X1),X2),X2) != iProver_top
    | r2_hidden(sK1(sK5(sK8),X0),k1_relat_1(sK4(X0,X1))) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17640,c_705])).

cnf(c_45550,plain,
    ( sK1(sK4(X0,X1),X2) != X1
    | k2_relat_1(sK4(X0,X1)) = X2
    | k2_relat_1(sK5(sK8)) = X0
    | sK8 = k1_xboole_0
    | r2_hidden(sK1(sK4(X0,X1),X2),X2) != iProver_top
    | r2_hidden(sK1(sK5(sK8),X0),X0) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_45527,c_9])).

cnf(c_12,plain,
    ( sK6(X0) != sK5(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_914,plain,
    ( sK6(sK8) != sK5(sK8)
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_386,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4486,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_386])).

cnf(c_387,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3057,plain,
    ( X0 != X1
    | sK8 != X1
    | sK8 = X0 ),
    inference(instantiation,[status(thm)],[c_387])).

cnf(c_8262,plain,
    ( X0 != sK8
    | sK8 = X0
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_3057])).

cnf(c_8263,plain,
    ( sK8 != sK8
    | sK8 = k1_xboole_0
    | k1_xboole_0 != sK8 ),
    inference(instantiation,[status(thm)],[c_8262])).

cnf(c_20,plain,
    ( r2_hidden(sK7(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_691,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK7(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1145,plain,
    ( sK4(X0,X1) = X2
    | k1_relat_1(X2) != X0
    | r2_hidden(sK7(X2,sK4(X0,X1)),k1_relat_1(X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_691])).

cnf(c_4653,plain,
    ( v1_funct_1(X2) != iProver_top
    | sK4(X0,X1) = X2
    | k1_relat_1(X2) != X0
    | r2_hidden(sK7(X2,sK4(X0,X1)),k1_relat_1(X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1145,c_47,c_50])).

cnf(c_4654,plain,
    ( sK4(X0,X1) = X2
    | k1_relat_1(X2) != X0
    | r2_hidden(sK7(X2,sK4(X0,X1)),k1_relat_1(X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4653])).

cnf(c_4667,plain,
    ( sK4(k1_relat_1(X0),X1) = X0
    | r2_hidden(sK7(X0,sK4(k1_relat_1(X0),X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4654])).

cnf(c_49628,plain,
    ( sK4(k1_relat_1(sK5(X0)),X1) = sK5(X0)
    | k1_xboole_0 = X0
    | r2_hidden(sK7(sK5(X0),sK4(X0,X1)),X0) = iProver_top
    | v1_relat_1(sK5(X0)) != iProver_top
    | v1_funct_1(sK5(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_4667])).

cnf(c_50194,plain,
    ( sK4(k1_relat_1(sK5(X0)),X1) = sK5(X0)
    | k1_xboole_0 = X0
    | r2_hidden(sK7(sK5(X0),sK4(X0,X1)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49628,c_32,c_35])).

cnf(c_50222,plain,
    ( sK4(k1_relat_1(sK5(sK8)),X0) = sK5(sK8)
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_50194,c_11622])).

cnf(c_50767,plain,
    ( sK4(sK8,X0) = sK5(sK8)
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14,c_50222])).

cnf(c_13,plain,
    ( k1_relat_1(sK6(X0)) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_49627,plain,
    ( sK4(k1_relat_1(sK6(X0)),X1) = sK6(X0)
    | k1_xboole_0 = X0
    | r2_hidden(sK7(sK6(X0),sK4(X0,X1)),X0) = iProver_top
    | v1_relat_1(sK6(X0)) != iProver_top
    | v1_funct_1(sK6(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_4667])).

cnf(c_16,plain,
    ( v1_relat_1(sK6(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_38,plain,
    ( k1_xboole_0 = X0
    | v1_relat_1(sK6(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( v1_funct_1(sK6(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_41,plain,
    ( k1_xboole_0 = X0
    | v1_funct_1(sK6(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_49894,plain,
    ( sK4(k1_relat_1(sK6(X0)),X1) = sK6(X0)
    | k1_xboole_0 = X0
    | r2_hidden(sK7(sK6(X0),sK4(X0,X1)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49627,c_38,c_41])).

cnf(c_49922,plain,
    ( sK4(k1_relat_1(sK6(sK8)),X0) = sK6(sK8)
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_49894,c_11622])).

cnf(c_50668,plain,
    ( sK4(sK8,X0) = sK6(sK8)
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_49922])).

cnf(c_51769,plain,
    ( sK6(sK8) = sK5(sK8)
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_50767,c_50668])).

cnf(c_52445,plain,
    ( sK8 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_45550,c_914,c_4486,c_8263,c_51769])).

cnf(c_2596,plain,
    ( k2_relat_1(sK4(X0,X1)) = X2
    | r2_hidden(sK2(sK4(X0,X1),X2),X0) = iProver_top
    | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_703])).

cnf(c_5224,plain,
    ( k2_relat_1(sK4(X0,X1)) = X2
    | r2_hidden(sK2(sK4(X0,X1),X2),X0) = iProver_top
    | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2596,c_47,c_50])).

cnf(c_11850,plain,
    ( k2_relat_1(sK4(X0,X1)) = sK8
    | r2_hidden(sK2(sK4(X0,X1),sK8),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5224,c_11622])).

cnf(c_15619,plain,
    ( k2_relat_1(sK4(sK8,X0)) = sK8 ),
    inference(superposition,[status(thm)],[c_11850,c_11622])).

cnf(c_52568,plain,
    ( k2_relat_1(sK4(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_52445,c_15619])).

cnf(c_52583,plain,
    ( sK0(k2_relat_1(sK4(sK9,X0)),k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_52445,c_10507])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 = sK9
    | k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_52606,plain,
    ( sK9 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_52445,c_22])).

cnf(c_52607,plain,
    ( sK9 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_52606])).

cnf(c_52642,plain,
    ( sK0(k2_relat_1(sK4(k1_xboole_0,X0)),k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_52583,c_52607])).

cnf(c_52652,plain,
    ( sK0(k1_xboole_0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_52568,c_52642])).

cnf(c_52602,plain,
    ( sK9 != X0
    | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),k1_xboole_0),k2_relat_1(sK4(X0,X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_52445,c_1009])).

cnf(c_52633,plain,
    ( k1_xboole_0 != X0
    | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),k1_xboole_0),k2_relat_1(sK4(X0,X1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_52602,c_52607])).

cnf(c_52656,plain,
    ( k1_xboole_0 != X0
    | r2_hidden(sK0(k2_relat_1(sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0),k2_relat_1(sK0(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_52652,c_52633])).

cnf(c_52658,plain,
    ( k2_relat_1(sK0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_52652,c_52568])).

cnf(c_52670,plain,
    ( k1_xboole_0 != X0
    | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_52656,c_52658])).

cnf(c_52582,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_52445,c_11622])).

cnf(c_52673,plain,
    ( k1_xboole_0 != X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_52670,c_52582])).

cnf(c_52777,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_52673])).

cnf(c_401,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_386])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52777,c_401])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:42:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 11.54/2.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.54/2.02  
% 11.54/2.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.54/2.02  
% 11.54/2.02  ------  iProver source info
% 11.54/2.02  
% 11.54/2.02  git: date: 2020-06-30 10:37:57 +0100
% 11.54/2.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.54/2.02  git: non_committed_changes: false
% 11.54/2.02  git: last_make_outside_of_git: false
% 11.54/2.02  
% 11.54/2.02  ------ 
% 11.54/2.02  
% 11.54/2.02  ------ Input Options
% 11.54/2.02  
% 11.54/2.02  --out_options                           all
% 11.54/2.02  --tptp_safe_out                         true
% 11.54/2.02  --problem_path                          ""
% 11.54/2.02  --include_path                          ""
% 11.54/2.02  --clausifier                            res/vclausify_rel
% 11.54/2.02  --clausifier_options                    --mode clausify
% 11.54/2.02  --stdin                                 false
% 11.54/2.02  --stats_out                             all
% 11.54/2.02  
% 11.54/2.02  ------ General Options
% 11.54/2.02  
% 11.54/2.02  --fof                                   false
% 11.54/2.02  --time_out_real                         305.
% 11.54/2.02  --time_out_virtual                      -1.
% 11.54/2.02  --symbol_type_check                     false
% 11.54/2.02  --clausify_out                          false
% 11.54/2.02  --sig_cnt_out                           false
% 11.54/2.02  --trig_cnt_out                          false
% 11.54/2.02  --trig_cnt_out_tolerance                1.
% 11.54/2.02  --trig_cnt_out_sk_spl                   false
% 11.54/2.02  --abstr_cl_out                          false
% 11.54/2.02  
% 11.54/2.02  ------ Global Options
% 11.54/2.02  
% 11.54/2.02  --schedule                              default
% 11.54/2.02  --add_important_lit                     false
% 11.54/2.02  --prop_solver_per_cl                    1000
% 11.54/2.02  --min_unsat_core                        false
% 11.54/2.02  --soft_assumptions                      false
% 11.54/2.02  --soft_lemma_size                       3
% 11.54/2.02  --prop_impl_unit_size                   0
% 11.54/2.02  --prop_impl_unit                        []
% 11.54/2.02  --share_sel_clauses                     true
% 11.54/2.02  --reset_solvers                         false
% 11.54/2.02  --bc_imp_inh                            [conj_cone]
% 11.54/2.02  --conj_cone_tolerance                   3.
% 11.54/2.02  --extra_neg_conj                        none
% 11.54/2.02  --large_theory_mode                     true
% 11.54/2.02  --prolific_symb_bound                   200
% 11.54/2.02  --lt_threshold                          2000
% 11.54/2.02  --clause_weak_htbl                      true
% 11.54/2.02  --gc_record_bc_elim                     false
% 11.54/2.02  
% 11.54/2.02  ------ Preprocessing Options
% 11.54/2.02  
% 11.54/2.02  --preprocessing_flag                    true
% 11.54/2.02  --time_out_prep_mult                    0.1
% 11.54/2.02  --splitting_mode                        input
% 11.54/2.02  --splitting_grd                         true
% 11.54/2.02  --splitting_cvd                         false
% 11.54/2.02  --splitting_cvd_svl                     false
% 11.54/2.02  --splitting_nvd                         32
% 11.54/2.02  --sub_typing                            true
% 11.54/2.02  --prep_gs_sim                           true
% 11.54/2.02  --prep_unflatten                        true
% 11.54/2.02  --prep_res_sim                          true
% 11.54/2.02  --prep_upred                            true
% 11.54/2.02  --prep_sem_filter                       exhaustive
% 11.54/2.02  --prep_sem_filter_out                   false
% 11.54/2.02  --pred_elim                             true
% 11.54/2.02  --res_sim_input                         true
% 11.54/2.02  --eq_ax_congr_red                       true
% 11.54/2.02  --pure_diseq_elim                       true
% 11.54/2.02  --brand_transform                       false
% 11.54/2.02  --non_eq_to_eq                          false
% 11.54/2.02  --prep_def_merge                        true
% 11.54/2.02  --prep_def_merge_prop_impl              false
% 11.54/2.02  --prep_def_merge_mbd                    true
% 11.54/2.02  --prep_def_merge_tr_red                 false
% 11.54/2.02  --prep_def_merge_tr_cl                  false
% 11.54/2.02  --smt_preprocessing                     true
% 11.54/2.02  --smt_ac_axioms                         fast
% 11.54/2.02  --preprocessed_out                      false
% 11.54/2.02  --preprocessed_stats                    false
% 11.54/2.02  
% 11.54/2.02  ------ Abstraction refinement Options
% 11.54/2.02  
% 11.54/2.02  --abstr_ref                             []
% 11.54/2.02  --abstr_ref_prep                        false
% 11.54/2.02  --abstr_ref_until_sat                   false
% 11.54/2.02  --abstr_ref_sig_restrict                funpre
% 11.54/2.02  --abstr_ref_af_restrict_to_split_sk     false
% 11.54/2.02  --abstr_ref_under                       []
% 11.54/2.02  
% 11.54/2.02  ------ SAT Options
% 11.54/2.02  
% 11.54/2.02  --sat_mode                              false
% 11.54/2.02  --sat_fm_restart_options                ""
% 11.54/2.02  --sat_gr_def                            false
% 11.54/2.02  --sat_epr_types                         true
% 11.54/2.02  --sat_non_cyclic_types                  false
% 11.54/2.02  --sat_finite_models                     false
% 11.54/2.02  --sat_fm_lemmas                         false
% 11.54/2.02  --sat_fm_prep                           false
% 11.54/2.02  --sat_fm_uc_incr                        true
% 11.54/2.02  --sat_out_model                         small
% 11.54/2.02  --sat_out_clauses                       false
% 11.54/2.02  
% 11.54/2.02  ------ QBF Options
% 11.54/2.02  
% 11.54/2.02  --qbf_mode                              false
% 11.54/2.02  --qbf_elim_univ                         false
% 11.54/2.02  --qbf_dom_inst                          none
% 11.54/2.02  --qbf_dom_pre_inst                      false
% 11.54/2.02  --qbf_sk_in                             false
% 11.54/2.02  --qbf_pred_elim                         true
% 11.54/2.02  --qbf_split                             512
% 11.54/2.02  
% 11.54/2.02  ------ BMC1 Options
% 11.54/2.02  
% 11.54/2.02  --bmc1_incremental                      false
% 11.54/2.02  --bmc1_axioms                           reachable_all
% 11.54/2.02  --bmc1_min_bound                        0
% 11.54/2.02  --bmc1_max_bound                        -1
% 11.54/2.02  --bmc1_max_bound_default                -1
% 11.54/2.02  --bmc1_symbol_reachability              true
% 11.54/2.02  --bmc1_property_lemmas                  false
% 11.54/2.02  --bmc1_k_induction                      false
% 11.54/2.02  --bmc1_non_equiv_states                 false
% 11.54/2.02  --bmc1_deadlock                         false
% 11.54/2.02  --bmc1_ucm                              false
% 11.54/2.02  --bmc1_add_unsat_core                   none
% 11.54/2.02  --bmc1_unsat_core_children              false
% 11.54/2.02  --bmc1_unsat_core_extrapolate_axioms    false
% 11.54/2.02  --bmc1_out_stat                         full
% 11.54/2.02  --bmc1_ground_init                      false
% 11.54/2.02  --bmc1_pre_inst_next_state              false
% 11.54/2.02  --bmc1_pre_inst_state                   false
% 11.54/2.02  --bmc1_pre_inst_reach_state             false
% 11.54/2.02  --bmc1_out_unsat_core                   false
% 11.54/2.02  --bmc1_aig_witness_out                  false
% 11.54/2.02  --bmc1_verbose                          false
% 11.54/2.02  --bmc1_dump_clauses_tptp                false
% 11.54/2.02  --bmc1_dump_unsat_core_tptp             false
% 11.54/2.02  --bmc1_dump_file                        -
% 11.54/2.02  --bmc1_ucm_expand_uc_limit              128
% 11.54/2.02  --bmc1_ucm_n_expand_iterations          6
% 11.54/2.02  --bmc1_ucm_extend_mode                  1
% 11.54/2.02  --bmc1_ucm_init_mode                    2
% 11.54/2.02  --bmc1_ucm_cone_mode                    none
% 11.54/2.02  --bmc1_ucm_reduced_relation_type        0
% 11.54/2.02  --bmc1_ucm_relax_model                  4
% 11.54/2.02  --bmc1_ucm_full_tr_after_sat            true
% 11.54/2.02  --bmc1_ucm_expand_neg_assumptions       false
% 11.54/2.02  --bmc1_ucm_layered_model                none
% 11.54/2.02  --bmc1_ucm_max_lemma_size               10
% 11.54/2.02  
% 11.54/2.02  ------ AIG Options
% 11.54/2.02  
% 11.54/2.02  --aig_mode                              false
% 11.54/2.02  
% 11.54/2.02  ------ Instantiation Options
% 11.54/2.02  
% 11.54/2.02  --instantiation_flag                    true
% 11.54/2.02  --inst_sos_flag                         false
% 11.54/2.02  --inst_sos_phase                        true
% 11.54/2.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.54/2.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.54/2.02  --inst_lit_sel_side                     num_symb
% 11.54/2.02  --inst_solver_per_active                1400
% 11.54/2.02  --inst_solver_calls_frac                1.
% 11.54/2.02  --inst_passive_queue_type               priority_queues
% 11.54/2.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.54/2.02  --inst_passive_queues_freq              [25;2]
% 11.54/2.02  --inst_dismatching                      true
% 11.54/2.02  --inst_eager_unprocessed_to_passive     true
% 11.54/2.02  --inst_prop_sim_given                   true
% 11.54/2.02  --inst_prop_sim_new                     false
% 11.54/2.02  --inst_subs_new                         false
% 11.54/2.02  --inst_eq_res_simp                      false
% 11.54/2.02  --inst_subs_given                       false
% 11.54/2.02  --inst_orphan_elimination               true
% 11.54/2.02  --inst_learning_loop_flag               true
% 11.54/2.02  --inst_learning_start                   3000
% 11.54/2.02  --inst_learning_factor                  2
% 11.54/2.02  --inst_start_prop_sim_after_learn       3
% 11.54/2.02  --inst_sel_renew                        solver
% 11.54/2.02  --inst_lit_activity_flag                true
% 11.54/2.02  --inst_restr_to_given                   false
% 11.54/2.02  --inst_activity_threshold               500
% 11.54/2.02  --inst_out_proof                        true
% 11.54/2.02  
% 11.54/2.02  ------ Resolution Options
% 11.54/2.02  
% 11.54/2.02  --resolution_flag                       true
% 11.54/2.02  --res_lit_sel                           adaptive
% 11.54/2.02  --res_lit_sel_side                      none
% 11.54/2.02  --res_ordering                          kbo
% 11.54/2.02  --res_to_prop_solver                    active
% 11.54/2.02  --res_prop_simpl_new                    false
% 11.54/2.02  --res_prop_simpl_given                  true
% 11.54/2.02  --res_passive_queue_type                priority_queues
% 11.54/2.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.54/2.02  --res_passive_queues_freq               [15;5]
% 11.54/2.02  --res_forward_subs                      full
% 11.54/2.02  --res_backward_subs                     full
% 11.54/2.02  --res_forward_subs_resolution           true
% 11.54/2.02  --res_backward_subs_resolution          true
% 11.54/2.02  --res_orphan_elimination                true
% 11.54/2.02  --res_time_limit                        2.
% 11.54/2.02  --res_out_proof                         true
% 11.54/2.02  
% 11.54/2.02  ------ Superposition Options
% 11.54/2.02  
% 11.54/2.02  --superposition_flag                    true
% 11.54/2.02  --sup_passive_queue_type                priority_queues
% 11.54/2.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.54/2.02  --sup_passive_queues_freq               [8;1;4]
% 11.54/2.02  --demod_completeness_check              fast
% 11.54/2.02  --demod_use_ground                      true
% 11.54/2.02  --sup_to_prop_solver                    passive
% 11.54/2.02  --sup_prop_simpl_new                    true
% 11.54/2.02  --sup_prop_simpl_given                  true
% 11.54/2.02  --sup_fun_splitting                     false
% 11.54/2.02  --sup_smt_interval                      50000
% 11.54/2.02  
% 11.54/2.02  ------ Superposition Simplification Setup
% 11.54/2.02  
% 11.54/2.02  --sup_indices_passive                   []
% 11.54/2.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.54/2.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.54/2.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.54/2.02  --sup_full_triv                         [TrivRules;PropSubs]
% 11.54/2.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.54/2.02  --sup_full_bw                           [BwDemod]
% 11.54/2.02  --sup_immed_triv                        [TrivRules]
% 11.54/2.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.54/2.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.54/2.02  --sup_immed_bw_main                     []
% 11.54/2.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.54/2.02  --sup_input_triv                        [Unflattening;TrivRules]
% 11.54/2.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.54/2.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.54/2.02  
% 11.54/2.02  ------ Combination Options
% 11.54/2.02  
% 11.54/2.02  --comb_res_mult                         3
% 11.54/2.02  --comb_sup_mult                         2
% 11.54/2.02  --comb_inst_mult                        10
% 11.54/2.02  
% 11.54/2.02  ------ Debug Options
% 11.54/2.02  
% 11.54/2.02  --dbg_backtrace                         false
% 11.54/2.02  --dbg_dump_prop_clauses                 false
% 11.54/2.02  --dbg_dump_prop_clauses_file            -
% 11.54/2.02  --dbg_out_stat                          false
% 11.54/2.02  ------ Parsing...
% 11.54/2.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.54/2.02  
% 11.54/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.54/2.02  
% 11.54/2.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.54/2.02  
% 11.54/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.54/2.02  ------ Proving...
% 11.54/2.02  ------ Problem Properties 
% 11.54/2.02  
% 11.54/2.02  
% 11.54/2.02  clauses                                 22
% 11.54/2.02  conjectures                             1
% 11.54/2.02  EPR                                     1
% 11.54/2.02  Horn                                    13
% 11.54/2.02  unary                                   3
% 11.54/2.02  binary                                  9
% 11.54/2.02  lits                                    71
% 11.54/2.02  lits eq                                 27
% 11.54/2.02  fd_pure                                 0
% 11.54/2.02  fd_pseudo                               0
% 11.54/2.02  fd_cond                                 5
% 11.54/2.02  fd_pseudo_cond                          5
% 11.54/2.02  AC symbols                              0
% 11.54/2.02  
% 11.54/2.02  ------ Schedule dynamic 5 is on 
% 11.54/2.02  
% 11.54/2.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.54/2.02  
% 11.54/2.02  
% 11.54/2.02  ------ 
% 11.54/2.02  Current options:
% 11.54/2.02  ------ 
% 11.54/2.02  
% 11.54/2.02  ------ Input Options
% 11.54/2.02  
% 11.54/2.02  --out_options                           all
% 11.54/2.02  --tptp_safe_out                         true
% 11.54/2.02  --problem_path                          ""
% 11.54/2.02  --include_path                          ""
% 11.54/2.02  --clausifier                            res/vclausify_rel
% 11.54/2.02  --clausifier_options                    --mode clausify
% 11.54/2.02  --stdin                                 false
% 11.54/2.02  --stats_out                             all
% 11.54/2.02  
% 11.54/2.02  ------ General Options
% 11.54/2.02  
% 11.54/2.02  --fof                                   false
% 11.54/2.02  --time_out_real                         305.
% 11.54/2.02  --time_out_virtual                      -1.
% 11.54/2.02  --symbol_type_check                     false
% 11.54/2.02  --clausify_out                          false
% 11.54/2.02  --sig_cnt_out                           false
% 11.54/2.02  --trig_cnt_out                          false
% 11.54/2.02  --trig_cnt_out_tolerance                1.
% 11.54/2.02  --trig_cnt_out_sk_spl                   false
% 11.54/2.02  --abstr_cl_out                          false
% 11.54/2.02  
% 11.54/2.02  ------ Global Options
% 11.54/2.02  
% 11.54/2.02  --schedule                              default
% 11.54/2.02  --add_important_lit                     false
% 11.54/2.02  --prop_solver_per_cl                    1000
% 11.54/2.02  --min_unsat_core                        false
% 11.54/2.02  --soft_assumptions                      false
% 11.54/2.02  --soft_lemma_size                       3
% 11.54/2.02  --prop_impl_unit_size                   0
% 11.54/2.02  --prop_impl_unit                        []
% 11.54/2.02  --share_sel_clauses                     true
% 11.54/2.02  --reset_solvers                         false
% 11.54/2.02  --bc_imp_inh                            [conj_cone]
% 11.54/2.02  --conj_cone_tolerance                   3.
% 11.54/2.02  --extra_neg_conj                        none
% 11.54/2.02  --large_theory_mode                     true
% 11.54/2.02  --prolific_symb_bound                   200
% 11.54/2.02  --lt_threshold                          2000
% 11.54/2.02  --clause_weak_htbl                      true
% 11.54/2.02  --gc_record_bc_elim                     false
% 11.54/2.02  
% 11.54/2.02  ------ Preprocessing Options
% 11.54/2.02  
% 11.54/2.02  --preprocessing_flag                    true
% 11.54/2.02  --time_out_prep_mult                    0.1
% 11.54/2.02  --splitting_mode                        input
% 11.54/2.02  --splitting_grd                         true
% 11.54/2.02  --splitting_cvd                         false
% 11.54/2.02  --splitting_cvd_svl                     false
% 11.54/2.02  --splitting_nvd                         32
% 11.54/2.02  --sub_typing                            true
% 11.54/2.02  --prep_gs_sim                           true
% 11.54/2.02  --prep_unflatten                        true
% 11.54/2.02  --prep_res_sim                          true
% 11.54/2.02  --prep_upred                            true
% 11.54/2.02  --prep_sem_filter                       exhaustive
% 11.54/2.02  --prep_sem_filter_out                   false
% 11.54/2.02  --pred_elim                             true
% 11.54/2.02  --res_sim_input                         true
% 11.54/2.02  --eq_ax_congr_red                       true
% 11.54/2.02  --pure_diseq_elim                       true
% 11.54/2.02  --brand_transform                       false
% 11.54/2.02  --non_eq_to_eq                          false
% 11.54/2.02  --prep_def_merge                        true
% 11.54/2.02  --prep_def_merge_prop_impl              false
% 11.54/2.02  --prep_def_merge_mbd                    true
% 11.54/2.02  --prep_def_merge_tr_red                 false
% 11.54/2.02  --prep_def_merge_tr_cl                  false
% 11.54/2.02  --smt_preprocessing                     true
% 11.54/2.02  --smt_ac_axioms                         fast
% 11.54/2.02  --preprocessed_out                      false
% 11.54/2.02  --preprocessed_stats                    false
% 11.54/2.02  
% 11.54/2.02  ------ Abstraction refinement Options
% 11.54/2.02  
% 11.54/2.02  --abstr_ref                             []
% 11.54/2.02  --abstr_ref_prep                        false
% 11.54/2.02  --abstr_ref_until_sat                   false
% 11.54/2.02  --abstr_ref_sig_restrict                funpre
% 11.54/2.02  --abstr_ref_af_restrict_to_split_sk     false
% 11.54/2.02  --abstr_ref_under                       []
% 11.54/2.02  
% 11.54/2.02  ------ SAT Options
% 11.54/2.02  
% 11.54/2.02  --sat_mode                              false
% 11.54/2.02  --sat_fm_restart_options                ""
% 11.54/2.02  --sat_gr_def                            false
% 11.54/2.02  --sat_epr_types                         true
% 11.54/2.02  --sat_non_cyclic_types                  false
% 11.54/2.02  --sat_finite_models                     false
% 11.54/2.02  --sat_fm_lemmas                         false
% 11.54/2.02  --sat_fm_prep                           false
% 11.54/2.02  --sat_fm_uc_incr                        true
% 11.54/2.02  --sat_out_model                         small
% 11.54/2.02  --sat_out_clauses                       false
% 11.54/2.02  
% 11.54/2.02  ------ QBF Options
% 11.54/2.02  
% 11.54/2.02  --qbf_mode                              false
% 11.54/2.02  --qbf_elim_univ                         false
% 11.54/2.02  --qbf_dom_inst                          none
% 11.54/2.02  --qbf_dom_pre_inst                      false
% 11.54/2.02  --qbf_sk_in                             false
% 11.54/2.02  --qbf_pred_elim                         true
% 11.54/2.02  --qbf_split                             512
% 11.54/2.02  
% 11.54/2.02  ------ BMC1 Options
% 11.54/2.02  
% 11.54/2.02  --bmc1_incremental                      false
% 11.54/2.02  --bmc1_axioms                           reachable_all
% 11.54/2.02  --bmc1_min_bound                        0
% 11.54/2.02  --bmc1_max_bound                        -1
% 11.54/2.02  --bmc1_max_bound_default                -1
% 11.54/2.02  --bmc1_symbol_reachability              true
% 11.54/2.02  --bmc1_property_lemmas                  false
% 11.54/2.02  --bmc1_k_induction                      false
% 11.54/2.02  --bmc1_non_equiv_states                 false
% 11.54/2.02  --bmc1_deadlock                         false
% 11.54/2.02  --bmc1_ucm                              false
% 11.54/2.02  --bmc1_add_unsat_core                   none
% 11.54/2.02  --bmc1_unsat_core_children              false
% 11.54/2.02  --bmc1_unsat_core_extrapolate_axioms    false
% 11.54/2.02  --bmc1_out_stat                         full
% 11.54/2.02  --bmc1_ground_init                      false
% 11.54/2.02  --bmc1_pre_inst_next_state              false
% 11.54/2.02  --bmc1_pre_inst_state                   false
% 11.54/2.02  --bmc1_pre_inst_reach_state             false
% 11.54/2.02  --bmc1_out_unsat_core                   false
% 11.54/2.02  --bmc1_aig_witness_out                  false
% 11.54/2.02  --bmc1_verbose                          false
% 11.54/2.02  --bmc1_dump_clauses_tptp                false
% 11.54/2.02  --bmc1_dump_unsat_core_tptp             false
% 11.54/2.02  --bmc1_dump_file                        -
% 11.54/2.02  --bmc1_ucm_expand_uc_limit              128
% 11.54/2.02  --bmc1_ucm_n_expand_iterations          6
% 11.54/2.02  --bmc1_ucm_extend_mode                  1
% 11.54/2.02  --bmc1_ucm_init_mode                    2
% 11.54/2.02  --bmc1_ucm_cone_mode                    none
% 11.54/2.02  --bmc1_ucm_reduced_relation_type        0
% 11.54/2.02  --bmc1_ucm_relax_model                  4
% 11.54/2.02  --bmc1_ucm_full_tr_after_sat            true
% 11.54/2.02  --bmc1_ucm_expand_neg_assumptions       false
% 11.54/2.02  --bmc1_ucm_layered_model                none
% 11.54/2.02  --bmc1_ucm_max_lemma_size               10
% 11.54/2.02  
% 11.54/2.02  ------ AIG Options
% 11.54/2.02  
% 11.54/2.02  --aig_mode                              false
% 11.54/2.02  
% 11.54/2.02  ------ Instantiation Options
% 11.54/2.02  
% 11.54/2.02  --instantiation_flag                    true
% 11.54/2.02  --inst_sos_flag                         false
% 11.54/2.02  --inst_sos_phase                        true
% 11.54/2.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.54/2.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.54/2.02  --inst_lit_sel_side                     none
% 11.54/2.02  --inst_solver_per_active                1400
% 11.54/2.02  --inst_solver_calls_frac                1.
% 11.54/2.02  --inst_passive_queue_type               priority_queues
% 11.54/2.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.54/2.02  --inst_passive_queues_freq              [25;2]
% 11.54/2.02  --inst_dismatching                      true
% 11.54/2.02  --inst_eager_unprocessed_to_passive     true
% 11.54/2.02  --inst_prop_sim_given                   true
% 11.54/2.02  --inst_prop_sim_new                     false
% 11.54/2.02  --inst_subs_new                         false
% 11.54/2.02  --inst_eq_res_simp                      false
% 11.54/2.02  --inst_subs_given                       false
% 11.54/2.02  --inst_orphan_elimination               true
% 11.54/2.02  --inst_learning_loop_flag               true
% 11.54/2.02  --inst_learning_start                   3000
% 11.54/2.02  --inst_learning_factor                  2
% 11.54/2.02  --inst_start_prop_sim_after_learn       3
% 11.54/2.02  --inst_sel_renew                        solver
% 11.54/2.02  --inst_lit_activity_flag                true
% 11.54/2.02  --inst_restr_to_given                   false
% 11.54/2.02  --inst_activity_threshold               500
% 11.54/2.02  --inst_out_proof                        true
% 11.54/2.02  
% 11.54/2.02  ------ Resolution Options
% 11.54/2.02  
% 11.54/2.02  --resolution_flag                       false
% 11.54/2.02  --res_lit_sel                           adaptive
% 11.54/2.02  --res_lit_sel_side                      none
% 11.54/2.02  --res_ordering                          kbo
% 11.54/2.02  --res_to_prop_solver                    active
% 11.54/2.02  --res_prop_simpl_new                    false
% 11.54/2.02  --res_prop_simpl_given                  true
% 11.54/2.02  --res_passive_queue_type                priority_queues
% 11.54/2.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.54/2.02  --res_passive_queues_freq               [15;5]
% 11.54/2.02  --res_forward_subs                      full
% 11.54/2.02  --res_backward_subs                     full
% 11.54/2.02  --res_forward_subs_resolution           true
% 11.54/2.02  --res_backward_subs_resolution          true
% 11.54/2.02  --res_orphan_elimination                true
% 11.54/2.02  --res_time_limit                        2.
% 11.54/2.02  --res_out_proof                         true
% 11.54/2.02  
% 11.54/2.02  ------ Superposition Options
% 11.54/2.02  
% 11.54/2.02  --superposition_flag                    true
% 11.54/2.02  --sup_passive_queue_type                priority_queues
% 11.54/2.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.54/2.02  --sup_passive_queues_freq               [8;1;4]
% 11.54/2.02  --demod_completeness_check              fast
% 11.54/2.02  --demod_use_ground                      true
% 11.54/2.02  --sup_to_prop_solver                    passive
% 11.54/2.02  --sup_prop_simpl_new                    true
% 11.54/2.02  --sup_prop_simpl_given                  true
% 11.54/2.02  --sup_fun_splitting                     false
% 11.54/2.02  --sup_smt_interval                      50000
% 11.54/2.02  
% 11.54/2.02  ------ Superposition Simplification Setup
% 11.54/2.02  
% 11.54/2.02  --sup_indices_passive                   []
% 11.54/2.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.54/2.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.54/2.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.54/2.02  --sup_full_triv                         [TrivRules;PropSubs]
% 11.54/2.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.54/2.02  --sup_full_bw                           [BwDemod]
% 11.54/2.02  --sup_immed_triv                        [TrivRules]
% 11.54/2.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.54/2.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.54/2.02  --sup_immed_bw_main                     []
% 11.54/2.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.54/2.02  --sup_input_triv                        [Unflattening;TrivRules]
% 11.54/2.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.54/2.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.54/2.02  
% 11.54/2.02  ------ Combination Options
% 11.54/2.02  
% 11.54/2.02  --comb_res_mult                         3
% 11.54/2.02  --comb_sup_mult                         2
% 11.54/2.02  --comb_inst_mult                        10
% 11.54/2.02  
% 11.54/2.02  ------ Debug Options
% 11.54/2.02  
% 11.54/2.02  --dbg_backtrace                         false
% 11.54/2.02  --dbg_dump_prop_clauses                 false
% 11.54/2.02  --dbg_dump_prop_clauses_file            -
% 11.54/2.02  --dbg_out_stat                          false
% 11.54/2.02  
% 11.54/2.02  
% 11.54/2.02  
% 11.54/2.02  
% 11.54/2.02  ------ Proving...
% 11.54/2.02  
% 11.54/2.02  
% 11.54/2.02  % SZS status Theorem for theBenchmark.p
% 11.54/2.02  
% 11.54/2.02  % SZS output start CNFRefutation for theBenchmark.p
% 11.54/2.02  
% 11.54/2.02  fof(f4,axiom,(
% 11.54/2.02    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 11.54/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.02  
% 11.54/2.02  fof(f13,plain,(
% 11.54/2.02    ! [X0] : (k1_xboole_0 = X0 | ? [X1] : (? [X2] : ((X1 != X2 & (k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1))))),
% 11.54/2.02    inference(ennf_transformation,[],[f4])).
% 11.54/2.02  
% 11.54/2.02  fof(f14,plain,(
% 11.54/2.02    ! [X0] : (k1_xboole_0 = X0 | ? [X1] : (? [X2] : (X1 != X2 & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)))),
% 11.54/2.02    inference(flattening,[],[f13])).
% 11.54/2.02  
% 11.54/2.02  fof(f30,plain,(
% 11.54/2.02    ( ! [X1] : (! [X0] : (? [X2] : (X1 != X2 & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (sK6(X0) != X1 & k1_relat_1(sK6(X0)) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0))))) )),
% 11.54/2.02    introduced(choice_axiom,[])).
% 11.54/2.02  
% 11.54/2.02  fof(f29,plain,(
% 11.54/2.02    ! [X0] : (? [X1] : (? [X2] : (X1 != X2 & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (sK5(X0) != X2 & k1_relat_1(X2) = X0 & k1_relat_1(sK5(X0)) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0))))),
% 11.54/2.02    introduced(choice_axiom,[])).
% 11.54/2.02  
% 11.54/2.02  fof(f31,plain,(
% 11.54/2.02    ! [X0] : (k1_xboole_0 = X0 | ((sK5(X0) != sK6(X0) & k1_relat_1(sK6(X0)) = X0 & k1_relat_1(sK5(X0)) = X0 & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0))) & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0))))),
% 11.54/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f14,f30,f29])).
% 11.54/2.02  
% 11.54/2.02  fof(f52,plain,(
% 11.54/2.02    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(sK5(X0)) = X0) )),
% 11.54/2.02    inference(cnf_transformation,[],[f31])).
% 11.54/2.02  
% 11.54/2.02  fof(f2,axiom,(
% 11.54/2.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 11.54/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.02  
% 11.54/2.02  fof(f10,plain,(
% 11.54/2.02    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.54/2.02    inference(ennf_transformation,[],[f2])).
% 11.54/2.02  
% 11.54/2.02  fof(f11,plain,(
% 11.54/2.02    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.54/2.02    inference(flattening,[],[f10])).
% 11.54/2.02  
% 11.54/2.02  fof(f21,plain,(
% 11.54/2.02    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.54/2.02    inference(nnf_transformation,[],[f11])).
% 11.54/2.02  
% 11.54/2.02  fof(f22,plain,(
% 11.54/2.02    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.54/2.02    inference(rectify,[],[f21])).
% 11.54/2.02  
% 11.54/2.02  fof(f25,plain,(
% 11.54/2.02    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 11.54/2.02    introduced(choice_axiom,[])).
% 11.54/2.02  
% 11.54/2.02  fof(f24,plain,(
% 11.54/2.02    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 11.54/2.02    introduced(choice_axiom,[])).
% 11.54/2.02  
% 11.54/2.02  fof(f23,plain,(
% 11.54/2.02    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 11.54/2.02    introduced(choice_axiom,[])).
% 11.54/2.02  
% 11.54/2.02  fof(f26,plain,(
% 11.54/2.02    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.54/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f25,f24,f23])).
% 11.54/2.02  
% 11.54/2.02  fof(f41,plain,(
% 11.54/2.02    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.54/2.02    inference(cnf_transformation,[],[f26])).
% 11.54/2.02  
% 11.54/2.02  fof(f48,plain,(
% 11.54/2.02    ( ! [X0] : (k1_xboole_0 = X0 | v1_relat_1(sK5(X0))) )),
% 11.54/2.02    inference(cnf_transformation,[],[f31])).
% 11.54/2.02  
% 11.54/2.02  fof(f49,plain,(
% 11.54/2.02    ( ! [X0] : (k1_xboole_0 = X0 | v1_funct_1(sK5(X0))) )),
% 11.54/2.02    inference(cnf_transformation,[],[f31])).
% 11.54/2.02  
% 11.54/2.02  fof(f3,axiom,(
% 11.54/2.02    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 11.54/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.02  
% 11.54/2.02  fof(f12,plain,(
% 11.54/2.02    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 11.54/2.02    inference(ennf_transformation,[],[f3])).
% 11.54/2.02  
% 11.54/2.02  fof(f27,plain,(
% 11.54/2.02    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))))),
% 11.54/2.02    introduced(choice_axiom,[])).
% 11.54/2.02  
% 11.54/2.02  fof(f28,plain,(
% 11.54/2.02    ! [X0,X1] : (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1)))),
% 11.54/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f27])).
% 11.54/2.02  
% 11.54/2.02  fof(f46,plain,(
% 11.54/2.02    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X0) )),
% 11.54/2.02    inference(cnf_transformation,[],[f28])).
% 11.54/2.02  
% 11.54/2.02  fof(f1,axiom,(
% 11.54/2.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.54/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.02  
% 11.54/2.02  fof(f8,plain,(
% 11.54/2.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 11.54/2.02    inference(unused_predicate_definition_removal,[],[f1])).
% 11.54/2.02  
% 11.54/2.02  fof(f9,plain,(
% 11.54/2.02    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 11.54/2.02    inference(ennf_transformation,[],[f8])).
% 11.54/2.02  
% 11.54/2.02  fof(f19,plain,(
% 11.54/2.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.54/2.02    introduced(choice_axiom,[])).
% 11.54/2.02  
% 11.54/2.02  fof(f20,plain,(
% 11.54/2.02    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.54/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f19])).
% 11.54/2.02  
% 11.54/2.02  fof(f36,plain,(
% 11.54/2.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.54/2.02    inference(cnf_transformation,[],[f20])).
% 11.54/2.02  
% 11.54/2.02  fof(f6,conjecture,(
% 11.54/2.02    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 11.54/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.02  
% 11.54/2.02  fof(f7,negated_conjecture,(
% 11.54/2.02    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 11.54/2.02    inference(negated_conjecture,[],[f6])).
% 11.54/2.02  
% 11.54/2.02  fof(f17,plain,(
% 11.54/2.02    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 11.54/2.02    inference(ennf_transformation,[],[f7])).
% 11.54/2.02  
% 11.54/2.02  fof(f18,plain,(
% 11.54/2.02    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 11.54/2.02    inference(flattening,[],[f17])).
% 11.54/2.02  
% 11.54/2.02  fof(f34,plain,(
% 11.54/2.02    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK8) | k1_relat_1(X2) != sK9 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK9 | k1_xboole_0 != sK8))),
% 11.54/2.02    introduced(choice_axiom,[])).
% 11.54/2.02  
% 11.54/2.02  fof(f35,plain,(
% 11.54/2.02    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK8) | k1_relat_1(X2) != sK9 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK9 | k1_xboole_0 != sK8)),
% 11.54/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f18,f34])).
% 11.54/2.02  
% 11.54/2.02  fof(f58,plain,(
% 11.54/2.02    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK8) | k1_relat_1(X2) != sK9 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 11.54/2.02    inference(cnf_transformation,[],[f35])).
% 11.54/2.02  
% 11.54/2.02  fof(f44,plain,(
% 11.54/2.02    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1))) )),
% 11.54/2.02    inference(cnf_transformation,[],[f28])).
% 11.54/2.02  
% 11.54/2.02  fof(f45,plain,(
% 11.54/2.02    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1))) )),
% 11.54/2.02    inference(cnf_transformation,[],[f28])).
% 11.54/2.02  
% 11.54/2.02  fof(f38,plain,(
% 11.54/2.02    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.54/2.02    inference(cnf_transformation,[],[f26])).
% 11.54/2.02  
% 11.54/2.02  fof(f62,plain,(
% 11.54/2.02    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.54/2.02    inference(equality_resolution,[],[f38])).
% 11.54/2.02  
% 11.54/2.02  fof(f47,plain,(
% 11.54/2.02    ( ! [X0,X3,X1] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 11.54/2.02    inference(cnf_transformation,[],[f28])).
% 11.54/2.02  
% 11.54/2.02  fof(f39,plain,(
% 11.54/2.02    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.54/2.02    inference(cnf_transformation,[],[f26])).
% 11.54/2.02  
% 11.54/2.02  fof(f61,plain,(
% 11.54/2.02    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.54/2.02    inference(equality_resolution,[],[f39])).
% 11.54/2.02  
% 11.54/2.02  fof(f37,plain,(
% 11.54/2.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.54/2.02    inference(cnf_transformation,[],[f20])).
% 11.54/2.02  
% 11.54/2.02  fof(f43,plain,(
% 11.54/2.02    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.54/2.02    inference(cnf_transformation,[],[f26])).
% 11.54/2.02  
% 11.54/2.02  fof(f54,plain,(
% 11.54/2.02    ( ! [X0] : (k1_xboole_0 = X0 | sK5(X0) != sK6(X0)) )),
% 11.54/2.02    inference(cnf_transformation,[],[f31])).
% 11.54/2.02  
% 11.54/2.02  fof(f5,axiom,(
% 11.54/2.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 11.54/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.54/2.02  
% 11.54/2.02  fof(f15,plain,(
% 11.54/2.02    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.54/2.02    inference(ennf_transformation,[],[f5])).
% 11.54/2.02  
% 11.54/2.02  fof(f16,plain,(
% 11.54/2.02    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.54/2.02    inference(flattening,[],[f15])).
% 11.54/2.02  
% 11.54/2.02  fof(f32,plain,(
% 11.54/2.02    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))))),
% 11.54/2.02    introduced(choice_axiom,[])).
% 11.54/2.02  
% 11.54/2.02  fof(f33,plain,(
% 11.54/2.02    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.54/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f16,f32])).
% 11.54/2.02  
% 11.54/2.02  fof(f55,plain,(
% 11.54/2.02    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK7(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.54/2.02    inference(cnf_transformation,[],[f33])).
% 11.54/2.02  
% 11.54/2.02  fof(f53,plain,(
% 11.54/2.02    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(sK6(X0)) = X0) )),
% 11.54/2.02    inference(cnf_transformation,[],[f31])).
% 11.54/2.02  
% 11.54/2.02  fof(f50,plain,(
% 11.54/2.02    ( ! [X0] : (k1_xboole_0 = X0 | v1_relat_1(sK6(X0))) )),
% 11.54/2.02    inference(cnf_transformation,[],[f31])).
% 11.54/2.02  
% 11.54/2.02  fof(f51,plain,(
% 11.54/2.02    ( ! [X0] : (k1_xboole_0 = X0 | v1_funct_1(sK6(X0))) )),
% 11.54/2.02    inference(cnf_transformation,[],[f31])).
% 11.54/2.02  
% 11.54/2.02  fof(f57,plain,(
% 11.54/2.02    k1_xboole_0 = sK9 | k1_xboole_0 != sK8),
% 11.54/2.02    inference(cnf_transformation,[],[f35])).
% 11.54/2.02  
% 11.54/2.02  cnf(c_14,plain,
% 11.54/2.02      ( k1_relat_1(sK5(X0)) = X0 | k1_xboole_0 = X0 ),
% 11.54/2.02      inference(cnf_transformation,[],[f52]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_4,plain,
% 11.54/2.02      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 11.54/2.02      | r2_hidden(sK1(X0,X1),X1)
% 11.54/2.02      | ~ v1_relat_1(X0)
% 11.54/2.02      | ~ v1_funct_1(X0)
% 11.54/2.02      | k2_relat_1(X0) = X1 ),
% 11.54/2.02      inference(cnf_transformation,[],[f41]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_703,plain,
% 11.54/2.02      ( k2_relat_1(X0) = X1
% 11.54/2.02      | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
% 11.54/2.02      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 11.54/2.02      | v1_relat_1(X0) != iProver_top
% 11.54/2.02      | v1_funct_1(X0) != iProver_top ),
% 11.54/2.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_2598,plain,
% 11.54/2.02      ( k2_relat_1(sK5(X0)) = X1
% 11.54/2.02      | k1_xboole_0 = X0
% 11.54/2.02      | r2_hidden(sK2(sK5(X0),X1),X0) = iProver_top
% 11.54/2.02      | r2_hidden(sK1(sK5(X0),X1),X1) = iProver_top
% 11.54/2.02      | v1_relat_1(sK5(X0)) != iProver_top
% 11.54/2.02      | v1_funct_1(sK5(X0)) != iProver_top ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_14,c_703]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_18,plain,
% 11.54/2.02      ( v1_relat_1(sK5(X0)) | k1_xboole_0 = X0 ),
% 11.54/2.02      inference(cnf_transformation,[],[f48]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_32,plain,
% 11.54/2.02      ( k1_xboole_0 = X0 | v1_relat_1(sK5(X0)) = iProver_top ),
% 11.54/2.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_17,plain,
% 11.54/2.02      ( v1_funct_1(sK5(X0)) | k1_xboole_0 = X0 ),
% 11.54/2.02      inference(cnf_transformation,[],[f49]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_35,plain,
% 11.54/2.02      ( k1_xboole_0 = X0 | v1_funct_1(sK5(X0)) = iProver_top ),
% 11.54/2.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_4766,plain,
% 11.54/2.02      ( k2_relat_1(sK5(X0)) = X1
% 11.54/2.02      | k1_xboole_0 = X0
% 11.54/2.02      | r2_hidden(sK2(sK5(X0),X1),X0) = iProver_top
% 11.54/2.02      | r2_hidden(sK1(sK5(X0),X1),X1) = iProver_top ),
% 11.54/2.02      inference(global_propositional_subsumption,
% 11.54/2.02                [status(thm)],
% 11.54/2.02                [c_2598,c_32,c_35]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_9,plain,
% 11.54/2.02      ( k1_relat_1(sK4(X0,X1)) = X0 ),
% 11.54/2.02      inference(cnf_transformation,[],[f46]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_1,plain,
% 11.54/2.02      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.54/2.02      inference(cnf_transformation,[],[f36]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_21,negated_conjecture,
% 11.54/2.02      ( ~ r1_tarski(k2_relat_1(X0),sK8)
% 11.54/2.02      | ~ v1_relat_1(X0)
% 11.54/2.02      | ~ v1_funct_1(X0)
% 11.54/2.02      | k1_relat_1(X0) != sK9 ),
% 11.54/2.02      inference(cnf_transformation,[],[f58]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_223,plain,
% 11.54/2.02      ( r2_hidden(sK0(X0,X1),X0)
% 11.54/2.02      | ~ v1_relat_1(X2)
% 11.54/2.02      | ~ v1_funct_1(X2)
% 11.54/2.02      | k1_relat_1(X2) != sK9
% 11.54/2.02      | k2_relat_1(X2) != X0
% 11.54/2.02      | sK8 != X1 ),
% 11.54/2.02      inference(resolution_lifted,[status(thm)],[c_1,c_21]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_224,plain,
% 11.54/2.02      ( r2_hidden(sK0(k2_relat_1(X0),sK8),k2_relat_1(X0))
% 11.54/2.02      | ~ v1_relat_1(X0)
% 11.54/2.02      | ~ v1_funct_1(X0)
% 11.54/2.02      | k1_relat_1(X0) != sK9 ),
% 11.54/2.02      inference(unflattening,[status(thm)],[c_223]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_690,plain,
% 11.54/2.02      ( k1_relat_1(X0) != sK9
% 11.54/2.02      | r2_hidden(sK0(k2_relat_1(X0),sK8),k2_relat_1(X0)) = iProver_top
% 11.54/2.02      | v1_relat_1(X0) != iProver_top
% 11.54/2.02      | v1_funct_1(X0) != iProver_top ),
% 11.54/2.02      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_945,plain,
% 11.54/2.02      ( sK9 != X0
% 11.54/2.02      | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK8),k2_relat_1(sK4(X0,X1))) = iProver_top
% 11.54/2.02      | v1_relat_1(sK4(X0,X1)) != iProver_top
% 11.54/2.02      | v1_funct_1(sK4(X0,X1)) != iProver_top ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_9,c_690]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_11,plain,
% 11.54/2.02      ( v1_relat_1(sK4(X0,X1)) ),
% 11.54/2.02      inference(cnf_transformation,[],[f44]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_47,plain,
% 11.54/2.02      ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
% 11.54/2.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_10,plain,
% 11.54/2.02      ( v1_funct_1(sK4(X0,X1)) ),
% 11.54/2.02      inference(cnf_transformation,[],[f45]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_50,plain,
% 11.54/2.02      ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
% 11.54/2.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_1009,plain,
% 11.54/2.02      ( sK9 != X0
% 11.54/2.02      | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK8),k2_relat_1(sK4(X0,X1))) = iProver_top ),
% 11.54/2.02      inference(global_propositional_subsumption,
% 11.54/2.02                [status(thm)],
% 11.54/2.02                [c_945,c_47,c_50]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_1017,plain,
% 11.54/2.02      ( r2_hidden(sK0(k2_relat_1(sK4(sK9,X0)),sK8),k2_relat_1(sK4(sK9,X0))) = iProver_top ),
% 11.54/2.02      inference(equality_resolution,[status(thm)],[c_1009]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_7,plain,
% 11.54/2.02      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 11.54/2.02      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 11.54/2.02      | ~ v1_relat_1(X1)
% 11.54/2.02      | ~ v1_funct_1(X1) ),
% 11.54/2.02      inference(cnf_transformation,[],[f62]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_700,plain,
% 11.54/2.02      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 11.54/2.02      | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
% 11.54/2.02      | v1_relat_1(X1) != iProver_top
% 11.54/2.02      | v1_funct_1(X1) != iProver_top ),
% 11.54/2.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_8,plain,
% 11.54/2.02      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK4(X1,X2),X0) = X2 ),
% 11.54/2.02      inference(cnf_transformation,[],[f47]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_699,plain,
% 11.54/2.02      ( k1_funct_1(sK4(X0,X1),X2) = X1
% 11.54/2.02      | r2_hidden(X2,X0) != iProver_top ),
% 11.54/2.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_2472,plain,
% 11.54/2.02      ( k1_funct_1(sK4(k1_relat_1(X0),X1),sK3(X0,X2)) = X1
% 11.54/2.02      | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
% 11.54/2.02      | v1_relat_1(X0) != iProver_top
% 11.54/2.02      | v1_funct_1(X0) != iProver_top ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_700,c_699]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_10174,plain,
% 11.54/2.02      ( k1_funct_1(sK4(k1_relat_1(sK4(sK9,X0)),X1),sK3(sK4(sK9,X0),sK0(k2_relat_1(sK4(sK9,X0)),sK8))) = X1
% 11.54/2.02      | v1_relat_1(sK4(sK9,X0)) != iProver_top
% 11.54/2.02      | v1_funct_1(sK4(sK9,X0)) != iProver_top ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_1017,c_2472]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_10398,plain,
% 11.54/2.02      ( k1_funct_1(sK4(sK9,X0),sK3(sK4(sK9,X1),sK0(k2_relat_1(sK4(sK9,X1)),sK8))) = X0
% 11.54/2.02      | v1_relat_1(sK4(sK9,X1)) != iProver_top
% 11.54/2.02      | v1_funct_1(sK4(sK9,X1)) != iProver_top ),
% 11.54/2.02      inference(demodulation,[status(thm)],[c_10174,c_9]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_698,plain,
% 11.54/2.02      ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
% 11.54/2.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_697,plain,
% 11.54/2.02      ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
% 11.54/2.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_10505,plain,
% 11.54/2.02      ( k1_funct_1(sK4(sK9,X0),sK3(sK4(sK9,X1),sK0(k2_relat_1(sK4(sK9,X1)),sK8))) = X0 ),
% 11.54/2.02      inference(forward_subsumption_resolution,
% 11.54/2.02                [status(thm)],
% 11.54/2.02                [c_10398,c_698,c_697]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_6,plain,
% 11.54/2.02      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 11.54/2.02      | ~ v1_relat_1(X1)
% 11.54/2.02      | ~ v1_funct_1(X1)
% 11.54/2.02      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 11.54/2.02      inference(cnf_transformation,[],[f61]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_701,plain,
% 11.54/2.02      ( k1_funct_1(X0,sK3(X0,X1)) = X1
% 11.54/2.02      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 11.54/2.02      | v1_relat_1(X0) != iProver_top
% 11.54/2.02      | v1_funct_1(X0) != iProver_top ),
% 11.54/2.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_2271,plain,
% 11.54/2.02      ( k1_funct_1(sK4(sK9,X0),sK3(sK4(sK9,X0),sK0(k2_relat_1(sK4(sK9,X0)),sK8))) = sK0(k2_relat_1(sK4(sK9,X0)),sK8)
% 11.54/2.02      | v1_relat_1(sK4(sK9,X0)) != iProver_top
% 11.54/2.02      | v1_funct_1(sK4(sK9,X0)) != iProver_top ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_1017,c_701]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_2305,plain,
% 11.54/2.02      ( k1_funct_1(sK4(sK9,X0),sK3(sK4(sK9,X0),sK0(k2_relat_1(sK4(sK9,X0)),sK8))) = sK0(k2_relat_1(sK4(sK9,X0)),sK8) ),
% 11.54/2.02      inference(forward_subsumption_resolution,
% 11.54/2.02                [status(thm)],
% 11.54/2.02                [c_2271,c_698,c_697]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_10507,plain,
% 11.54/2.02      ( sK0(k2_relat_1(sK4(sK9,X0)),sK8) = X0 ),
% 11.54/2.02      inference(demodulation,[status(thm)],[c_10505,c_2305]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_0,plain,
% 11.54/2.02      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.54/2.02      inference(cnf_transformation,[],[f37]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_241,plain,
% 11.54/2.02      ( ~ r2_hidden(sK0(X0,X1),X1)
% 11.54/2.02      | ~ v1_relat_1(X2)
% 11.54/2.02      | ~ v1_funct_1(X2)
% 11.54/2.02      | k1_relat_1(X2) != sK9
% 11.54/2.02      | k2_relat_1(X2) != X0
% 11.54/2.02      | sK8 != X1 ),
% 11.54/2.02      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_242,plain,
% 11.54/2.02      ( ~ r2_hidden(sK0(k2_relat_1(X0),sK8),sK8)
% 11.54/2.02      | ~ v1_relat_1(X0)
% 11.54/2.02      | ~ v1_funct_1(X0)
% 11.54/2.02      | k1_relat_1(X0) != sK9 ),
% 11.54/2.02      inference(unflattening,[status(thm)],[c_241]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_689,plain,
% 11.54/2.02      ( k1_relat_1(X0) != sK9
% 11.54/2.02      | r2_hidden(sK0(k2_relat_1(X0),sK8),sK8) != iProver_top
% 11.54/2.02      | v1_relat_1(X0) != iProver_top
% 11.54/2.02      | v1_funct_1(X0) != iProver_top ),
% 11.54/2.02      inference(predicate_to_equality,[status(thm)],[c_242]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_946,plain,
% 11.54/2.02      ( sK9 != X0
% 11.54/2.02      | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK8),sK8) != iProver_top
% 11.54/2.02      | v1_relat_1(sK4(X0,X1)) != iProver_top
% 11.54/2.02      | v1_funct_1(sK4(X0,X1)) != iProver_top ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_9,c_689]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_996,plain,
% 11.54/2.02      ( sK9 != X0
% 11.54/2.02      | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),sK8),sK8) != iProver_top ),
% 11.54/2.02      inference(global_propositional_subsumption,
% 11.54/2.02                [status(thm)],
% 11.54/2.02                [c_946,c_47,c_50]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_1004,plain,
% 11.54/2.02      ( r2_hidden(sK0(k2_relat_1(sK4(sK9,X0)),sK8),sK8) != iProver_top ),
% 11.54/2.02      inference(equality_resolution,[status(thm)],[c_996]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_11622,plain,
% 11.54/2.02      ( r2_hidden(X0,sK8) != iProver_top ),
% 11.54/2.02      inference(demodulation,[status(thm)],[c_10507,c_1004]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_11857,plain,
% 11.54/2.02      ( k2_relat_1(sK5(sK8)) = X0
% 11.54/2.02      | sK8 = k1_xboole_0
% 11.54/2.02      | r2_hidden(sK1(sK5(sK8),X0),X0) = iProver_top ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_4766,c_11622]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_17640,plain,
% 11.54/2.02      ( k1_funct_1(sK4(X0,X1),sK1(sK5(sK8),X0)) = X1
% 11.54/2.02      | k2_relat_1(sK5(sK8)) = X0
% 11.54/2.02      | sK8 = k1_xboole_0 ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_11857,c_699]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_2,plain,
% 11.54/2.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.54/2.02      | ~ r2_hidden(sK1(X1,X2),X2)
% 11.54/2.02      | ~ v1_relat_1(X1)
% 11.54/2.02      | ~ v1_funct_1(X1)
% 11.54/2.02      | sK1(X1,X2) != k1_funct_1(X1,X0)
% 11.54/2.02      | k2_relat_1(X1) = X2 ),
% 11.54/2.02      inference(cnf_transformation,[],[f43]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_705,plain,
% 11.54/2.02      ( sK1(X0,X1) != k1_funct_1(X0,X2)
% 11.54/2.02      | k2_relat_1(X0) = X1
% 11.54/2.02      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 11.54/2.02      | r2_hidden(sK1(X0,X1),X1) != iProver_top
% 11.54/2.02      | v1_relat_1(X0) != iProver_top
% 11.54/2.02      | v1_funct_1(X0) != iProver_top ),
% 11.54/2.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_45527,plain,
% 11.54/2.02      ( sK1(sK4(X0,X1),X2) != X1
% 11.54/2.02      | k2_relat_1(sK4(X0,X1)) = X2
% 11.54/2.02      | k2_relat_1(sK5(sK8)) = X0
% 11.54/2.02      | sK8 = k1_xboole_0
% 11.54/2.02      | r2_hidden(sK1(sK4(X0,X1),X2),X2) != iProver_top
% 11.54/2.02      | r2_hidden(sK1(sK5(sK8),X0),k1_relat_1(sK4(X0,X1))) != iProver_top
% 11.54/2.02      | v1_relat_1(sK4(X0,X1)) != iProver_top
% 11.54/2.02      | v1_funct_1(sK4(X0,X1)) != iProver_top ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_17640,c_705]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_45550,plain,
% 11.54/2.02      ( sK1(sK4(X0,X1),X2) != X1
% 11.54/2.02      | k2_relat_1(sK4(X0,X1)) = X2
% 11.54/2.02      | k2_relat_1(sK5(sK8)) = X0
% 11.54/2.02      | sK8 = k1_xboole_0
% 11.54/2.02      | r2_hidden(sK1(sK4(X0,X1),X2),X2) != iProver_top
% 11.54/2.02      | r2_hidden(sK1(sK5(sK8),X0),X0) != iProver_top
% 11.54/2.02      | v1_relat_1(sK4(X0,X1)) != iProver_top
% 11.54/2.02      | v1_funct_1(sK4(X0,X1)) != iProver_top ),
% 11.54/2.02      inference(light_normalisation,[status(thm)],[c_45527,c_9]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_12,plain,
% 11.54/2.02      ( sK6(X0) != sK5(X0) | k1_xboole_0 = X0 ),
% 11.54/2.02      inference(cnf_transformation,[],[f54]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_914,plain,
% 11.54/2.02      ( sK6(sK8) != sK5(sK8) | k1_xboole_0 = sK8 ),
% 11.54/2.02      inference(instantiation,[status(thm)],[c_12]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_386,plain,( X0 = X0 ),theory(equality) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_4486,plain,
% 11.54/2.02      ( sK8 = sK8 ),
% 11.54/2.02      inference(instantiation,[status(thm)],[c_386]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_387,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_3057,plain,
% 11.54/2.02      ( X0 != X1 | sK8 != X1 | sK8 = X0 ),
% 11.54/2.02      inference(instantiation,[status(thm)],[c_387]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_8262,plain,
% 11.54/2.02      ( X0 != sK8 | sK8 = X0 | sK8 != sK8 ),
% 11.54/2.02      inference(instantiation,[status(thm)],[c_3057]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_8263,plain,
% 11.54/2.02      ( sK8 != sK8 | sK8 = k1_xboole_0 | k1_xboole_0 != sK8 ),
% 11.54/2.02      inference(instantiation,[status(thm)],[c_8262]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_20,plain,
% 11.54/2.02      ( r2_hidden(sK7(X0,X1),k1_relat_1(X0))
% 11.54/2.02      | ~ v1_relat_1(X0)
% 11.54/2.02      | ~ v1_relat_1(X1)
% 11.54/2.02      | ~ v1_funct_1(X0)
% 11.54/2.02      | ~ v1_funct_1(X1)
% 11.54/2.02      | X1 = X0
% 11.54/2.02      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 11.54/2.02      inference(cnf_transformation,[],[f55]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_691,plain,
% 11.54/2.02      ( X0 = X1
% 11.54/2.02      | k1_relat_1(X0) != k1_relat_1(X1)
% 11.54/2.02      | r2_hidden(sK7(X1,X0),k1_relat_1(X1)) = iProver_top
% 11.54/2.02      | v1_relat_1(X1) != iProver_top
% 11.54/2.02      | v1_relat_1(X0) != iProver_top
% 11.54/2.02      | v1_funct_1(X1) != iProver_top
% 11.54/2.02      | v1_funct_1(X0) != iProver_top ),
% 11.54/2.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_1145,plain,
% 11.54/2.02      ( sK4(X0,X1) = X2
% 11.54/2.02      | k1_relat_1(X2) != X0
% 11.54/2.02      | r2_hidden(sK7(X2,sK4(X0,X1)),k1_relat_1(X2)) = iProver_top
% 11.54/2.02      | v1_relat_1(X2) != iProver_top
% 11.54/2.02      | v1_relat_1(sK4(X0,X1)) != iProver_top
% 11.54/2.02      | v1_funct_1(X2) != iProver_top
% 11.54/2.02      | v1_funct_1(sK4(X0,X1)) != iProver_top ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_9,c_691]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_4653,plain,
% 11.54/2.02      ( v1_funct_1(X2) != iProver_top
% 11.54/2.02      | sK4(X0,X1) = X2
% 11.54/2.02      | k1_relat_1(X2) != X0
% 11.54/2.02      | r2_hidden(sK7(X2,sK4(X0,X1)),k1_relat_1(X2)) = iProver_top
% 11.54/2.02      | v1_relat_1(X2) != iProver_top ),
% 11.54/2.02      inference(global_propositional_subsumption,
% 11.54/2.02                [status(thm)],
% 11.54/2.02                [c_1145,c_47,c_50]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_4654,plain,
% 11.54/2.02      ( sK4(X0,X1) = X2
% 11.54/2.02      | k1_relat_1(X2) != X0
% 11.54/2.02      | r2_hidden(sK7(X2,sK4(X0,X1)),k1_relat_1(X2)) = iProver_top
% 11.54/2.02      | v1_relat_1(X2) != iProver_top
% 11.54/2.02      | v1_funct_1(X2) != iProver_top ),
% 11.54/2.02      inference(renaming,[status(thm)],[c_4653]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_4667,plain,
% 11.54/2.02      ( sK4(k1_relat_1(X0),X1) = X0
% 11.54/2.02      | r2_hidden(sK7(X0,sK4(k1_relat_1(X0),X1)),k1_relat_1(X0)) = iProver_top
% 11.54/2.02      | v1_relat_1(X0) != iProver_top
% 11.54/2.02      | v1_funct_1(X0) != iProver_top ),
% 11.54/2.02      inference(equality_resolution,[status(thm)],[c_4654]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_49628,plain,
% 11.54/2.02      ( sK4(k1_relat_1(sK5(X0)),X1) = sK5(X0)
% 11.54/2.02      | k1_xboole_0 = X0
% 11.54/2.02      | r2_hidden(sK7(sK5(X0),sK4(X0,X1)),X0) = iProver_top
% 11.54/2.02      | v1_relat_1(sK5(X0)) != iProver_top
% 11.54/2.02      | v1_funct_1(sK5(X0)) != iProver_top ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_14,c_4667]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_50194,plain,
% 11.54/2.02      ( sK4(k1_relat_1(sK5(X0)),X1) = sK5(X0)
% 11.54/2.02      | k1_xboole_0 = X0
% 11.54/2.02      | r2_hidden(sK7(sK5(X0),sK4(X0,X1)),X0) = iProver_top ),
% 11.54/2.02      inference(global_propositional_subsumption,
% 11.54/2.02                [status(thm)],
% 11.54/2.02                [c_49628,c_32,c_35]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_50222,plain,
% 11.54/2.02      ( sK4(k1_relat_1(sK5(sK8)),X0) = sK5(sK8) | sK8 = k1_xboole_0 ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_50194,c_11622]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_50767,plain,
% 11.54/2.02      ( sK4(sK8,X0) = sK5(sK8) | sK8 = k1_xboole_0 ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_14,c_50222]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_13,plain,
% 11.54/2.02      ( k1_relat_1(sK6(X0)) = X0 | k1_xboole_0 = X0 ),
% 11.54/2.02      inference(cnf_transformation,[],[f53]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_49627,plain,
% 11.54/2.02      ( sK4(k1_relat_1(sK6(X0)),X1) = sK6(X0)
% 11.54/2.02      | k1_xboole_0 = X0
% 11.54/2.02      | r2_hidden(sK7(sK6(X0),sK4(X0,X1)),X0) = iProver_top
% 11.54/2.02      | v1_relat_1(sK6(X0)) != iProver_top
% 11.54/2.02      | v1_funct_1(sK6(X0)) != iProver_top ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_13,c_4667]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_16,plain,
% 11.54/2.02      ( v1_relat_1(sK6(X0)) | k1_xboole_0 = X0 ),
% 11.54/2.02      inference(cnf_transformation,[],[f50]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_38,plain,
% 11.54/2.02      ( k1_xboole_0 = X0 | v1_relat_1(sK6(X0)) = iProver_top ),
% 11.54/2.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_15,plain,
% 11.54/2.02      ( v1_funct_1(sK6(X0)) | k1_xboole_0 = X0 ),
% 11.54/2.02      inference(cnf_transformation,[],[f51]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_41,plain,
% 11.54/2.02      ( k1_xboole_0 = X0 | v1_funct_1(sK6(X0)) = iProver_top ),
% 11.54/2.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_49894,plain,
% 11.54/2.02      ( sK4(k1_relat_1(sK6(X0)),X1) = sK6(X0)
% 11.54/2.02      | k1_xboole_0 = X0
% 11.54/2.02      | r2_hidden(sK7(sK6(X0),sK4(X0,X1)),X0) = iProver_top ),
% 11.54/2.02      inference(global_propositional_subsumption,
% 11.54/2.02                [status(thm)],
% 11.54/2.02                [c_49627,c_38,c_41]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_49922,plain,
% 11.54/2.02      ( sK4(k1_relat_1(sK6(sK8)),X0) = sK6(sK8) | sK8 = k1_xboole_0 ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_49894,c_11622]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_50668,plain,
% 11.54/2.02      ( sK4(sK8,X0) = sK6(sK8) | sK8 = k1_xboole_0 ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_13,c_49922]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_51769,plain,
% 11.54/2.02      ( sK6(sK8) = sK5(sK8) | sK8 = k1_xboole_0 ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_50767,c_50668]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_52445,plain,
% 11.54/2.02      ( sK8 = k1_xboole_0 ),
% 11.54/2.02      inference(global_propositional_subsumption,
% 11.54/2.02                [status(thm)],
% 11.54/2.02                [c_45550,c_914,c_4486,c_8263,c_51769]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_2596,plain,
% 11.54/2.02      ( k2_relat_1(sK4(X0,X1)) = X2
% 11.54/2.02      | r2_hidden(sK2(sK4(X0,X1),X2),X0) = iProver_top
% 11.54/2.02      | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top
% 11.54/2.02      | v1_relat_1(sK4(X0,X1)) != iProver_top
% 11.54/2.02      | v1_funct_1(sK4(X0,X1)) != iProver_top ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_9,c_703]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_5224,plain,
% 11.54/2.02      ( k2_relat_1(sK4(X0,X1)) = X2
% 11.54/2.02      | r2_hidden(sK2(sK4(X0,X1),X2),X0) = iProver_top
% 11.54/2.02      | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top ),
% 11.54/2.02      inference(global_propositional_subsumption,
% 11.54/2.02                [status(thm)],
% 11.54/2.02                [c_2596,c_47,c_50]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_11850,plain,
% 11.54/2.02      ( k2_relat_1(sK4(X0,X1)) = sK8
% 11.54/2.02      | r2_hidden(sK2(sK4(X0,X1),sK8),X0) = iProver_top ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_5224,c_11622]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_15619,plain,
% 11.54/2.02      ( k2_relat_1(sK4(sK8,X0)) = sK8 ),
% 11.54/2.02      inference(superposition,[status(thm)],[c_11850,c_11622]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_52568,plain,
% 11.54/2.02      ( k2_relat_1(sK4(k1_xboole_0,X0)) = k1_xboole_0 ),
% 11.54/2.02      inference(demodulation,[status(thm)],[c_52445,c_15619]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_52583,plain,
% 11.54/2.02      ( sK0(k2_relat_1(sK4(sK9,X0)),k1_xboole_0) = X0 ),
% 11.54/2.02      inference(demodulation,[status(thm)],[c_52445,c_10507]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_22,negated_conjecture,
% 11.54/2.02      ( k1_xboole_0 = sK9 | k1_xboole_0 != sK8 ),
% 11.54/2.02      inference(cnf_transformation,[],[f57]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_52606,plain,
% 11.54/2.02      ( sK9 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 11.54/2.02      inference(demodulation,[status(thm)],[c_52445,c_22]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_52607,plain,
% 11.54/2.02      ( sK9 = k1_xboole_0 ),
% 11.54/2.02      inference(equality_resolution_simp,[status(thm)],[c_52606]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_52642,plain,
% 11.54/2.02      ( sK0(k2_relat_1(sK4(k1_xboole_0,X0)),k1_xboole_0) = X0 ),
% 11.54/2.02      inference(light_normalisation,[status(thm)],[c_52583,c_52607]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_52652,plain,
% 11.54/2.02      ( sK0(k1_xboole_0,k1_xboole_0) = X0 ),
% 11.54/2.02      inference(demodulation,[status(thm)],[c_52568,c_52642]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_52602,plain,
% 11.54/2.02      ( sK9 != X0
% 11.54/2.02      | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),k1_xboole_0),k2_relat_1(sK4(X0,X1))) = iProver_top ),
% 11.54/2.02      inference(demodulation,[status(thm)],[c_52445,c_1009]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_52633,plain,
% 11.54/2.02      ( k1_xboole_0 != X0
% 11.54/2.02      | r2_hidden(sK0(k2_relat_1(sK4(X0,X1)),k1_xboole_0),k2_relat_1(sK4(X0,X1))) = iProver_top ),
% 11.54/2.02      inference(light_normalisation,[status(thm)],[c_52602,c_52607]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_52656,plain,
% 11.54/2.02      ( k1_xboole_0 != X0
% 11.54/2.02      | r2_hidden(sK0(k2_relat_1(sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0),k2_relat_1(sK0(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.54/2.02      inference(demodulation,[status(thm)],[c_52652,c_52633]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_52658,plain,
% 11.54/2.02      ( k2_relat_1(sK0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 11.54/2.02      inference(demodulation,[status(thm)],[c_52652,c_52568]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_52670,plain,
% 11.54/2.02      ( k1_xboole_0 != X0
% 11.54/2.02      | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 11.54/2.02      inference(light_normalisation,[status(thm)],[c_52656,c_52658]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_52582,plain,
% 11.54/2.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.54/2.02      inference(demodulation,[status(thm)],[c_52445,c_11622]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_52673,plain,
% 11.54/2.02      ( k1_xboole_0 != X0 ),
% 11.54/2.02      inference(forward_subsumption_resolution,
% 11.54/2.02                [status(thm)],
% 11.54/2.02                [c_52670,c_52582]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_52777,plain,
% 11.54/2.02      ( k1_xboole_0 != k1_xboole_0 ),
% 11.54/2.02      inference(instantiation,[status(thm)],[c_52673]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(c_401,plain,
% 11.54/2.02      ( k1_xboole_0 = k1_xboole_0 ),
% 11.54/2.02      inference(instantiation,[status(thm)],[c_386]) ).
% 11.54/2.02  
% 11.54/2.02  cnf(contradiction,plain,
% 11.54/2.02      ( $false ),
% 11.54/2.02      inference(minisat,[status(thm)],[c_52777,c_401]) ).
% 11.54/2.02  
% 11.54/2.02  
% 11.54/2.02  % SZS output end CNFRefutation for theBenchmark.p
% 11.54/2.02  
% 11.54/2.02  ------                               Statistics
% 11.54/2.02  
% 11.54/2.02  ------ General
% 11.54/2.02  
% 11.54/2.02  abstr_ref_over_cycles:                  0
% 11.54/2.02  abstr_ref_under_cycles:                 0
% 11.54/2.02  gc_basic_clause_elim:                   0
% 11.54/2.02  forced_gc_time:                         0
% 11.54/2.02  parsing_time:                           0.012
% 11.54/2.02  unif_index_cands_time:                  0.
% 11.54/2.02  unif_index_add_time:                    0.
% 11.54/2.02  orderings_time:                         0.
% 11.54/2.02  out_proof_time:                         0.015
% 11.54/2.02  total_time:                             1.438
% 11.54/2.02  num_of_symbols:                         49
% 11.54/2.02  num_of_terms:                           48422
% 11.54/2.02  
% 11.54/2.02  ------ Preprocessing
% 11.54/2.02  
% 11.54/2.02  num_of_splits:                          0
% 11.54/2.02  num_of_split_atoms:                     0
% 11.54/2.02  num_of_reused_defs:                     0
% 11.54/2.02  num_eq_ax_congr_red:                    41
% 11.54/2.02  num_of_sem_filtered_clauses:            1
% 11.54/2.02  num_of_subtypes:                        0
% 11.54/2.02  monotx_restored_types:                  0
% 11.54/2.02  sat_num_of_epr_types:                   0
% 11.54/2.02  sat_num_of_non_cyclic_types:            0
% 11.54/2.02  sat_guarded_non_collapsed_types:        0
% 11.54/2.02  num_pure_diseq_elim:                    0
% 11.54/2.02  simp_replaced_by:                       0
% 11.54/2.02  res_preprocessed:                       106
% 11.54/2.02  prep_upred:                             0
% 11.54/2.02  prep_unflattend:                        4
% 11.54/2.02  smt_new_axioms:                         0
% 11.54/2.02  pred_elim_cands:                        3
% 11.54/2.02  pred_elim:                              1
% 11.54/2.02  pred_elim_cl:                           1
% 11.54/2.02  pred_elim_cycles:                       3
% 11.54/2.02  merged_defs:                            0
% 11.54/2.02  merged_defs_ncl:                        0
% 11.54/2.02  bin_hyper_res:                          0
% 11.54/2.02  prep_cycles:                            4
% 11.54/2.02  pred_elim_time:                         0.001
% 11.54/2.02  splitting_time:                         0.
% 11.54/2.02  sem_filter_time:                        0.
% 11.54/2.02  monotx_time:                            0.
% 11.54/2.02  subtype_inf_time:                       0.
% 11.54/2.02  
% 11.54/2.02  ------ Problem properties
% 11.54/2.02  
% 11.54/2.02  clauses:                                22
% 11.54/2.02  conjectures:                            1
% 11.54/2.02  epr:                                    1
% 11.54/2.02  horn:                                   13
% 11.54/2.02  ground:                                 1
% 11.54/2.02  unary:                                  3
% 11.54/2.02  binary:                                 9
% 11.54/2.02  lits:                                   71
% 11.54/2.02  lits_eq:                                27
% 11.54/2.02  fd_pure:                                0
% 11.54/2.02  fd_pseudo:                              0
% 11.54/2.02  fd_cond:                                5
% 11.54/2.02  fd_pseudo_cond:                         5
% 11.54/2.02  ac_symbols:                             0
% 11.54/2.02  
% 11.54/2.02  ------ Propositional Solver
% 11.54/2.02  
% 11.54/2.02  prop_solver_calls:                      30
% 11.54/2.02  prop_fast_solver_calls:                 2589
% 11.54/2.02  smt_solver_calls:                       0
% 11.54/2.02  smt_fast_solver_calls:                  0
% 11.54/2.02  prop_num_of_clauses:                    14420
% 11.54/2.02  prop_preprocess_simplified:             20460
% 11.54/2.02  prop_fo_subsumed:                       162
% 11.54/2.02  prop_solver_time:                       0.
% 11.54/2.02  smt_solver_time:                        0.
% 11.54/2.02  smt_fast_solver_time:                   0.
% 11.54/2.02  prop_fast_solver_time:                  0.
% 11.54/2.02  prop_unsat_core_time:                   0.001
% 11.54/2.02  
% 11.54/2.02  ------ QBF
% 11.54/2.02  
% 11.54/2.02  qbf_q_res:                              0
% 11.54/2.02  qbf_num_tautologies:                    0
% 11.54/2.02  qbf_prep_cycles:                        0
% 11.54/2.02  
% 11.54/2.02  ------ BMC1
% 11.54/2.02  
% 11.54/2.02  bmc1_current_bound:                     -1
% 11.54/2.02  bmc1_last_solved_bound:                 -1
% 11.54/2.02  bmc1_unsat_core_size:                   -1
% 11.54/2.02  bmc1_unsat_core_parents_size:           -1
% 11.54/2.02  bmc1_merge_next_fun:                    0
% 11.54/2.02  bmc1_unsat_core_clauses_time:           0.
% 11.54/2.02  
% 11.54/2.02  ------ Instantiation
% 11.54/2.02  
% 11.54/2.02  inst_num_of_clauses:                    3317
% 11.54/2.02  inst_num_in_passive:                    961
% 11.54/2.02  inst_num_in_active:                     1355
% 11.54/2.02  inst_num_in_unprocessed:                1004
% 11.54/2.02  inst_num_of_loops:                      1720
% 11.54/2.02  inst_num_of_learning_restarts:          0
% 11.54/2.02  inst_num_moves_active_passive:          361
% 11.54/2.02  inst_lit_activity:                      0
% 11.54/2.02  inst_lit_activity_moves:                0
% 11.54/2.02  inst_num_tautologies:                   0
% 11.54/2.02  inst_num_prop_implied:                  0
% 11.54/2.02  inst_num_existing_simplified:           0
% 11.54/2.02  inst_num_eq_res_simplified:             0
% 11.54/2.02  inst_num_child_elim:                    0
% 11.54/2.02  inst_num_of_dismatching_blockings:      3562
% 11.54/2.02  inst_num_of_non_proper_insts:           4826
% 11.54/2.02  inst_num_of_duplicates:                 0
% 11.54/2.02  inst_inst_num_from_inst_to_res:         0
% 11.54/2.02  inst_dismatching_checking_time:         0.
% 11.54/2.02  
% 11.54/2.02  ------ Resolution
% 11.54/2.02  
% 11.54/2.02  res_num_of_clauses:                     0
% 11.54/2.02  res_num_in_passive:                     0
% 11.54/2.02  res_num_in_active:                      0
% 11.54/2.02  res_num_of_loops:                       110
% 11.54/2.02  res_forward_subset_subsumed:            141
% 11.54/2.02  res_backward_subset_subsumed:           30
% 11.54/2.02  res_forward_subsumed:                   0
% 11.54/2.02  res_backward_subsumed:                  0
% 11.54/2.02  res_forward_subsumption_resolution:     0
% 11.54/2.02  res_backward_subsumption_resolution:    0
% 11.54/2.02  res_clause_to_clause_subsumption:       5892
% 11.54/2.02  res_orphan_elimination:                 0
% 11.54/2.02  res_tautology_del:                      213
% 11.54/2.02  res_num_eq_res_simplified:              0
% 11.54/2.02  res_num_sel_changes:                    0
% 11.54/2.02  res_moves_from_active_to_pass:          0
% 11.54/2.02  
% 11.54/2.02  ------ Superposition
% 11.54/2.02  
% 11.54/2.02  sup_time_total:                         0.
% 11.54/2.02  sup_time_generating:                    0.
% 11.54/2.02  sup_time_sim_full:                      0.
% 11.54/2.02  sup_time_sim_immed:                     0.
% 11.54/2.02  
% 11.54/2.02  sup_num_of_clauses:                     1439
% 11.54/2.02  sup_num_in_active:                      148
% 11.54/2.02  sup_num_in_passive:                     1291
% 11.54/2.02  sup_num_of_loops:                       343
% 11.54/2.02  sup_fw_superposition:                   1155
% 11.54/2.02  sup_bw_superposition:                   1370
% 11.54/2.02  sup_immediate_simplified:               889
% 11.54/2.02  sup_given_eliminated:                   0
% 11.54/2.02  comparisons_done:                       0
% 11.54/2.02  comparisons_avoided:                    447
% 11.54/2.02  
% 11.54/2.02  ------ Simplifications
% 11.54/2.02  
% 11.54/2.02  
% 11.54/2.02  sim_fw_subset_subsumed:                 385
% 11.54/2.02  sim_bw_subset_subsumed:                 73
% 11.54/2.02  sim_fw_subsumed:                        307
% 11.54/2.02  sim_bw_subsumed:                        2
% 11.54/2.02  sim_fw_subsumption_res:                 194
% 11.54/2.02  sim_bw_subsumption_res:                 0
% 11.54/2.02  sim_tautology_del:                      16
% 11.54/2.02  sim_eq_tautology_del:                   91
% 11.54/2.02  sim_eq_res_simp:                        1
% 11.54/2.02  sim_fw_demodulated:                     205
% 11.54/2.02  sim_bw_demodulated:                     172
% 11.54/2.02  sim_light_normalised:                   76
% 11.54/2.02  sim_joinable_taut:                      0
% 11.54/2.02  sim_joinable_simp:                      0
% 11.54/2.02  sim_ac_normalised:                      0
% 11.54/2.02  sim_smt_subsumption:                    0
% 11.54/2.02  
%------------------------------------------------------------------------------
