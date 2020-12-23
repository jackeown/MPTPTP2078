%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:34 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  160 (1001 expanded)
%              Number of clauses        :   92 ( 233 expanded)
%              Number of leaves         :   20 ( 347 expanded)
%              Depth                    :   21
%              Number of atoms          :  633 (7985 expanded)
%              Number of equality atoms :  215 (2007 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X0)
                   => ( ( k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
                        & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                      | X3 = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( r3_wellord1(X0,X1,X2)
                 => ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                     => ( ( k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
                          & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                        | X3 = X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3,X4] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3,X4] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3,X4] :
          ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
          & X3 != X4
          & r2_hidden(k4_tarski(X3,X4),X0) )
     => ( ( k1_funct_1(X2,sK8) = k1_funct_1(X2,sK9)
          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK8),k1_funct_1(X2,sK9)),X1) )
        & sK8 != sK9
        & r2_hidden(k4_tarski(sK8,sK9),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3,X4] :
              ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
              & X3 != X4
              & r2_hidden(k4_tarski(X3,X4),X0) )
          & r3_wellord1(X0,X1,X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ? [X4,X3] :
            ( ( k1_funct_1(sK7,X3) = k1_funct_1(sK7,X4)
              | ~ r2_hidden(k4_tarski(k1_funct_1(sK7,X3),k1_funct_1(sK7,X4)),X1) )
            & X3 != X4
            & r2_hidden(k4_tarski(X3,X4),X0) )
        & r3_wellord1(X0,X1,sK7)
        & v1_funct_1(sK7)
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3,X4] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ? [X4,X3] :
                ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                  | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK6) )
                & X3 != X4
                & r2_hidden(k4_tarski(X3,X4),X0) )
            & r3_wellord1(X0,sK6,X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3,X4] :
                    ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                      | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                    & X3 != X4
                    & r2_hidden(k4_tarski(X3,X4),X0) )
                & r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X4,X3] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),sK5) )
              & r3_wellord1(sK5,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9)
      | ~ r2_hidden(k4_tarski(k1_funct_1(sK7,sK8),k1_funct_1(sK7,sK9)),sK6) )
    & sK8 != sK9
    & r2_hidden(k4_tarski(sK8,sK9),sK5)
    & r3_wellord1(sK5,sK6,sK7)
    & v1_funct_1(sK7)
    & v1_relat_1(sK7)
    & v1_relat_1(sK6)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f23,f42,f41,f40,f39])).

fof(f75,plain,(
    r2_hidden(k4_tarski(sK8,sK9),sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k3_relat_1(X0) = k1_relat_1(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k3_relat_1(X0) = k1_relat_1(X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k3_relat_1(X0) = k1_relat_1(X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,(
    ! [X0,X2,X1] :
      ( ( r3_wellord1(X0,X1,X2)
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ( ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X0)
          <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              & r2_hidden(X4,k3_relat_1(X0))
              & r2_hidden(X3,k3_relat_1(X0)) ) )
        & v2_funct_1(X2)
        & k2_relat_1(X2) = k3_relat_1(X1)
        & k3_relat_1(X0) = k1_relat_1(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f21,f25,f24])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f32,plain,(
    ! [X0,X2,X1] :
      ( ( ( r3_wellord1(X0,X1,X2)
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r3_wellord1(X0,X1,X2) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_wellord1(X0,X2,X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r3_wellord1(X0,X2,X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f32])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | ~ r3_wellord1(X0,X2,X1)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    r3_wellord1(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f34,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0))
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                & r2_hidden(X4,k3_relat_1(X0))
                & r2_hidden(X3,k3_relat_1(X0)) )
              | r2_hidden(k4_tarski(X3,X4),X0) ) )
        | ~ v2_funct_1(X2)
        | k2_relat_1(X2) != k3_relat_1(X1)
        | k3_relat_1(X0) != k1_relat_1(X2) )
      & ( ( ! [X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                | ~ r2_hidden(X4,k3_relat_1(X0))
                | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                  & r2_hidden(X4,k3_relat_1(X0))
                  & r2_hidden(X3,k3_relat_1(X0)) )
                | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
          & v2_funct_1(X2)
          & k2_relat_1(X2) = k3_relat_1(X1)
          & k3_relat_1(X0) = k1_relat_1(X2) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0))
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                & r2_hidden(X4,k3_relat_1(X0))
                & r2_hidden(X3,k3_relat_1(X0)) )
              | r2_hidden(k4_tarski(X3,X4),X0) ) )
        | ~ v2_funct_1(X2)
        | k2_relat_1(X2) != k3_relat_1(X1)
        | k3_relat_1(X0) != k1_relat_1(X2) )
      & ( ( ! [X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                | ~ r2_hidden(X4,k3_relat_1(X0))
                | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                  & r2_hidden(X4,k3_relat_1(X0))
                  & r2_hidden(X3,k3_relat_1(X0)) )
                | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
          & v2_funct_1(X2)
          & k2_relat_1(X2) = k3_relat_1(X1)
          & k3_relat_1(X0) = k1_relat_1(X2) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
              | ~ r2_hidden(X4,k3_relat_1(X2))
              | ~ r2_hidden(X3,k3_relat_1(X2))
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
                & r2_hidden(X4,k3_relat_1(X2))
                & r2_hidden(X3,k3_relat_1(X2)) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) )
        | ~ v2_funct_1(X1)
        | k2_relat_1(X1) != k3_relat_1(X0)
        | k3_relat_1(X2) != k1_relat_1(X1) )
      & ( ( ! [X5,X6] :
              ( ( r2_hidden(k4_tarski(X5,X6),X2)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                | ~ r2_hidden(X6,k3_relat_1(X2))
                | ~ r2_hidden(X5,k3_relat_1(X2)) )
              & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                  & r2_hidden(X6,k3_relat_1(X2))
                  & r2_hidden(X5,k3_relat_1(X2)) )
                | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
          & v2_funct_1(X1)
          & k2_relat_1(X1) = k3_relat_1(X0)
          & k3_relat_1(X2) = k1_relat_1(X1) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
            | ~ r2_hidden(X4,k3_relat_1(X2))
            | ~ r2_hidden(X3,k3_relat_1(X2))
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
              & r2_hidden(X4,k3_relat_1(X2))
              & r2_hidden(X3,k3_relat_1(X2)) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,sK3(X0,X1,X2)),k1_funct_1(X1,sK4(X0,X1,X2))),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),k3_relat_1(X2))
          | ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,sK3(X0,X1,X2)),k1_funct_1(X1,sK4(X0,X1,X2))),X0)
            & r2_hidden(sK4(X0,X1,X2),k3_relat_1(X2))
            & r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2)) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,sK3(X0,X1,X2)),k1_funct_1(X1,sK4(X0,X1,X2))),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),k3_relat_1(X2))
            | ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
            | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
          & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,sK3(X0,X1,X2)),k1_funct_1(X1,sK4(X0,X1,X2))),X0)
              & r2_hidden(sK4(X0,X1,X2),k3_relat_1(X2))
              & r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2)) )
            | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) )
        | ~ v2_funct_1(X1)
        | k2_relat_1(X1) != k3_relat_1(X0)
        | k3_relat_1(X2) != k1_relat_1(X1) )
      & ( ( ! [X5,X6] :
              ( ( r2_hidden(k4_tarski(X5,X6),X2)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                | ~ r2_hidden(X6,k3_relat_1(X2))
                | ~ r2_hidden(X5,k3_relat_1(X2)) )
              & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                  & r2_hidden(X6,k3_relat_1(X2))
                  & r2_hidden(X5,k3_relat_1(X2)) )
                | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
          & v2_funct_1(X1)
          & k2_relat_1(X1) = k3_relat_1(X0)
          & k3_relat_1(X2) = k1_relat_1(X1) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f37])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X2) = k1_relat_1(X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f63,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,
    ( k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9)
    | ~ r2_hidden(k4_tarski(k1_funct_1(sK7,sK8),k1_funct_1(sK7,sK9)),sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f46])).

fof(f79,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f78])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f76,plain,(
    sK8 != sK9 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(k4_tarski(sK8,sK9),sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3162,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_33,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_597,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_33])).

cnf(c_598,plain,
    ( r2_hidden(X0,k3_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_3154,plain,
    ( r2_hidden(X0,k3_relat_1(sK5)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_598])).

cnf(c_3474,plain,
    ( r2_hidden(sK9,k3_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3162,c_3154])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3176,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4251,plain,
    ( k4_xboole_0(k1_tarski(sK9),k3_relat_1(sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3474,c_3176])).

cnf(c_25,plain,
    ( sP1(X0,X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_13,plain,
    ( ~ sP1(X0,X1,X2)
    | sP0(X2,X1,X0)
    | ~ r3_wellord1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_29,negated_conjecture,
    ( r3_wellord1(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_469,plain,
    ( ~ sP1(X0,X1,X2)
    | sP0(X2,X1,X0)
    | sK5 != X0
    | sK6 != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_470,plain,
    ( ~ sP1(sK5,sK7,sK6)
    | sP0(sK6,sK7,sK5) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_482,plain,
    ( sP0(sK6,sK7,sK5)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | sK5 != X1
    | sK6 != X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_470])).

cnf(c_483,plain,
    ( sP0(sK6,sK7,sK5)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_32,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_485,plain,
    ( sP0(sK6,sK7,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_33,c_32,c_31,c_30])).

cnf(c_3161,plain,
    ( sP0(sK6,sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_24,plain,
    ( ~ sP0(X0,X1,X2)
    | k1_relat_1(X1) = k3_relat_1(X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3164,plain,
    ( k1_relat_1(X0) = k3_relat_1(X1)
    | sP0(X2,X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4147,plain,
    ( k1_relat_1(sK7) = k3_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_3161,c_3164])).

cnf(c_22,plain,
    ( ~ sP0(X0,X1,X2)
    | v2_funct_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1250,plain,
    ( v2_funct_1(X0)
    | sK5 != X1
    | sK6 != X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_485])).

cnf(c_1251,plain,
    ( v2_funct_1(sK7) ),
    inference(unflattening,[status(thm)],[c_1250])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_441,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
    | k4_xboole_0(X2,X3) != k1_xboole_0
    | k1_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_442,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
    | k4_xboole_0(X1,k1_relat_1(X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_513,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
    | k4_xboole_0(X1,k1_relat_1(X0)) != k1_xboole_0
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_442])).

cnf(c_514,plain,
    ( ~ v2_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | k10_relat_1(sK7,k9_relat_1(sK7,X0)) = X0
    | k4_xboole_0(X0,k1_relat_1(sK7)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_518,plain,
    ( ~ v2_funct_1(sK7)
    | k10_relat_1(sK7,k9_relat_1(sK7,X0)) = X0
    | k4_xboole_0(X0,k1_relat_1(sK7)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_31])).

cnf(c_1411,plain,
    ( k10_relat_1(sK7,k9_relat_1(sK7,X0)) = X0
    | k4_xboole_0(X0,k1_relat_1(sK7)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1251,c_518])).

cnf(c_4675,plain,
    ( k10_relat_1(sK7,k9_relat_1(sK7,X0)) = X0
    | k4_xboole_0(X0,k3_relat_1(sK5)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4147,c_1411])).

cnf(c_4769,plain,
    ( k10_relat_1(sK7,k9_relat_1(sK7,k1_tarski(sK9))) = k1_tarski(sK9) ),
    inference(superposition,[status(thm)],[c_4251,c_4675])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_495,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_30])).

cnf(c_496,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | k2_relat_1(k7_relat_1(sK7,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK7,X0)) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_500,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | k2_relat_1(k7_relat_1(sK7,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK7,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_496,c_31])).

cnf(c_3160,plain,
    ( k2_relat_1(k7_relat_1(sK7,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK7,X0))
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_607,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_31])).

cnf(c_608,plain,
    ( k2_relat_1(k7_relat_1(sK7,X0)) = k9_relat_1(sK7,X0) ),
    inference(unflattening,[status(thm)],[c_607])).

cnf(c_3247,plain,
    ( k9_relat_1(sK7,k1_tarski(X0)) = k1_tarski(k1_funct_1(sK7,X0))
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3160,c_608])).

cnf(c_4674,plain,
    ( k9_relat_1(sK7,k1_tarski(X0)) = k1_tarski(k1_funct_1(sK7,X0))
    | r2_hidden(X0,k3_relat_1(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4147,c_3247])).

cnf(c_4779,plain,
    ( k9_relat_1(sK7,k1_tarski(sK9)) = k1_tarski(k1_funct_1(sK7,sK9)) ),
    inference(superposition,[status(thm)],[c_3474,c_4674])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X2)
    | r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3169,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(k4_tarski(X3,X4),X2) != iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4978,plain,
    ( sP0(X0,X1,sK5) != iProver_top
    | r2_hidden(k4_tarski(k1_funct_1(X1,sK8),k1_funct_1(X1,sK9)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3162,c_3169])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(sK7,sK8),k1_funct_1(sK7,sK9)),sK6)
    | k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3163,plain,
    ( k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9)
    | r2_hidden(k4_tarski(k1_funct_1(sK7,sK8),k1_funct_1(sK7,sK9)),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5237,plain,
    ( k1_funct_1(sK7,sK9) = k1_funct_1(sK7,sK8)
    | sP0(sK6,sK7,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4978,c_3163])).

cnf(c_34,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_35,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_36,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_37,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_484,plain,
    ( sP0(sK6,sK7,sK5) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_5667,plain,
    ( k1_funct_1(sK7,sK9) = k1_funct_1(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5237,c_34,c_35,c_36,c_37,c_484])).

cnf(c_5812,plain,
    ( k9_relat_1(sK7,k1_tarski(sK9)) = k1_tarski(k1_funct_1(sK7,sK8)) ),
    inference(light_normalisation,[status(thm)],[c_4779,c_5667])).

cnf(c_9,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_585,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_33])).

cnf(c_586,plain,
    ( r2_hidden(X0,k3_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(X0,X1),sK5) ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_3155,plain,
    ( r2_hidden(X0,k3_relat_1(sK5)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_3523,plain,
    ( r2_hidden(sK8,k3_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3162,c_3155])).

cnf(c_4250,plain,
    ( k4_xboole_0(k1_tarski(sK8),k3_relat_1(sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3523,c_3176])).

cnf(c_4768,plain,
    ( k10_relat_1(sK7,k9_relat_1(sK7,k1_tarski(sK8))) = k1_tarski(sK8) ),
    inference(superposition,[status(thm)],[c_4250,c_4675])).

cnf(c_4778,plain,
    ( k9_relat_1(sK7,k1_tarski(sK8)) = k1_tarski(k1_funct_1(sK7,sK8)) ),
    inference(superposition,[status(thm)],[c_3523,c_4674])).

cnf(c_9095,plain,
    ( k10_relat_1(sK7,k1_tarski(k1_funct_1(sK7,sK8))) = k1_tarski(sK8) ),
    inference(light_normalisation,[status(thm)],[c_4768,c_4778])).

cnf(c_9189,plain,
    ( k1_tarski(sK8) = k1_tarski(sK9) ),
    inference(light_normalisation,[status(thm)],[c_4769,c_5812,c_9095])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3178,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9196,plain,
    ( r2_hidden(sK9,k1_tarski(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9189,c_3178])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3177,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9654,plain,
    ( sK9 = sK8 ),
    inference(superposition,[status(thm)],[c_9196,c_3177])).

cnf(c_2526,plain,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1) ),
    theory(equality)).

cnf(c_8509,plain,
    ( k1_tarski(sK9) = k1_tarski(sK8)
    | sK9 != sK8 ),
    inference(instantiation,[status(thm)],[c_2526])).

cnf(c_5709,plain,
    ( r2_hidden(sK8,k1_tarski(sK8)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2527,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3456,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_tarski(X2))
    | X0 != X2
    | X1 != k1_tarski(X2) ),
    inference(instantiation,[status(thm)],[c_2527])).

cnf(c_3640,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(X1,k1_tarski(X2))
    | X1 != X0
    | k1_tarski(X2) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_3456])).

cnf(c_3961,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(sK8,k1_tarski(sK9))
    | k1_tarski(sK9) != k1_tarski(X0)
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_3640])).

cnf(c_4198,plain,
    ( r2_hidden(sK8,k1_tarski(sK9))
    | ~ r2_hidden(sK8,k1_tarski(sK8))
    | k1_tarski(sK9) != k1_tarski(sK8)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_3961])).

cnf(c_2523,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3747,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_2523])).

cnf(c_3415,plain,
    ( ~ r2_hidden(sK8,k1_tarski(sK9))
    | sK8 = sK9 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_27,negated_conjecture,
    ( sK8 != sK9 ),
    inference(cnf_transformation,[],[f76])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9654,c_8509,c_5709,c_4198,c_3747,c_3415,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:34:22 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 3.38/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/0.98  
% 3.38/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.38/0.98  
% 3.38/0.98  ------  iProver source info
% 3.38/0.98  
% 3.38/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.38/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.38/0.98  git: non_committed_changes: false
% 3.38/0.98  git: last_make_outside_of_git: false
% 3.38/0.98  
% 3.38/0.98  ------ 
% 3.38/0.98  
% 3.38/0.98  ------ Input Options
% 3.38/0.98  
% 3.38/0.98  --out_options                           all
% 3.38/0.98  --tptp_safe_out                         true
% 3.38/0.98  --problem_path                          ""
% 3.38/0.98  --include_path                          ""
% 3.38/0.98  --clausifier                            res/vclausify_rel
% 3.38/0.98  --clausifier_options                    --mode clausify
% 3.38/0.98  --stdin                                 false
% 3.38/0.98  --stats_out                             all
% 3.38/0.98  
% 3.38/0.98  ------ General Options
% 3.38/0.98  
% 3.38/0.98  --fof                                   false
% 3.38/0.98  --time_out_real                         305.
% 3.38/0.98  --time_out_virtual                      -1.
% 3.38/0.98  --symbol_type_check                     false
% 3.38/0.98  --clausify_out                          false
% 3.38/0.98  --sig_cnt_out                           false
% 3.38/0.98  --trig_cnt_out                          false
% 3.38/0.98  --trig_cnt_out_tolerance                1.
% 3.38/0.98  --trig_cnt_out_sk_spl                   false
% 3.38/0.98  --abstr_cl_out                          false
% 3.38/0.98  
% 3.38/0.98  ------ Global Options
% 3.38/0.98  
% 3.38/0.98  --schedule                              default
% 3.38/0.98  --add_important_lit                     false
% 3.38/0.98  --prop_solver_per_cl                    1000
% 3.38/0.98  --min_unsat_core                        false
% 3.38/0.98  --soft_assumptions                      false
% 3.38/0.98  --soft_lemma_size                       3
% 3.38/0.98  --prop_impl_unit_size                   0
% 3.38/0.98  --prop_impl_unit                        []
% 3.38/0.98  --share_sel_clauses                     true
% 3.38/0.98  --reset_solvers                         false
% 3.38/0.98  --bc_imp_inh                            [conj_cone]
% 3.38/0.98  --conj_cone_tolerance                   3.
% 3.38/0.98  --extra_neg_conj                        none
% 3.38/0.98  --large_theory_mode                     true
% 3.38/0.98  --prolific_symb_bound                   200
% 3.38/0.98  --lt_threshold                          2000
% 3.38/0.98  --clause_weak_htbl                      true
% 3.38/0.98  --gc_record_bc_elim                     false
% 3.38/0.98  
% 3.38/0.98  ------ Preprocessing Options
% 3.38/0.98  
% 3.38/0.98  --preprocessing_flag                    true
% 3.38/0.98  --time_out_prep_mult                    0.1
% 3.38/0.98  --splitting_mode                        input
% 3.38/0.98  --splitting_grd                         true
% 3.38/0.98  --splitting_cvd                         false
% 3.38/0.98  --splitting_cvd_svl                     false
% 3.38/0.98  --splitting_nvd                         32
% 3.38/0.98  --sub_typing                            true
% 3.38/0.98  --prep_gs_sim                           true
% 3.38/0.98  --prep_unflatten                        true
% 3.38/0.98  --prep_res_sim                          true
% 3.38/0.98  --prep_upred                            true
% 3.38/0.98  --prep_sem_filter                       exhaustive
% 3.38/0.98  --prep_sem_filter_out                   false
% 3.38/0.98  --pred_elim                             true
% 3.38/0.98  --res_sim_input                         true
% 3.38/0.98  --eq_ax_congr_red                       true
% 3.38/0.98  --pure_diseq_elim                       true
% 3.38/0.98  --brand_transform                       false
% 3.38/0.98  --non_eq_to_eq                          false
% 3.38/0.98  --prep_def_merge                        true
% 3.38/0.98  --prep_def_merge_prop_impl              false
% 3.38/0.98  --prep_def_merge_mbd                    true
% 3.38/0.98  --prep_def_merge_tr_red                 false
% 3.38/0.98  --prep_def_merge_tr_cl                  false
% 3.38/0.98  --smt_preprocessing                     true
% 3.38/0.98  --smt_ac_axioms                         fast
% 3.38/0.98  --preprocessed_out                      false
% 3.38/0.98  --preprocessed_stats                    false
% 3.38/0.98  
% 3.38/0.98  ------ Abstraction refinement Options
% 3.38/0.98  
% 3.38/0.98  --abstr_ref                             []
% 3.38/0.98  --abstr_ref_prep                        false
% 3.38/0.98  --abstr_ref_until_sat                   false
% 3.38/0.98  --abstr_ref_sig_restrict                funpre
% 3.38/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.38/0.98  --abstr_ref_under                       []
% 3.38/0.98  
% 3.38/0.98  ------ SAT Options
% 3.38/0.98  
% 3.38/0.98  --sat_mode                              false
% 3.38/0.98  --sat_fm_restart_options                ""
% 3.38/0.98  --sat_gr_def                            false
% 3.38/0.98  --sat_epr_types                         true
% 3.38/0.98  --sat_non_cyclic_types                  false
% 3.38/0.98  --sat_finite_models                     false
% 3.38/0.98  --sat_fm_lemmas                         false
% 3.38/0.98  --sat_fm_prep                           false
% 3.38/0.98  --sat_fm_uc_incr                        true
% 3.38/0.98  --sat_out_model                         small
% 3.38/0.98  --sat_out_clauses                       false
% 3.38/0.98  
% 3.38/0.98  ------ QBF Options
% 3.38/0.98  
% 3.38/0.98  --qbf_mode                              false
% 3.38/0.98  --qbf_elim_univ                         false
% 3.38/0.98  --qbf_dom_inst                          none
% 3.38/0.98  --qbf_dom_pre_inst                      false
% 3.38/0.98  --qbf_sk_in                             false
% 3.38/0.98  --qbf_pred_elim                         true
% 3.38/0.98  --qbf_split                             512
% 3.38/0.98  
% 3.38/0.98  ------ BMC1 Options
% 3.38/0.98  
% 3.38/0.98  --bmc1_incremental                      false
% 3.38/0.98  --bmc1_axioms                           reachable_all
% 3.38/0.98  --bmc1_min_bound                        0
% 3.38/0.98  --bmc1_max_bound                        -1
% 3.38/0.98  --bmc1_max_bound_default                -1
% 3.38/0.98  --bmc1_symbol_reachability              true
% 3.38/0.98  --bmc1_property_lemmas                  false
% 3.38/0.98  --bmc1_k_induction                      false
% 3.38/0.98  --bmc1_non_equiv_states                 false
% 3.38/0.98  --bmc1_deadlock                         false
% 3.38/0.98  --bmc1_ucm                              false
% 3.38/0.98  --bmc1_add_unsat_core                   none
% 3.38/0.98  --bmc1_unsat_core_children              false
% 3.38/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.38/0.98  --bmc1_out_stat                         full
% 3.38/0.98  --bmc1_ground_init                      false
% 3.38/0.98  --bmc1_pre_inst_next_state              false
% 3.38/0.98  --bmc1_pre_inst_state                   false
% 3.38/0.98  --bmc1_pre_inst_reach_state             false
% 3.38/0.98  --bmc1_out_unsat_core                   false
% 3.38/0.98  --bmc1_aig_witness_out                  false
% 3.38/0.98  --bmc1_verbose                          false
% 3.38/0.98  --bmc1_dump_clauses_tptp                false
% 3.38/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.38/0.98  --bmc1_dump_file                        -
% 3.38/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.38/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.38/0.98  --bmc1_ucm_extend_mode                  1
% 3.38/0.98  --bmc1_ucm_init_mode                    2
% 3.38/0.98  --bmc1_ucm_cone_mode                    none
% 3.38/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.38/0.98  --bmc1_ucm_relax_model                  4
% 3.38/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.38/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.38/0.98  --bmc1_ucm_layered_model                none
% 3.38/0.98  --bmc1_ucm_max_lemma_size               10
% 3.38/0.98  
% 3.38/0.98  ------ AIG Options
% 3.38/0.98  
% 3.38/0.98  --aig_mode                              false
% 3.38/0.98  
% 3.38/0.98  ------ Instantiation Options
% 3.38/0.98  
% 3.38/0.98  --instantiation_flag                    true
% 3.38/0.98  --inst_sos_flag                         false
% 3.38/0.98  --inst_sos_phase                        true
% 3.38/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.38/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.38/0.98  --inst_lit_sel_side                     num_symb
% 3.38/0.98  --inst_solver_per_active                1400
% 3.38/0.98  --inst_solver_calls_frac                1.
% 3.38/0.98  --inst_passive_queue_type               priority_queues
% 3.38/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.38/0.98  --inst_passive_queues_freq              [25;2]
% 3.38/0.98  --inst_dismatching                      true
% 3.38/0.98  --inst_eager_unprocessed_to_passive     true
% 3.38/0.98  --inst_prop_sim_given                   true
% 3.38/0.98  --inst_prop_sim_new                     false
% 3.38/0.98  --inst_subs_new                         false
% 3.38/0.98  --inst_eq_res_simp                      false
% 3.38/0.98  --inst_subs_given                       false
% 3.38/0.98  --inst_orphan_elimination               true
% 3.38/0.98  --inst_learning_loop_flag               true
% 3.38/0.98  --inst_learning_start                   3000
% 3.38/0.98  --inst_learning_factor                  2
% 3.38/0.98  --inst_start_prop_sim_after_learn       3
% 3.38/0.98  --inst_sel_renew                        solver
% 3.38/0.98  --inst_lit_activity_flag                true
% 3.38/0.98  --inst_restr_to_given                   false
% 3.38/0.98  --inst_activity_threshold               500
% 3.38/0.98  --inst_out_proof                        true
% 3.38/0.98  
% 3.38/0.98  ------ Resolution Options
% 3.38/0.98  
% 3.38/0.98  --resolution_flag                       true
% 3.38/0.98  --res_lit_sel                           adaptive
% 3.38/0.98  --res_lit_sel_side                      none
% 3.38/0.98  --res_ordering                          kbo
% 3.38/0.98  --res_to_prop_solver                    active
% 3.38/0.98  --res_prop_simpl_new                    false
% 3.38/0.98  --res_prop_simpl_given                  true
% 3.38/0.98  --res_passive_queue_type                priority_queues
% 3.38/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.38/0.98  --res_passive_queues_freq               [15;5]
% 3.38/0.98  --res_forward_subs                      full
% 3.38/0.98  --res_backward_subs                     full
% 3.38/0.98  --res_forward_subs_resolution           true
% 3.38/0.98  --res_backward_subs_resolution          true
% 3.38/0.98  --res_orphan_elimination                true
% 3.38/0.98  --res_time_limit                        2.
% 3.38/0.98  --res_out_proof                         true
% 3.38/0.98  
% 3.38/0.98  ------ Superposition Options
% 3.38/0.98  
% 3.38/0.98  --superposition_flag                    true
% 3.38/0.98  --sup_passive_queue_type                priority_queues
% 3.38/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.38/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.38/0.98  --demod_completeness_check              fast
% 3.38/0.98  --demod_use_ground                      true
% 3.38/0.98  --sup_to_prop_solver                    passive
% 3.38/0.98  --sup_prop_simpl_new                    true
% 3.38/0.98  --sup_prop_simpl_given                  true
% 3.38/0.98  --sup_fun_splitting                     false
% 3.38/0.98  --sup_smt_interval                      50000
% 3.38/0.98  
% 3.38/0.98  ------ Superposition Simplification Setup
% 3.38/0.98  
% 3.38/0.98  --sup_indices_passive                   []
% 3.38/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.38/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.98  --sup_full_bw                           [BwDemod]
% 3.38/0.98  --sup_immed_triv                        [TrivRules]
% 3.38/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.98  --sup_immed_bw_main                     []
% 3.38/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.38/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/0.98  
% 3.38/0.98  ------ Combination Options
% 3.38/0.98  
% 3.38/0.98  --comb_res_mult                         3
% 3.38/0.98  --comb_sup_mult                         2
% 3.38/0.98  --comb_inst_mult                        10
% 3.38/0.98  
% 3.38/0.98  ------ Debug Options
% 3.38/0.98  
% 3.38/0.98  --dbg_backtrace                         false
% 3.38/0.98  --dbg_dump_prop_clauses                 false
% 3.38/0.98  --dbg_dump_prop_clauses_file            -
% 3.38/0.98  --dbg_out_stat                          false
% 3.38/0.98  ------ Parsing...
% 3.38/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.38/0.98  
% 3.38/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.38/0.98  
% 3.38/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.38/0.98  
% 3.38/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.38/0.98  ------ Proving...
% 3.38/0.98  ------ Problem Properties 
% 3.38/0.98  
% 3.38/0.98  
% 3.38/0.98  clauses                                 32
% 3.38/0.98  conjectures                             3
% 3.38/0.98  EPR                                     3
% 3.38/0.98  Horn                                    28
% 3.38/0.98  unary                                   7
% 3.38/0.98  binary                                  15
% 3.38/0.98  lits                                    83
% 3.38/0.98  lits eq                                 25
% 3.38/0.98  fd_pure                                 0
% 3.38/0.98  fd_pseudo                               0
% 3.38/0.98  fd_cond                                 0
% 3.38/0.98  fd_pseudo_cond                          2
% 3.38/0.98  AC symbols                              0
% 3.38/0.98  
% 3.38/0.98  ------ Schedule dynamic 5 is on 
% 3.38/0.98  
% 3.38/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.38/0.98  
% 3.38/0.98  
% 3.38/0.98  ------ 
% 3.38/0.98  Current options:
% 3.38/0.98  ------ 
% 3.38/0.98  
% 3.38/0.98  ------ Input Options
% 3.38/0.98  
% 3.38/0.98  --out_options                           all
% 3.38/0.98  --tptp_safe_out                         true
% 3.38/0.98  --problem_path                          ""
% 3.38/0.98  --include_path                          ""
% 3.38/0.98  --clausifier                            res/vclausify_rel
% 3.38/0.98  --clausifier_options                    --mode clausify
% 3.38/0.98  --stdin                                 false
% 3.38/0.98  --stats_out                             all
% 3.38/0.98  
% 3.38/0.98  ------ General Options
% 3.38/0.98  
% 3.38/0.98  --fof                                   false
% 3.38/0.98  --time_out_real                         305.
% 3.38/0.98  --time_out_virtual                      -1.
% 3.38/0.98  --symbol_type_check                     false
% 3.38/0.98  --clausify_out                          false
% 3.38/0.98  --sig_cnt_out                           false
% 3.38/0.98  --trig_cnt_out                          false
% 3.38/0.98  --trig_cnt_out_tolerance                1.
% 3.38/0.98  --trig_cnt_out_sk_spl                   false
% 3.38/0.98  --abstr_cl_out                          false
% 3.38/0.98  
% 3.38/0.98  ------ Global Options
% 3.38/0.98  
% 3.38/0.98  --schedule                              default
% 3.38/0.98  --add_important_lit                     false
% 3.38/0.98  --prop_solver_per_cl                    1000
% 3.38/0.98  --min_unsat_core                        false
% 3.38/0.98  --soft_assumptions                      false
% 3.38/0.98  --soft_lemma_size                       3
% 3.38/0.98  --prop_impl_unit_size                   0
% 3.38/0.98  --prop_impl_unit                        []
% 3.38/0.98  --share_sel_clauses                     true
% 3.38/0.98  --reset_solvers                         false
% 3.38/0.98  --bc_imp_inh                            [conj_cone]
% 3.38/0.98  --conj_cone_tolerance                   3.
% 3.38/0.98  --extra_neg_conj                        none
% 3.38/0.98  --large_theory_mode                     true
% 3.38/0.98  --prolific_symb_bound                   200
% 3.38/0.98  --lt_threshold                          2000
% 3.38/0.98  --clause_weak_htbl                      true
% 3.38/0.98  --gc_record_bc_elim                     false
% 3.38/0.98  
% 3.38/0.98  ------ Preprocessing Options
% 3.38/0.98  
% 3.38/0.98  --preprocessing_flag                    true
% 3.38/0.98  --time_out_prep_mult                    0.1
% 3.38/0.98  --splitting_mode                        input
% 3.38/0.98  --splitting_grd                         true
% 3.38/0.98  --splitting_cvd                         false
% 3.38/0.98  --splitting_cvd_svl                     false
% 3.38/0.98  --splitting_nvd                         32
% 3.38/0.98  --sub_typing                            true
% 3.38/0.98  --prep_gs_sim                           true
% 3.38/0.98  --prep_unflatten                        true
% 3.38/0.98  --prep_res_sim                          true
% 3.38/0.98  --prep_upred                            true
% 3.38/0.98  --prep_sem_filter                       exhaustive
% 3.38/0.98  --prep_sem_filter_out                   false
% 3.38/0.98  --pred_elim                             true
% 3.38/0.98  --res_sim_input                         true
% 3.38/0.98  --eq_ax_congr_red                       true
% 3.38/0.98  --pure_diseq_elim                       true
% 3.38/0.98  --brand_transform                       false
% 3.38/0.98  --non_eq_to_eq                          false
% 3.38/0.98  --prep_def_merge                        true
% 3.38/0.98  --prep_def_merge_prop_impl              false
% 3.38/0.98  --prep_def_merge_mbd                    true
% 3.38/0.98  --prep_def_merge_tr_red                 false
% 3.38/0.98  --prep_def_merge_tr_cl                  false
% 3.38/0.98  --smt_preprocessing                     true
% 3.38/0.98  --smt_ac_axioms                         fast
% 3.38/0.98  --preprocessed_out                      false
% 3.38/0.98  --preprocessed_stats                    false
% 3.38/0.98  
% 3.38/0.98  ------ Abstraction refinement Options
% 3.38/0.98  
% 3.38/0.98  --abstr_ref                             []
% 3.38/0.98  --abstr_ref_prep                        false
% 3.38/0.98  --abstr_ref_until_sat                   false
% 3.38/0.98  --abstr_ref_sig_restrict                funpre
% 3.38/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.38/0.98  --abstr_ref_under                       []
% 3.38/0.98  
% 3.38/0.98  ------ SAT Options
% 3.38/0.98  
% 3.38/0.98  --sat_mode                              false
% 3.38/0.98  --sat_fm_restart_options                ""
% 3.38/0.98  --sat_gr_def                            false
% 3.38/0.98  --sat_epr_types                         true
% 3.38/0.98  --sat_non_cyclic_types                  false
% 3.38/0.98  --sat_finite_models                     false
% 3.38/0.98  --sat_fm_lemmas                         false
% 3.38/0.98  --sat_fm_prep                           false
% 3.38/0.98  --sat_fm_uc_incr                        true
% 3.38/0.98  --sat_out_model                         small
% 3.38/0.98  --sat_out_clauses                       false
% 3.38/0.98  
% 3.38/0.98  ------ QBF Options
% 3.38/0.98  
% 3.38/0.98  --qbf_mode                              false
% 3.38/0.98  --qbf_elim_univ                         false
% 3.38/0.98  --qbf_dom_inst                          none
% 3.38/0.98  --qbf_dom_pre_inst                      false
% 3.38/0.98  --qbf_sk_in                             false
% 3.38/0.98  --qbf_pred_elim                         true
% 3.38/0.98  --qbf_split                             512
% 3.38/0.98  
% 3.38/0.98  ------ BMC1 Options
% 3.38/0.98  
% 3.38/0.98  --bmc1_incremental                      false
% 3.38/0.98  --bmc1_axioms                           reachable_all
% 3.38/0.98  --bmc1_min_bound                        0
% 3.38/0.98  --bmc1_max_bound                        -1
% 3.38/0.98  --bmc1_max_bound_default                -1
% 3.38/0.98  --bmc1_symbol_reachability              true
% 3.38/0.98  --bmc1_property_lemmas                  false
% 3.38/0.98  --bmc1_k_induction                      false
% 3.38/0.98  --bmc1_non_equiv_states                 false
% 3.38/0.98  --bmc1_deadlock                         false
% 3.38/0.98  --bmc1_ucm                              false
% 3.38/0.98  --bmc1_add_unsat_core                   none
% 3.38/0.98  --bmc1_unsat_core_children              false
% 3.38/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.38/0.98  --bmc1_out_stat                         full
% 3.38/0.98  --bmc1_ground_init                      false
% 3.38/0.98  --bmc1_pre_inst_next_state              false
% 3.38/0.98  --bmc1_pre_inst_state                   false
% 3.38/0.98  --bmc1_pre_inst_reach_state             false
% 3.38/0.98  --bmc1_out_unsat_core                   false
% 3.38/0.98  --bmc1_aig_witness_out                  false
% 3.38/0.98  --bmc1_verbose                          false
% 3.38/0.98  --bmc1_dump_clauses_tptp                false
% 3.38/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.38/0.98  --bmc1_dump_file                        -
% 3.38/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.38/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.38/0.98  --bmc1_ucm_extend_mode                  1
% 3.38/0.98  --bmc1_ucm_init_mode                    2
% 3.38/0.98  --bmc1_ucm_cone_mode                    none
% 3.38/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.38/0.98  --bmc1_ucm_relax_model                  4
% 3.38/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.38/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.38/0.98  --bmc1_ucm_layered_model                none
% 3.38/0.98  --bmc1_ucm_max_lemma_size               10
% 3.38/0.98  
% 3.38/0.98  ------ AIG Options
% 3.38/0.98  
% 3.38/0.98  --aig_mode                              false
% 3.38/0.98  
% 3.38/0.98  ------ Instantiation Options
% 3.38/0.98  
% 3.38/0.98  --instantiation_flag                    true
% 3.38/0.98  --inst_sos_flag                         false
% 3.38/0.98  --inst_sos_phase                        true
% 3.38/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.38/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.38/0.98  --inst_lit_sel_side                     none
% 3.38/0.98  --inst_solver_per_active                1400
% 3.38/0.98  --inst_solver_calls_frac                1.
% 3.38/0.98  --inst_passive_queue_type               priority_queues
% 3.38/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.38/0.98  --inst_passive_queues_freq              [25;2]
% 3.38/0.98  --inst_dismatching                      true
% 3.38/0.98  --inst_eager_unprocessed_to_passive     true
% 3.38/0.98  --inst_prop_sim_given                   true
% 3.38/0.98  --inst_prop_sim_new                     false
% 3.38/0.98  --inst_subs_new                         false
% 3.38/0.98  --inst_eq_res_simp                      false
% 3.38/0.98  --inst_subs_given                       false
% 3.38/0.98  --inst_orphan_elimination               true
% 3.38/0.98  --inst_learning_loop_flag               true
% 3.38/0.98  --inst_learning_start                   3000
% 3.38/0.98  --inst_learning_factor                  2
% 3.38/0.98  --inst_start_prop_sim_after_learn       3
% 3.38/0.98  --inst_sel_renew                        solver
% 3.38/0.98  --inst_lit_activity_flag                true
% 3.38/0.98  --inst_restr_to_given                   false
% 3.38/0.98  --inst_activity_threshold               500
% 3.38/0.98  --inst_out_proof                        true
% 3.38/0.98  
% 3.38/0.98  ------ Resolution Options
% 3.38/0.98  
% 3.38/0.98  --resolution_flag                       false
% 3.38/0.98  --res_lit_sel                           adaptive
% 3.38/0.98  --res_lit_sel_side                      none
% 3.38/0.98  --res_ordering                          kbo
% 3.38/0.98  --res_to_prop_solver                    active
% 3.38/0.98  --res_prop_simpl_new                    false
% 3.38/0.98  --res_prop_simpl_given                  true
% 3.38/0.98  --res_passive_queue_type                priority_queues
% 3.38/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.38/0.98  --res_passive_queues_freq               [15;5]
% 3.38/0.98  --res_forward_subs                      full
% 3.38/0.98  --res_backward_subs                     full
% 3.38/0.98  --res_forward_subs_resolution           true
% 3.38/0.98  --res_backward_subs_resolution          true
% 3.38/0.98  --res_orphan_elimination                true
% 3.38/0.98  --res_time_limit                        2.
% 3.38/0.98  --res_out_proof                         true
% 3.38/0.98  
% 3.38/0.98  ------ Superposition Options
% 3.38/0.98  
% 3.38/0.98  --superposition_flag                    true
% 3.38/0.98  --sup_passive_queue_type                priority_queues
% 3.38/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.38/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.38/0.98  --demod_completeness_check              fast
% 3.38/0.98  --demod_use_ground                      true
% 3.38/0.98  --sup_to_prop_solver                    passive
% 3.38/0.98  --sup_prop_simpl_new                    true
% 3.38/0.98  --sup_prop_simpl_given                  true
% 3.38/0.98  --sup_fun_splitting                     false
% 3.38/0.98  --sup_smt_interval                      50000
% 3.38/0.98  
% 3.38/0.98  ------ Superposition Simplification Setup
% 3.38/0.98  
% 3.38/0.98  --sup_indices_passive                   []
% 3.38/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.38/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.38/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.98  --sup_full_bw                           [BwDemod]
% 3.38/0.98  --sup_immed_triv                        [TrivRules]
% 3.38/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.38/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.98  --sup_immed_bw_main                     []
% 3.38/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.38/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.38/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.38/0.98  
% 3.38/0.98  ------ Combination Options
% 3.38/0.98  
% 3.38/0.98  --comb_res_mult                         3
% 3.38/0.98  --comb_sup_mult                         2
% 3.38/0.98  --comb_inst_mult                        10
% 3.38/0.98  
% 3.38/0.98  ------ Debug Options
% 3.38/0.98  
% 3.38/0.98  --dbg_backtrace                         false
% 3.38/0.98  --dbg_dump_prop_clauses                 false
% 3.38/0.98  --dbg_dump_prop_clauses_file            -
% 3.38/0.98  --dbg_out_stat                          false
% 3.38/0.98  
% 3.38/0.98  
% 3.38/0.98  
% 3.38/0.98  
% 3.38/0.98  ------ Proving...
% 3.38/0.98  
% 3.38/0.98  
% 3.38/0.98  % SZS status Theorem for theBenchmark.p
% 3.38/0.98  
% 3.38/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.38/0.98  
% 3.38/0.98  fof(f9,conjecture,(
% 3.38/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) => ((k1_funct_1(X2,X3) != k1_funct_1(X2,X4) & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) | X3 = X4))))))),
% 3.38/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f10,negated_conjecture,(
% 3.38/0.98    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) => ((k1_funct_1(X2,X3) != k1_funct_1(X2,X4) & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) | X3 = X4))))))),
% 3.38/0.98    inference(negated_conjecture,[],[f9])).
% 3.38/0.98  
% 3.38/0.98  fof(f22,plain,(
% 3.38/0.98    ? [X0] : (? [X1] : (? [X2] : ((? [X3,X4] : (((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4) & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2)) & (v1_funct_1(X2) & v1_relat_1(X2))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.38/0.98    inference(ennf_transformation,[],[f10])).
% 3.38/0.98  
% 3.38/0.98  fof(f23,plain,(
% 3.38/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.38/0.98    inference(flattening,[],[f22])).
% 3.38/0.98  
% 3.38/0.98  fof(f42,plain,(
% 3.38/0.98    ( ! [X2,X0,X1] : (? [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) => ((k1_funct_1(X2,sK8) = k1_funct_1(X2,sK9) | ~r2_hidden(k4_tarski(k1_funct_1(X2,sK8),k1_funct_1(X2,sK9)),X1)) & sK8 != sK9 & r2_hidden(k4_tarski(sK8,sK9),X0))) )),
% 3.38/0.98    introduced(choice_axiom,[])).
% 3.38/0.98  
% 3.38/0.98  fof(f41,plain,(
% 3.38/0.98    ( ! [X0,X1] : (? [X2] : (? [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) => (? [X4,X3] : ((k1_funct_1(sK7,X3) = k1_funct_1(sK7,X4) | ~r2_hidden(k4_tarski(k1_funct_1(sK7,X3),k1_funct_1(sK7,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,sK7) & v1_funct_1(sK7) & v1_relat_1(sK7))) )),
% 3.38/0.98    introduced(choice_axiom,[])).
% 3.38/0.98  
% 3.38/0.98  fof(f40,plain,(
% 3.38/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (? [X4,X3] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK6)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,sK6,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(sK6))) )),
% 3.38/0.98    introduced(choice_axiom,[])).
% 3.38/0.98  
% 3.38/0.98  fof(f39,plain,(
% 3.38/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (? [X4,X3] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),sK5)) & r3_wellord1(sK5,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK5))),
% 3.38/0.98    introduced(choice_axiom,[])).
% 3.38/0.98  
% 3.38/0.98  fof(f43,plain,(
% 3.38/0.98    ((((k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9) | ~r2_hidden(k4_tarski(k1_funct_1(sK7,sK8),k1_funct_1(sK7,sK9)),sK6)) & sK8 != sK9 & r2_hidden(k4_tarski(sK8,sK9),sK5)) & r3_wellord1(sK5,sK6,sK7) & v1_funct_1(sK7) & v1_relat_1(sK7)) & v1_relat_1(sK6)) & v1_relat_1(sK5)),
% 3.38/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f23,f42,f41,f40,f39])).
% 3.38/0.98  
% 3.38/0.98  fof(f75,plain,(
% 3.38/0.98    r2_hidden(k4_tarski(sK8,sK9),sK5)),
% 3.38/0.98    inference(cnf_transformation,[],[f43])).
% 3.38/0.98  
% 3.38/0.98  fof(f5,axiom,(
% 3.38/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 3.38/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f14,plain,(
% 3.38/0.98    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 3.38/0.98    inference(ennf_transformation,[],[f5])).
% 3.38/0.98  
% 3.38/0.98  fof(f15,plain,(
% 3.38/0.98    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 3.38/0.98    inference(flattening,[],[f14])).
% 3.38/0.98  
% 3.38/0.98  fof(f53,plain,(
% 3.38/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f15])).
% 3.38/0.98  
% 3.38/0.98  fof(f70,plain,(
% 3.38/0.98    v1_relat_1(sK5)),
% 3.38/0.98    inference(cnf_transformation,[],[f43])).
% 3.38/0.98  
% 3.38/0.98  fof(f3,axiom,(
% 3.38/0.98    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 3.38/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f31,plain,(
% 3.38/0.98    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0))),
% 3.38/0.98    inference(nnf_transformation,[],[f3])).
% 3.38/0.98  
% 3.38/0.98  fof(f50,plain,(
% 3.38/0.98    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f31])).
% 3.38/0.98  
% 3.38/0.98  fof(f8,axiom,(
% 3.38/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k3_relat_1(X0) = k1_relat_1(X2))))))),
% 3.38/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f20,plain,(
% 3.38/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k3_relat_1(X0) = k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.38/0.98    inference(ennf_transformation,[],[f8])).
% 3.38/0.98  
% 3.38/0.98  fof(f21,plain,(
% 3.38/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k3_relat_1(X0) = k1_relat_1(X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.38/0.98    inference(flattening,[],[f20])).
% 3.38/0.98  
% 3.38/0.98  fof(f25,plain,(
% 3.38/0.98    ! [X0,X2,X1] : ((r3_wellord1(X0,X1,X2) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 3.38/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.38/0.98  
% 3.38/0.98  fof(f24,plain,(
% 3.38/0.98    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k3_relat_1(X0) = k1_relat_1(X2)))),
% 3.38/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.38/0.98  
% 3.38/0.98  fof(f26,plain,(
% 3.38/0.98    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.38/0.98    inference(definition_folding,[],[f21,f25,f24])).
% 3.38/0.98  
% 3.38/0.98  fof(f69,plain,(
% 3.38/0.98    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f26])).
% 3.38/0.98  
% 3.38/0.98  fof(f32,plain,(
% 3.38/0.98    ! [X0,X2,X1] : (((r3_wellord1(X0,X1,X2) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r3_wellord1(X0,X1,X2))) | ~sP1(X0,X2,X1))),
% 3.38/0.98    inference(nnf_transformation,[],[f25])).
% 3.38/0.98  
% 3.38/0.98  fof(f33,plain,(
% 3.38/0.98    ! [X0,X1,X2] : (((r3_wellord1(X0,X2,X1) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r3_wellord1(X0,X2,X1))) | ~sP1(X0,X1,X2))),
% 3.38/0.98    inference(rectify,[],[f32])).
% 3.38/0.98  
% 3.38/0.98  fof(f56,plain,(
% 3.38/0.98    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | ~r3_wellord1(X0,X2,X1) | ~sP1(X0,X1,X2)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f33])).
% 3.38/0.98  
% 3.38/0.98  fof(f74,plain,(
% 3.38/0.98    r3_wellord1(sK5,sK6,sK7)),
% 3.38/0.98    inference(cnf_transformation,[],[f43])).
% 3.38/0.98  
% 3.38/0.98  fof(f71,plain,(
% 3.38/0.98    v1_relat_1(sK6)),
% 3.38/0.98    inference(cnf_transformation,[],[f43])).
% 3.38/0.98  
% 3.38/0.98  fof(f72,plain,(
% 3.38/0.98    v1_relat_1(sK7)),
% 3.38/0.98    inference(cnf_transformation,[],[f43])).
% 3.38/0.98  
% 3.38/0.98  fof(f73,plain,(
% 3.38/0.98    v1_funct_1(sK7)),
% 3.38/0.98    inference(cnf_transformation,[],[f43])).
% 3.38/0.98  
% 3.38/0.98  fof(f34,plain,(
% 3.38/0.98    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | (? [X3,X4] : (((~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X3,X4),X0)) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | r2_hidden(k4_tarski(X3,X4),X0))) | ~v2_funct_1(X2) | k2_relat_1(X2) != k3_relat_1(X1) | k3_relat_1(X0) != k1_relat_1(X2))) & ((! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X0) | (~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)))) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X3,X4),X0))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k3_relat_1(X0) = k1_relat_1(X2)) | ~sP0(X1,X2,X0)))),
% 3.38/0.98    inference(nnf_transformation,[],[f24])).
% 3.38/0.98  
% 3.38/0.98  fof(f35,plain,(
% 3.38/0.98    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ? [X3,X4] : ((~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X4),X0)) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | r2_hidden(k4_tarski(X3,X4),X0))) | ~v2_funct_1(X2) | k2_relat_1(X2) != k3_relat_1(X1) | k3_relat_1(X0) != k1_relat_1(X2)) & ((! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X3,X4),X0))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k3_relat_1(X0) = k1_relat_1(X2)) | ~sP0(X1,X2,X0)))),
% 3.38/0.98    inference(flattening,[],[f34])).
% 3.38/0.98  
% 3.38/0.98  fof(f36,plain,(
% 3.38/0.98    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3,X4] : ((~r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) | ~r2_hidden(X4,k3_relat_1(X2)) | ~r2_hidden(X3,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) & r2_hidden(X4,k3_relat_1(X2)) & r2_hidden(X3,k3_relat_1(X2))) | r2_hidden(k4_tarski(X3,X4),X2))) | ~v2_funct_1(X1) | k2_relat_1(X1) != k3_relat_1(X0) | k3_relat_1(X2) != k1_relat_1(X1)) & ((! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0) | ~r2_hidden(X6,k3_relat_1(X2)) | ~r2_hidden(X5,k3_relat_1(X2))) & ((r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0) & r2_hidden(X6,k3_relat_1(X2)) & r2_hidden(X5,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X5,X6),X2))) & v2_funct_1(X1) & k2_relat_1(X1) = k3_relat_1(X0) & k3_relat_1(X2) = k1_relat_1(X1)) | ~sP0(X0,X1,X2)))),
% 3.38/0.98    inference(rectify,[],[f35])).
% 3.38/0.98  
% 3.38/0.98  fof(f37,plain,(
% 3.38/0.98    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) | ~r2_hidden(X4,k3_relat_1(X2)) | ~r2_hidden(X3,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) & r2_hidden(X4,k3_relat_1(X2)) & r2_hidden(X3,k3_relat_1(X2))) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(k1_funct_1(X1,sK3(X0,X1,X2)),k1_funct_1(X1,sK4(X0,X1,X2))),X0) | ~r2_hidden(sK4(X0,X1,X2),k3_relat_1(X2)) | ~r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(k1_funct_1(X1,sK3(X0,X1,X2)),k1_funct_1(X1,sK4(X0,X1,X2))),X0) & r2_hidden(sK4(X0,X1,X2),k3_relat_1(X2)) & r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 3.38/0.98    introduced(choice_axiom,[])).
% 3.38/0.98  
% 3.38/0.98  fof(f38,plain,(
% 3.38/0.98    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(k4_tarski(k1_funct_1(X1,sK3(X0,X1,X2)),k1_funct_1(X1,sK4(X0,X1,X2))),X0) | ~r2_hidden(sK4(X0,X1,X2),k3_relat_1(X2)) | ~r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(k1_funct_1(X1,sK3(X0,X1,X2)),k1_funct_1(X1,sK4(X0,X1,X2))),X0) & r2_hidden(sK4(X0,X1,X2),k3_relat_1(X2)) & r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))) | ~v2_funct_1(X1) | k2_relat_1(X1) != k3_relat_1(X0) | k3_relat_1(X2) != k1_relat_1(X1)) & ((! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0) | ~r2_hidden(X6,k3_relat_1(X2)) | ~r2_hidden(X5,k3_relat_1(X2))) & ((r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0) & r2_hidden(X6,k3_relat_1(X2)) & r2_hidden(X5,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X5,X6),X2))) & v2_funct_1(X1) & k2_relat_1(X1) = k3_relat_1(X0) & k3_relat_1(X2) = k1_relat_1(X1)) | ~sP0(X0,X1,X2)))),
% 3.38/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f37])).
% 3.38/0.98  
% 3.38/0.98  fof(f58,plain,(
% 3.38/0.98    ( ! [X2,X0,X1] : (k3_relat_1(X2) = k1_relat_1(X1) | ~sP0(X0,X1,X2)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f38])).
% 3.38/0.98  
% 3.38/0.98  fof(f60,plain,(
% 3.38/0.98    ( ! [X2,X0,X1] : (v2_funct_1(X1) | ~sP0(X0,X1,X2)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f38])).
% 3.38/0.98  
% 3.38/0.98  fof(f1,axiom,(
% 3.38/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.38/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f11,plain,(
% 3.38/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 => r1_tarski(X0,X1))),
% 3.38/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 3.38/0.98  
% 3.38/0.98  fof(f12,plain,(
% 3.38/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 3.38/0.98    inference(ennf_transformation,[],[f11])).
% 3.38/0.98  
% 3.38/0.98  fof(f44,plain,(
% 3.38/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.38/0.98    inference(cnf_transformation,[],[f12])).
% 3.38/0.98  
% 3.38/0.98  fof(f6,axiom,(
% 3.38/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.38/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f16,plain,(
% 3.38/0.98    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.38/0.98    inference(ennf_transformation,[],[f6])).
% 3.38/0.98  
% 3.38/0.98  fof(f17,plain,(
% 3.38/0.98    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.38/0.98    inference(flattening,[],[f16])).
% 3.38/0.98  
% 3.38/0.98  fof(f54,plain,(
% 3.38/0.98    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f17])).
% 3.38/0.98  
% 3.38/0.98  fof(f7,axiom,(
% 3.38/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))))),
% 3.38/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f18,plain,(
% 3.38/0.98    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.38/0.98    inference(ennf_transformation,[],[f7])).
% 3.38/0.98  
% 3.38/0.98  fof(f19,plain,(
% 3.38/0.98    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.38/0.98    inference(flattening,[],[f18])).
% 3.38/0.98  
% 3.38/0.98  fof(f55,plain,(
% 3.38/0.98    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f19])).
% 3.38/0.98  
% 3.38/0.98  fof(f4,axiom,(
% 3.38/0.98    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.38/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f13,plain,(
% 3.38/0.98    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.38/0.98    inference(ennf_transformation,[],[f4])).
% 3.38/0.98  
% 3.38/0.98  fof(f51,plain,(
% 3.38/0.98    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f13])).
% 3.38/0.98  
% 3.38/0.98  fof(f63,plain,(
% 3.38/0.98    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | ~sP0(X0,X1,X2)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f38])).
% 3.38/0.98  
% 3.38/0.98  fof(f77,plain,(
% 3.38/0.98    k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9) | ~r2_hidden(k4_tarski(k1_funct_1(sK7,sK8),k1_funct_1(sK7,sK9)),sK6)),
% 3.38/0.98    inference(cnf_transformation,[],[f43])).
% 3.38/0.98  
% 3.38/0.98  fof(f52,plain,(
% 3.38/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.38/0.98    inference(cnf_transformation,[],[f15])).
% 3.38/0.98  
% 3.38/0.98  fof(f2,axiom,(
% 3.38/0.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.38/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.38/0.98  
% 3.38/0.98  fof(f27,plain,(
% 3.38/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.38/0.98    inference(nnf_transformation,[],[f2])).
% 3.38/0.98  
% 3.38/0.98  fof(f28,plain,(
% 3.38/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.38/0.98    inference(rectify,[],[f27])).
% 3.38/0.98  
% 3.38/0.98  fof(f29,plain,(
% 3.38/0.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 3.38/0.98    introduced(choice_axiom,[])).
% 3.38/0.98  
% 3.38/0.98  fof(f30,plain,(
% 3.38/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.38/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 3.38/0.98  
% 3.38/0.98  fof(f46,plain,(
% 3.38/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.38/0.98    inference(cnf_transformation,[],[f30])).
% 3.38/0.98  
% 3.38/0.98  fof(f78,plain,(
% 3.38/0.98    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 3.38/0.98    inference(equality_resolution,[],[f46])).
% 3.38/0.98  
% 3.38/0.98  fof(f79,plain,(
% 3.38/0.98    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 3.38/0.98    inference(equality_resolution,[],[f78])).
% 3.38/0.98  
% 3.38/0.98  fof(f45,plain,(
% 3.38/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.38/0.98    inference(cnf_transformation,[],[f30])).
% 3.38/0.98  
% 3.38/0.98  fof(f80,plain,(
% 3.38/0.98    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 3.38/0.98    inference(equality_resolution,[],[f45])).
% 3.38/0.98  
% 3.38/0.98  fof(f76,plain,(
% 3.38/0.98    sK8 != sK9),
% 3.38/0.98    inference(cnf_transformation,[],[f43])).
% 3.38/0.98  
% 3.38/0.98  cnf(c_28,negated_conjecture,
% 3.38/0.98      ( r2_hidden(k4_tarski(sK8,sK9),sK5) ),
% 3.38/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_3162,plain,
% 3.38/0.98      ( r2_hidden(k4_tarski(sK8,sK9),sK5) = iProver_top ),
% 3.38/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_8,plain,
% 3.38/0.98      ( r2_hidden(X0,k3_relat_1(X1))
% 3.38/0.98      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 3.38/0.98      | ~ v1_relat_1(X1) ),
% 3.38/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_33,negated_conjecture,
% 3.38/0.98      ( v1_relat_1(sK5) ),
% 3.38/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_597,plain,
% 3.38/0.98      ( r2_hidden(X0,k3_relat_1(X1))
% 3.38/0.98      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 3.38/0.98      | sK5 != X1 ),
% 3.38/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_33]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_598,plain,
% 3.38/0.98      ( r2_hidden(X0,k3_relat_1(sK5))
% 3.38/0.98      | ~ r2_hidden(k4_tarski(X1,X0),sK5) ),
% 3.38/0.98      inference(unflattening,[status(thm)],[c_597]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_3154,plain,
% 3.38/0.98      ( r2_hidden(X0,k3_relat_1(sK5)) = iProver_top
% 3.38/0.98      | r2_hidden(k4_tarski(X1,X0),sK5) != iProver_top ),
% 3.38/0.98      inference(predicate_to_equality,[status(thm)],[c_598]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_3474,plain,
% 3.38/0.98      ( r2_hidden(sK9,k3_relat_1(sK5)) = iProver_top ),
% 3.38/0.98      inference(superposition,[status(thm)],[c_3162,c_3154]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_5,plain,
% 3.38/0.98      ( ~ r2_hidden(X0,X1)
% 3.38/0.98      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
% 3.38/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_3176,plain,
% 3.38/0.98      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
% 3.38/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.38/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_4251,plain,
% 3.38/0.98      ( k4_xboole_0(k1_tarski(sK9),k3_relat_1(sK5)) = k1_xboole_0 ),
% 3.38/0.98      inference(superposition,[status(thm)],[c_3474,c_3176]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_25,plain,
% 3.38/0.98      ( sP1(X0,X1,X2)
% 3.38/0.98      | ~ v1_funct_1(X1)
% 3.38/0.98      | ~ v1_relat_1(X2)
% 3.38/0.98      | ~ v1_relat_1(X0)
% 3.38/0.98      | ~ v1_relat_1(X1) ),
% 3.38/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_13,plain,
% 3.38/0.98      ( ~ sP1(X0,X1,X2) | sP0(X2,X1,X0) | ~ r3_wellord1(X0,X2,X1) ),
% 3.38/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_29,negated_conjecture,
% 3.38/0.98      ( r3_wellord1(sK5,sK6,sK7) ),
% 3.38/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_469,plain,
% 3.38/0.98      ( ~ sP1(X0,X1,X2)
% 3.38/0.98      | sP0(X2,X1,X0)
% 3.38/0.98      | sK5 != X0
% 3.38/0.98      | sK6 != X2
% 3.38/0.98      | sK7 != X1 ),
% 3.38/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_470,plain,
% 3.38/0.98      ( ~ sP1(sK5,sK7,sK6) | sP0(sK6,sK7,sK5) ),
% 3.38/0.98      inference(unflattening,[status(thm)],[c_469]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_482,plain,
% 3.38/0.98      ( sP0(sK6,sK7,sK5)
% 3.38/0.98      | ~ v1_funct_1(X0)
% 3.38/0.98      | ~ v1_relat_1(X0)
% 3.38/0.98      | ~ v1_relat_1(X1)
% 3.38/0.98      | ~ v1_relat_1(X2)
% 3.38/0.98      | sK5 != X1
% 3.38/0.98      | sK6 != X2
% 3.38/0.98      | sK7 != X0 ),
% 3.38/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_470]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_483,plain,
% 3.38/0.98      ( sP0(sK6,sK7,sK5)
% 3.38/0.98      | ~ v1_funct_1(sK7)
% 3.38/0.98      | ~ v1_relat_1(sK5)
% 3.38/0.98      | ~ v1_relat_1(sK6)
% 3.38/0.98      | ~ v1_relat_1(sK7) ),
% 3.38/0.98      inference(unflattening,[status(thm)],[c_482]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_32,negated_conjecture,
% 3.38/0.98      ( v1_relat_1(sK6) ),
% 3.38/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_31,negated_conjecture,
% 3.38/0.98      ( v1_relat_1(sK7) ),
% 3.38/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_30,negated_conjecture,
% 3.38/0.98      ( v1_funct_1(sK7) ),
% 3.38/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_485,plain,
% 3.38/0.98      ( sP0(sK6,sK7,sK5) ),
% 3.38/0.98      inference(global_propositional_subsumption,
% 3.38/0.98                [status(thm)],
% 3.38/0.98                [c_483,c_33,c_32,c_31,c_30]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_3161,plain,
% 3.38/0.98      ( sP0(sK6,sK7,sK5) = iProver_top ),
% 3.38/0.98      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_24,plain,
% 3.38/0.98      ( ~ sP0(X0,X1,X2) | k1_relat_1(X1) = k3_relat_1(X2) ),
% 3.38/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_3164,plain,
% 3.38/0.98      ( k1_relat_1(X0) = k3_relat_1(X1) | sP0(X2,X0,X1) != iProver_top ),
% 3.38/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_4147,plain,
% 3.38/0.98      ( k1_relat_1(sK7) = k3_relat_1(sK5) ),
% 3.38/0.98      inference(superposition,[status(thm)],[c_3161,c_3164]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_22,plain,
% 3.38/0.98      ( ~ sP0(X0,X1,X2) | v2_funct_1(X1) ),
% 3.38/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1250,plain,
% 3.38/0.98      ( v2_funct_1(X0) | sK5 != X1 | sK6 != X2 | sK7 != X0 ),
% 3.38/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_485]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1251,plain,
% 3.38/0.98      ( v2_funct_1(sK7) ),
% 3.38/0.98      inference(unflattening,[status(thm)],[c_1250]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_0,plain,
% 3.38/0.98      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.38/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_10,plain,
% 3.38/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.38/0.98      | ~ v1_funct_1(X1)
% 3.38/0.98      | ~ v2_funct_1(X1)
% 3.38/0.98      | ~ v1_relat_1(X1)
% 3.38/0.98      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 3.38/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_441,plain,
% 3.38/0.98      ( ~ v1_funct_1(X0)
% 3.38/0.98      | ~ v2_funct_1(X0)
% 3.38/0.98      | ~ v1_relat_1(X0)
% 3.38/0.98      | X1 != X2
% 3.38/0.98      | k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
% 3.38/0.98      | k4_xboole_0(X2,X3) != k1_xboole_0
% 3.38/0.98      | k1_relat_1(X0) != X3 ),
% 3.38/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_442,plain,
% 3.38/0.98      ( ~ v1_funct_1(X0)
% 3.38/0.98      | ~ v2_funct_1(X0)
% 3.38/0.98      | ~ v1_relat_1(X0)
% 3.38/0.98      | k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
% 3.38/0.98      | k4_xboole_0(X1,k1_relat_1(X0)) != k1_xboole_0 ),
% 3.38/0.98      inference(unflattening,[status(thm)],[c_441]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_513,plain,
% 3.38/0.98      ( ~ v2_funct_1(X0)
% 3.38/0.98      | ~ v1_relat_1(X0)
% 3.38/0.98      | k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
% 3.38/0.98      | k4_xboole_0(X1,k1_relat_1(X0)) != k1_xboole_0
% 3.38/0.98      | sK7 != X0 ),
% 3.38/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_442]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_514,plain,
% 3.38/0.98      ( ~ v2_funct_1(sK7)
% 3.38/0.98      | ~ v1_relat_1(sK7)
% 3.38/0.98      | k10_relat_1(sK7,k9_relat_1(sK7,X0)) = X0
% 3.38/0.98      | k4_xboole_0(X0,k1_relat_1(sK7)) != k1_xboole_0 ),
% 3.38/0.98      inference(unflattening,[status(thm)],[c_513]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_518,plain,
% 3.38/0.98      ( ~ v2_funct_1(sK7)
% 3.38/0.98      | k10_relat_1(sK7,k9_relat_1(sK7,X0)) = X0
% 3.38/0.98      | k4_xboole_0(X0,k1_relat_1(sK7)) != k1_xboole_0 ),
% 3.38/0.98      inference(global_propositional_subsumption,
% 3.38/0.98                [status(thm)],
% 3.38/0.98                [c_514,c_31]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_1411,plain,
% 3.38/0.98      ( k10_relat_1(sK7,k9_relat_1(sK7,X0)) = X0
% 3.38/0.98      | k4_xboole_0(X0,k1_relat_1(sK7)) != k1_xboole_0 ),
% 3.38/0.98      inference(backward_subsumption_resolution,
% 3.38/0.98                [status(thm)],
% 3.38/0.98                [c_1251,c_518]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_4675,plain,
% 3.38/0.98      ( k10_relat_1(sK7,k9_relat_1(sK7,X0)) = X0
% 3.38/0.98      | k4_xboole_0(X0,k3_relat_1(sK5)) != k1_xboole_0 ),
% 3.38/0.98      inference(demodulation,[status(thm)],[c_4147,c_1411]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_4769,plain,
% 3.38/0.98      ( k10_relat_1(sK7,k9_relat_1(sK7,k1_tarski(sK9))) = k1_tarski(sK9) ),
% 3.38/0.98      inference(superposition,[status(thm)],[c_4251,c_4675]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_11,plain,
% 3.38/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.38/0.98      | ~ v1_funct_1(X1)
% 3.38/0.98      | ~ v1_relat_1(X1)
% 3.38/0.98      | k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) ),
% 3.38/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_495,plain,
% 3.38/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.38/0.98      | ~ v1_relat_1(X1)
% 3.38/0.98      | k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))
% 3.38/0.98      | sK7 != X1 ),
% 3.38/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_30]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_496,plain,
% 3.38/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 3.38/0.98      | ~ v1_relat_1(sK7)
% 3.38/0.98      | k2_relat_1(k7_relat_1(sK7,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK7,X0)) ),
% 3.38/0.98      inference(unflattening,[status(thm)],[c_495]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_500,plain,
% 3.38/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 3.38/0.98      | k2_relat_1(k7_relat_1(sK7,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK7,X0)) ),
% 3.38/0.98      inference(global_propositional_subsumption,
% 3.38/0.98                [status(thm)],
% 3.38/0.98                [c_496,c_31]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_3160,plain,
% 3.38/0.98      ( k2_relat_1(k7_relat_1(sK7,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK7,X0))
% 3.38/0.98      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.38/0.98      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_7,plain,
% 3.38/0.98      ( ~ v1_relat_1(X0)
% 3.38/0.98      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.38/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_607,plain,
% 3.38/0.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) | sK7 != X0 ),
% 3.38/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_31]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_608,plain,
% 3.38/0.98      ( k2_relat_1(k7_relat_1(sK7,X0)) = k9_relat_1(sK7,X0) ),
% 3.38/0.98      inference(unflattening,[status(thm)],[c_607]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_3247,plain,
% 3.38/0.98      ( k9_relat_1(sK7,k1_tarski(X0)) = k1_tarski(k1_funct_1(sK7,X0))
% 3.38/0.98      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.38/0.98      inference(demodulation,[status(thm)],[c_3160,c_608]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_4674,plain,
% 3.38/0.98      ( k9_relat_1(sK7,k1_tarski(X0)) = k1_tarski(k1_funct_1(sK7,X0))
% 3.38/0.98      | r2_hidden(X0,k3_relat_1(sK5)) != iProver_top ),
% 3.38/0.98      inference(demodulation,[status(thm)],[c_4147,c_3247]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_4779,plain,
% 3.38/0.98      ( k9_relat_1(sK7,k1_tarski(sK9)) = k1_tarski(k1_funct_1(sK7,sK9)) ),
% 3.38/0.98      inference(superposition,[status(thm)],[c_3474,c_4674]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_19,plain,
% 3.38/0.98      ( ~ sP0(X0,X1,X2)
% 3.38/0.98      | ~ r2_hidden(k4_tarski(X3,X4),X2)
% 3.38/0.98      | r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) ),
% 3.38/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_3169,plain,
% 3.38/0.98      ( sP0(X0,X1,X2) != iProver_top
% 3.38/0.98      | r2_hidden(k4_tarski(X3,X4),X2) != iProver_top
% 3.38/0.98      | r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0) = iProver_top ),
% 3.38/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_4978,plain,
% 3.38/0.98      ( sP0(X0,X1,sK5) != iProver_top
% 3.38/0.98      | r2_hidden(k4_tarski(k1_funct_1(X1,sK8),k1_funct_1(X1,sK9)),X0) = iProver_top ),
% 3.38/0.98      inference(superposition,[status(thm)],[c_3162,c_3169]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_26,negated_conjecture,
% 3.38/0.98      ( ~ r2_hidden(k4_tarski(k1_funct_1(sK7,sK8),k1_funct_1(sK7,sK9)),sK6)
% 3.38/0.98      | k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9) ),
% 3.38/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_3163,plain,
% 3.38/0.98      ( k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9)
% 3.38/0.98      | r2_hidden(k4_tarski(k1_funct_1(sK7,sK8),k1_funct_1(sK7,sK9)),sK6) != iProver_top ),
% 3.38/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_5237,plain,
% 3.38/0.98      ( k1_funct_1(sK7,sK9) = k1_funct_1(sK7,sK8)
% 3.38/0.98      | sP0(sK6,sK7,sK5) != iProver_top ),
% 3.38/0.98      inference(superposition,[status(thm)],[c_4978,c_3163]) ).
% 3.38/0.98  
% 3.38/0.98  cnf(c_34,plain,
% 3.38/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_35,plain,
% 3.38/0.99      ( v1_relat_1(sK6) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_36,plain,
% 3.38/0.99      ( v1_relat_1(sK7) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_37,plain,
% 3.38/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_484,plain,
% 3.38/0.99      ( sP0(sK6,sK7,sK5) = iProver_top
% 3.38/0.99      | v1_funct_1(sK7) != iProver_top
% 3.38/0.99      | v1_relat_1(sK5) != iProver_top
% 3.38/0.99      | v1_relat_1(sK6) != iProver_top
% 3.38/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_5667,plain,
% 3.38/0.99      ( k1_funct_1(sK7,sK9) = k1_funct_1(sK7,sK8) ),
% 3.38/0.99      inference(global_propositional_subsumption,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_5237,c_34,c_35,c_36,c_37,c_484]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_5812,plain,
% 3.38/0.99      ( k9_relat_1(sK7,k1_tarski(sK9)) = k1_tarski(k1_funct_1(sK7,sK8)) ),
% 3.38/0.99      inference(light_normalisation,[status(thm)],[c_4779,c_5667]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_9,plain,
% 3.38/0.99      ( r2_hidden(X0,k3_relat_1(X1))
% 3.38/0.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.38/0.99      | ~ v1_relat_1(X1) ),
% 3.38/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_585,plain,
% 3.38/0.99      ( r2_hidden(X0,k3_relat_1(X1))
% 3.38/0.99      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.38/0.99      | sK5 != X1 ),
% 3.38/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_33]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_586,plain,
% 3.38/0.99      ( r2_hidden(X0,k3_relat_1(sK5))
% 3.38/0.99      | ~ r2_hidden(k4_tarski(X0,X1),sK5) ),
% 3.38/0.99      inference(unflattening,[status(thm)],[c_585]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3155,plain,
% 3.38/0.99      ( r2_hidden(X0,k3_relat_1(sK5)) = iProver_top
% 3.38/0.99      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3523,plain,
% 3.38/0.99      ( r2_hidden(sK8,k3_relat_1(sK5)) = iProver_top ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_3162,c_3155]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_4250,plain,
% 3.38/0.99      ( k4_xboole_0(k1_tarski(sK8),k3_relat_1(sK5)) = k1_xboole_0 ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_3523,c_3176]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_4768,plain,
% 3.38/0.99      ( k10_relat_1(sK7,k9_relat_1(sK7,k1_tarski(sK8))) = k1_tarski(sK8) ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_4250,c_4675]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_4778,plain,
% 3.38/0.99      ( k9_relat_1(sK7,k1_tarski(sK8)) = k1_tarski(k1_funct_1(sK7,sK8)) ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_3523,c_4674]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_9095,plain,
% 3.38/0.99      ( k10_relat_1(sK7,k1_tarski(k1_funct_1(sK7,sK8))) = k1_tarski(sK8) ),
% 3.38/0.99      inference(light_normalisation,[status(thm)],[c_4768,c_4778]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_9189,plain,
% 3.38/0.99      ( k1_tarski(sK8) = k1_tarski(sK9) ),
% 3.38/0.99      inference(light_normalisation,[status(thm)],[c_4769,c_5812,c_9095]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3,plain,
% 3.38/0.99      ( r2_hidden(X0,k1_tarski(X0)) ),
% 3.38/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3178,plain,
% 3.38/0.99      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_9196,plain,
% 3.38/0.99      ( r2_hidden(sK9,k1_tarski(sK8)) = iProver_top ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_9189,c_3178]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_4,plain,
% 3.38/0.99      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 3.38/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3177,plain,
% 3.38/0.99      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 3.38/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_9654,plain,
% 3.38/0.99      ( sK9 = sK8 ),
% 3.38/0.99      inference(superposition,[status(thm)],[c_9196,c_3177]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2526,plain,
% 3.38/0.99      ( X0 != X1 | k1_tarski(X0) = k1_tarski(X1) ),
% 3.38/0.99      theory(equality) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_8509,plain,
% 3.38/0.99      ( k1_tarski(sK9) = k1_tarski(sK8) | sK9 != sK8 ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_2526]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_5709,plain,
% 3.38/0.99      ( r2_hidden(sK8,k1_tarski(sK8)) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2527,plain,
% 3.38/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.38/0.99      theory(equality) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3456,plain,
% 3.38/0.99      ( r2_hidden(X0,X1)
% 3.38/0.99      | ~ r2_hidden(X2,k1_tarski(X2))
% 3.38/0.99      | X0 != X2
% 3.38/0.99      | X1 != k1_tarski(X2) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_2527]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3640,plain,
% 3.38/0.99      ( ~ r2_hidden(X0,k1_tarski(X0))
% 3.38/0.99      | r2_hidden(X1,k1_tarski(X2))
% 3.38/0.99      | X1 != X0
% 3.38/0.99      | k1_tarski(X2) != k1_tarski(X0) ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_3456]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3961,plain,
% 3.38/0.99      ( ~ r2_hidden(X0,k1_tarski(X0))
% 3.38/0.99      | r2_hidden(sK8,k1_tarski(sK9))
% 3.38/0.99      | k1_tarski(sK9) != k1_tarski(X0)
% 3.38/0.99      | sK8 != X0 ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_3640]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_4198,plain,
% 3.38/0.99      ( r2_hidden(sK8,k1_tarski(sK9))
% 3.38/0.99      | ~ r2_hidden(sK8,k1_tarski(sK8))
% 3.38/0.99      | k1_tarski(sK9) != k1_tarski(sK8)
% 3.38/0.99      | sK8 != sK8 ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_3961]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_2523,plain,( X0 = X0 ),theory(equality) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3747,plain,
% 3.38/0.99      ( sK8 = sK8 ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_2523]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_3415,plain,
% 3.38/0.99      ( ~ r2_hidden(sK8,k1_tarski(sK9)) | sK8 = sK9 ),
% 3.38/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(c_27,negated_conjecture,
% 3.38/0.99      ( sK8 != sK9 ),
% 3.38/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.38/0.99  
% 3.38/0.99  cnf(contradiction,plain,
% 3.38/0.99      ( $false ),
% 3.38/0.99      inference(minisat,
% 3.38/0.99                [status(thm)],
% 3.38/0.99                [c_9654,c_8509,c_5709,c_4198,c_3747,c_3415,c_27]) ).
% 3.38/0.99  
% 3.38/0.99  
% 3.38/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.38/0.99  
% 3.38/0.99  ------                               Statistics
% 3.38/0.99  
% 3.38/0.99  ------ General
% 3.38/0.99  
% 3.38/0.99  abstr_ref_over_cycles:                  0
% 3.38/0.99  abstr_ref_under_cycles:                 0
% 3.38/0.99  gc_basic_clause_elim:                   0
% 3.38/0.99  forced_gc_time:                         0
% 3.38/0.99  parsing_time:                           0.01
% 3.38/0.99  unif_index_cands_time:                  0.
% 3.38/0.99  unif_index_add_time:                    0.
% 3.38/0.99  orderings_time:                         0.
% 3.38/0.99  out_proof_time:                         0.009
% 3.38/0.99  total_time:                             0.261
% 3.38/0.99  num_of_symbols:                         58
% 3.38/0.99  num_of_terms:                           7964
% 3.38/0.99  
% 3.38/0.99  ------ Preprocessing
% 3.38/0.99  
% 3.38/0.99  num_of_splits:                          0
% 3.38/0.99  num_of_split_atoms:                     0
% 3.38/0.99  num_of_reused_defs:                     0
% 3.38/0.99  num_eq_ax_congr_red:                    43
% 3.38/0.99  num_of_sem_filtered_clauses:            1
% 3.38/0.99  num_of_subtypes:                        0
% 3.38/0.99  monotx_restored_types:                  0
% 3.38/0.99  sat_num_of_epr_types:                   0
% 3.38/0.99  sat_num_of_non_cyclic_types:            0
% 3.38/0.99  sat_guarded_non_collapsed_types:        0
% 3.38/0.99  num_pure_diseq_elim:                    0
% 3.38/0.99  simp_replaced_by:                       0
% 3.38/0.99  res_preprocessed:                       159
% 3.38/0.99  prep_upred:                             0
% 3.38/0.99  prep_unflattend:                        62
% 3.38/0.99  smt_new_axioms:                         0
% 3.38/0.99  pred_elim_cands:                        3
% 3.38/0.99  pred_elim:                              5
% 3.38/0.99  pred_elim_cl:                           2
% 3.38/0.99  pred_elim_cycles:                       10
% 3.38/0.99  merged_defs:                            8
% 3.38/0.99  merged_defs_ncl:                        0
% 3.38/0.99  bin_hyper_res:                          8
% 3.38/0.99  prep_cycles:                            4
% 3.38/0.99  pred_elim_time:                         0.036
% 3.38/0.99  splitting_time:                         0.
% 3.38/0.99  sem_filter_time:                        0.
% 3.38/0.99  monotx_time:                            0.001
% 3.38/0.99  subtype_inf_time:                       0.
% 3.38/0.99  
% 3.38/0.99  ------ Problem properties
% 3.38/0.99  
% 3.38/0.99  clauses:                                32
% 3.38/0.99  conjectures:                            3
% 3.38/0.99  epr:                                    3
% 3.38/0.99  horn:                                   28
% 3.38/0.99  ground:                                 4
% 3.38/0.99  unary:                                  7
% 3.38/0.99  binary:                                 15
% 3.38/0.99  lits:                                   83
% 3.38/0.99  lits_eq:                                25
% 3.38/0.99  fd_pure:                                0
% 3.38/0.99  fd_pseudo:                              0
% 3.38/0.99  fd_cond:                                0
% 3.38/0.99  fd_pseudo_cond:                         2
% 3.38/0.99  ac_symbols:                             0
% 3.38/0.99  
% 3.38/0.99  ------ Propositional Solver
% 3.38/0.99  
% 3.38/0.99  prop_solver_calls:                      27
% 3.38/0.99  prop_fast_solver_calls:                 1444
% 3.38/0.99  smt_solver_calls:                       0
% 3.38/0.99  smt_fast_solver_calls:                  0
% 3.38/0.99  prop_num_of_clauses:                    3338
% 3.38/0.99  prop_preprocess_simplified:             9733
% 3.38/0.99  prop_fo_subsumed:                       9
% 3.38/0.99  prop_solver_time:                       0.
% 3.38/0.99  smt_solver_time:                        0.
% 3.38/0.99  smt_fast_solver_time:                   0.
% 3.38/0.99  prop_fast_solver_time:                  0.
% 3.38/0.99  prop_unsat_core_time:                   0.
% 3.38/0.99  
% 3.38/0.99  ------ QBF
% 3.38/0.99  
% 3.38/0.99  qbf_q_res:                              0
% 3.38/0.99  qbf_num_tautologies:                    0
% 3.38/0.99  qbf_prep_cycles:                        0
% 3.38/0.99  
% 3.38/0.99  ------ BMC1
% 3.38/0.99  
% 3.38/0.99  bmc1_current_bound:                     -1
% 3.38/0.99  bmc1_last_solved_bound:                 -1
% 3.38/0.99  bmc1_unsat_core_size:                   -1
% 3.38/0.99  bmc1_unsat_core_parents_size:           -1
% 3.38/0.99  bmc1_merge_next_fun:                    0
% 3.38/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.38/0.99  
% 3.38/0.99  ------ Instantiation
% 3.38/0.99  
% 3.38/0.99  inst_num_of_clauses:                    1003
% 3.38/0.99  inst_num_in_passive:                    441
% 3.38/0.99  inst_num_in_active:                     367
% 3.38/0.99  inst_num_in_unprocessed:                196
% 3.38/0.99  inst_num_of_loops:                      430
% 3.38/0.99  inst_num_of_learning_restarts:          0
% 3.38/0.99  inst_num_moves_active_passive:          61
% 3.38/0.99  inst_lit_activity:                      0
% 3.38/0.99  inst_lit_activity_moves:                0
% 3.38/0.99  inst_num_tautologies:                   0
% 3.38/0.99  inst_num_prop_implied:                  0
% 3.38/0.99  inst_num_existing_simplified:           0
% 3.38/0.99  inst_num_eq_res_simplified:             0
% 3.38/0.99  inst_num_child_elim:                    0
% 3.38/0.99  inst_num_of_dismatching_blockings:      377
% 3.38/0.99  inst_num_of_non_proper_insts:           1039
% 3.38/0.99  inst_num_of_duplicates:                 0
% 3.38/0.99  inst_inst_num_from_inst_to_res:         0
% 3.38/0.99  inst_dismatching_checking_time:         0.
% 3.38/0.99  
% 3.38/0.99  ------ Resolution
% 3.38/0.99  
% 3.38/0.99  res_num_of_clauses:                     0
% 3.38/0.99  res_num_in_passive:                     0
% 3.38/0.99  res_num_in_active:                      0
% 3.38/0.99  res_num_of_loops:                       163
% 3.38/0.99  res_forward_subset_subsumed:            125
% 3.38/0.99  res_backward_subset_subsumed:           2
% 3.38/0.99  res_forward_subsumed:                   0
% 3.38/0.99  res_backward_subsumed:                  0
% 3.38/0.99  res_forward_subsumption_resolution:     0
% 3.38/0.99  res_backward_subsumption_resolution:    1
% 3.38/0.99  res_clause_to_clause_subsumption:       237
% 3.38/0.99  res_orphan_elimination:                 0
% 3.38/0.99  res_tautology_del:                      98
% 3.38/0.99  res_num_eq_res_simplified:              0
% 3.38/0.99  res_num_sel_changes:                    0
% 3.38/0.99  res_moves_from_active_to_pass:          0
% 3.38/0.99  
% 3.38/0.99  ------ Superposition
% 3.38/0.99  
% 3.38/0.99  sup_time_total:                         0.
% 3.38/0.99  sup_time_generating:                    0.
% 3.38/0.99  sup_time_sim_full:                      0.
% 3.38/0.99  sup_time_sim_immed:                     0.
% 3.38/0.99  
% 3.38/0.99  sup_num_of_clauses:                     110
% 3.38/0.99  sup_num_in_active:                      76
% 3.38/0.99  sup_num_in_passive:                     34
% 3.38/0.99  sup_num_of_loops:                       84
% 3.38/0.99  sup_fw_superposition:                   49
% 3.38/0.99  sup_bw_superposition:                   66
% 3.38/0.99  sup_immediate_simplified:               11
% 3.38/0.99  sup_given_eliminated:                   1
% 3.38/0.99  comparisons_done:                       0
% 3.38/0.99  comparisons_avoided:                    9
% 3.38/0.99  
% 3.38/0.99  ------ Simplifications
% 3.38/0.99  
% 3.38/0.99  
% 3.38/0.99  sim_fw_subset_subsumed:                 3
% 3.38/0.99  sim_bw_subset_subsumed:                 0
% 3.38/0.99  sim_fw_subsumed:                        6
% 3.38/0.99  sim_bw_subsumed:                        0
% 3.38/0.99  sim_fw_subsumption_res:                 0
% 3.38/0.99  sim_bw_subsumption_res:                 0
% 3.38/0.99  sim_tautology_del:                      0
% 3.38/0.99  sim_eq_tautology_del:                   3
% 3.38/0.99  sim_eq_res_simp:                        0
% 3.38/0.99  sim_fw_demodulated:                     1
% 3.38/0.99  sim_bw_demodulated:                     10
% 3.38/0.99  sim_light_normalised:                   9
% 3.38/0.99  sim_joinable_taut:                      0
% 3.38/0.99  sim_joinable_simp:                      0
% 3.38/0.99  sim_ac_normalised:                      0
% 3.38/0.99  sim_smt_subsumption:                    0
% 3.38/0.99  
%------------------------------------------------------------------------------
