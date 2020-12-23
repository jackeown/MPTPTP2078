%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:41 EST 2020

% Result     : Theorem 31.55s
% Output     : CNFRefutation 31.55s
% Verified   : 
% Statistics : Number of formulae       :  234 (47369 expanded)
%              Number of clauses        :  182 (16272 expanded)
%              Number of leaves         :   18 (11784 expanded)
%              Depth                    :   40
%              Number of atoms          :  695 (214948 expanded)
%              Number of equality atoms :  457 (93848 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = o_1_0_funct_1(X0) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = o_1_0_funct_1(X0)
          | ~ r2_hidden(X3,X1) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = o_1_0_funct_1(X0)
              | ~ r2_hidden(X3,X1) )
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK4(X0,X1),X3) = o_1_0_funct_1(X0)
            | ~ r2_hidden(X3,X1) )
        & k1_relat_1(sK4(X0,X1)) = X1
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK4(X0,X1),X3) = o_1_0_funct_1(X0)
          | ~ r2_hidden(X3,X1) )
      & k1_relat_1(sK4(X0,X1)) = X1
      & v1_funct_1(sK4(X0,X1))
      & v1_relat_1(sK4(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f26])).

fof(f44,plain,(
    ! [X0,X1] : k1_relat_1(sK4(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f24,f23,f22])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f43,plain,(
    ! [X0,X1] : v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK5(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK5(X0,X1)) = X0
        & v1_funct_1(sK5(X0,X1))
        & v1_relat_1(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK5(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK5(X0,X1)) = X0
      & v1_funct_1(sK5(X0,X1))
      & v1_relat_1(sK5(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f28])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK5(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0,X1] : k1_relat_1(sK5(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f16,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK6)
          | k1_relat_1(X2) != sK7
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK7
        | k1_xboole_0 != sK6 ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK6)
        | k1_relat_1(X2) != sK7
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK7
      | k1_xboole_0 != sK6 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f17,f30])).

fof(f50,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK6)
      | k1_relat_1(X2) != sK7
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X0,X1] : v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f53,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK4(X0,X1),X3) = o_1_0_funct_1(X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_11,plain,
    ( k1_relat_1(sK4(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1931,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2787,plain,
    ( sK4(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X1
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1931])).

cnf(c_13,plain,
    ( v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_33,plain,
    ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2877,plain,
    ( k1_xboole_0 != X1
    | sK4(X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2787,c_33])).

cnf(c_2878,plain,
    ( sK4(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(renaming,[status(thm)],[c_2877])).

cnf(c_2880,plain,
    ( sK4(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_2878])).

cnf(c_3023,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2880,c_11])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1925,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3061,plain,
    ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3023,c_1925])).

cnf(c_35,plain,
    ( v1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_12,plain,
    ( v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_36,plain,
    ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_38,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_39,plain,
    ( k1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_657,plain,
    ( sK4(X0,X1) != X2
    | k1_relat_1(X2) != k1_xboole_0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_658,plain,
    ( k1_relat_1(sK4(X0,X1)) != k1_xboole_0
    | k1_xboole_0 = sK4(X0,X1) ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_659,plain,
    ( k1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 = sK4(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_1658,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2000,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK4(X1,X2))
    | X0 != sK4(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1658])).

cnf(c_2001,plain,
    ( X0 != sK4(X1,X2)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK4(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2000])).

cnf(c_2003,plain,
    ( k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0)
    | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2001])).

cnf(c_1655,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2066,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK4(X1,X2))
    | X0 != sK4(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1655])).

cnf(c_2067,plain,
    ( X0 != sK4(X1,X2)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK4(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2066])).

cnf(c_2069,plain,
    ( k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0)
    | v1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2067])).

cnf(c_7814,plain,
    ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3061,c_35,c_38,c_39,c_659,c_2003,c_2069])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK5(X1,X2),X0) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1921,plain,
    ( k1_funct_1(sK5(X0,X1),X2) = X1
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7821,plain,
    ( k1_funct_1(sK5(k1_xboole_0,X0),sK3(k1_xboole_0,X1)) = X0
    | r2_hidden(X1,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7814,c_1921])).

cnf(c_15,plain,
    ( k1_relat_1(sK5(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2788,plain,
    ( sK5(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(sK5(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1931])).

cnf(c_17,plain,
    ( v1_relat_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_23,plain,
    ( v1_relat_1(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2883,plain,
    ( k1_xboole_0 != X0
    | sK5(X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2788,c_23])).

cnf(c_2884,plain,
    ( sK5(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_2883])).

cnf(c_2886,plain,
    ( sK5(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_2884])).

cnf(c_7822,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1
    | r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7821,c_2886])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_34,plain,
    ( v1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_37,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1651,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1666,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1651])).

cnf(c_1652,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1957,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_1958,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1957])).

cnf(c_2002,plain,
    ( ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0))
    | v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2000])).

cnf(c_2068,plain,
    ( ~ v1_relat_1(sK4(k1_xboole_0,k1_xboole_0))
    | v1_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2066])).

cnf(c_1979,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_2026,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1979])).

cnf(c_2097,plain,
    ( k2_relat_1(X0) != sK6
    | sK6 = k2_relat_1(X0)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2026])).

cnf(c_2098,plain,
    ( k2_relat_1(k1_xboole_0) != sK6
    | sK6 = k2_relat_1(k1_xboole_0)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2097])).

cnf(c_2156,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1651])).

cnf(c_2054,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_2186,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2054])).

cnf(c_2187,plain,
    ( sK7 != sK7
    | sK7 = k1_xboole_0
    | k1_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_2186])).

cnf(c_2278,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1651])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(X0),sK6)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK7 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_205,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_relat_1(X2) != sK7
    | k2_relat_1(X2) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_206,plain,
    ( r2_hidden(sK0(k2_relat_1(X0),sK6),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK7 ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_1918,plain,
    ( k1_relat_1(X0) != sK7
    | r2_hidden(sK0(k2_relat_1(X0),sK6),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_206])).

cnf(c_3059,plain,
    ( sK7 != k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(k1_xboole_0),sK6),k2_relat_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3023,c_1918])).

cnf(c_3161,plain,
    ( sK7 != k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(k1_xboole_0),sK6),k2_relat_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3059,c_35,c_38,c_39,c_659,c_2003,c_2069])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_223,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_relat_1(X2) != sK7
    | k2_relat_1(X2) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_18])).

cnf(c_224,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(X0),sK6),sK6)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK7 ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_1917,plain,
    ( k1_relat_1(X0) != sK7
    | r2_hidden(sK0(k2_relat_1(X0),sK6),sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_3060,plain,
    ( sK7 != k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(k1_xboole_0),sK6),sK6) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3023,c_1917])).

cnf(c_3166,plain,
    ( sK7 != k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(k1_xboole_0),sK6),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3060,c_35,c_38,c_39,c_659,c_2003,c_2069])).

cnf(c_6,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1928,plain,
    ( k2_relat_1(X0) = X1
    | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3442,plain,
    ( k2_relat_1(sK4(X0,X1)) = X2
    | r2_hidden(sK2(sK4(X0,X1),X2),X1) = iProver_top
    | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1928])).

cnf(c_4190,plain,
    ( k2_relat_1(sK4(X0,X1)) = X2
    | r2_hidden(sK2(sK4(X0,X1),X2),X1) = iProver_top
    | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3442,c_33,c_36])).

cnf(c_1919,plain,
    ( v1_relat_1(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1920,plain,
    ( v1_funct_1(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2190,plain,
    ( sK7 != X0
    | r2_hidden(sK0(k2_relat_1(sK5(X0,X1)),sK6),k2_relat_1(sK5(X0,X1))) = iProver_top
    | v1_funct_1(sK5(X0,X1)) != iProver_top
    | v1_relat_1(sK5(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1918])).

cnf(c_26,plain,
    ( v1_funct_1(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2337,plain,
    ( sK7 != X0
    | r2_hidden(sK0(k2_relat_1(sK5(X0,X1)),sK6),k2_relat_1(sK5(X0,X1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2190,c_23,c_26])).

cnf(c_2343,plain,
    ( r2_hidden(sK0(k2_relat_1(sK5(sK7,X0)),sK6),k2_relat_1(sK5(sK7,X0))) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2337])).

cnf(c_2652,plain,
    ( k1_funct_1(sK5(k1_relat_1(X0),X1),sK3(X0,X2)) = X1
    | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1925,c_1921])).

cnf(c_5544,plain,
    ( k1_funct_1(sK5(k1_relat_1(sK5(sK7,X0)),X1),sK3(sK5(sK7,X0),sK0(k2_relat_1(sK5(sK7,X0)),sK6))) = X1
    | v1_funct_1(sK5(sK7,X0)) != iProver_top
    | v1_relat_1(sK5(sK7,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2343,c_2652])).

cnf(c_5557,plain,
    ( k1_funct_1(sK5(sK7,X0),sK3(sK5(sK7,X1),sK0(k2_relat_1(sK5(sK7,X1)),sK6))) = X0
    | v1_funct_1(sK5(sK7,X1)) != iProver_top
    | v1_relat_1(sK5(sK7,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5544,c_15])).

cnf(c_5759,plain,
    ( k1_funct_1(sK5(sK7,X0),sK3(sK5(sK7,X1),sK0(k2_relat_1(sK5(sK7,X1)),sK6))) = X0
    | v1_relat_1(sK5(sK7,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1920,c_5557])).

cnf(c_6382,plain,
    ( k1_funct_1(sK5(sK7,X0),sK3(sK5(sK7,X1),sK0(k2_relat_1(sK5(sK7,X1)),sK6))) = X0 ),
    inference(superposition,[status(thm)],[c_1919,c_5759])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1926,plain,
    ( k1_funct_1(X0,sK3(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3245,plain,
    ( k1_funct_1(sK5(sK7,X0),sK3(sK5(sK7,X0),sK0(k2_relat_1(sK5(sK7,X0)),sK6))) = sK0(k2_relat_1(sK5(sK7,X0)),sK6)
    | v1_funct_1(sK5(sK7,X0)) != iProver_top
    | v1_relat_1(sK5(sK7,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2343,c_1926])).

cnf(c_2046,plain,
    ( v1_funct_1(sK5(sK7,X0)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2047,plain,
    ( v1_funct_1(sK5(sK7,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2046])).

cnf(c_2145,plain,
    ( v1_relat_1(sK5(sK7,X0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2146,plain,
    ( v1_relat_1(sK5(sK7,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2145])).

cnf(c_3653,plain,
    ( k1_funct_1(sK5(sK7,X0),sK3(sK5(sK7,X0),sK0(k2_relat_1(sK5(sK7,X0)),sK6))) = sK0(k2_relat_1(sK5(sK7,X0)),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3245,c_2047,c_2146])).

cnf(c_7358,plain,
    ( sK0(k2_relat_1(sK5(sK7,X0)),sK6) = X0 ),
    inference(demodulation,[status(thm)],[c_6382,c_3653])).

cnf(c_2191,plain,
    ( sK7 != X0
    | r2_hidden(sK0(k2_relat_1(sK5(X0,X1)),sK6),sK6) != iProver_top
    | v1_funct_1(sK5(X0,X1)) != iProver_top
    | v1_relat_1(sK5(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1917])).

cnf(c_2253,plain,
    ( sK7 != X0
    | r2_hidden(sK0(k2_relat_1(sK5(X0,X1)),sK6),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2191,c_23,c_26])).

cnf(c_2259,plain,
    ( r2_hidden(sK0(k2_relat_1(sK5(sK7,X0)),sK6),sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2253])).

cnf(c_7373,plain,
    ( r2_hidden(X0,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7358,c_2259])).

cnf(c_7459,plain,
    ( k2_relat_1(sK4(X0,X1)) = sK6
    | r2_hidden(sK2(sK4(X0,X1),sK6),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4190,c_7373])).

cnf(c_8208,plain,
    ( k1_funct_1(sK5(X0,X1),sK2(sK4(X2,X0),sK6)) = X1
    | k2_relat_1(sK4(X2,X0)) = sK6 ),
    inference(superposition,[status(thm)],[c_7459,c_1921])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1927,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_16231,plain,
    ( k2_relat_1(sK4(X0,X1)) = sK6
    | r2_hidden(X2,k2_relat_1(sK5(X1,X2))) = iProver_top
    | r2_hidden(sK2(sK4(X0,X1),sK6),k1_relat_1(sK5(X1,X2))) != iProver_top
    | v1_funct_1(sK5(X1,X2)) != iProver_top
    | v1_relat_1(sK5(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8208,c_1927])).

cnf(c_16232,plain,
    ( k2_relat_1(sK4(X0,X1)) = sK6
    | r2_hidden(X2,k2_relat_1(sK5(X1,X2))) = iProver_top
    | r2_hidden(sK2(sK4(X0,X1),sK6),X1) != iProver_top
    | v1_funct_1(sK5(X1,X2)) != iProver_top
    | v1_relat_1(sK5(X1,X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16231,c_15])).

cnf(c_16551,plain,
    ( r2_hidden(X2,k2_relat_1(sK5(X1,X2))) = iProver_top
    | k2_relat_1(sK4(X0,X1)) = sK6
    | v1_funct_1(sK5(X1,X2)) != iProver_top
    | v1_relat_1(sK5(X1,X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16232,c_7459])).

cnf(c_16552,plain,
    ( k2_relat_1(sK4(X0,X1)) = sK6
    | r2_hidden(X2,k2_relat_1(sK5(X1,X2))) = iProver_top
    | v1_funct_1(sK5(X1,X2)) != iProver_top
    | v1_relat_1(sK5(X1,X2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_16551])).

cnf(c_16565,plain,
    ( k1_funct_1(sK5(k1_relat_1(sK5(X0,X1)),X2),sK3(sK5(X0,X1),X1)) = X2
    | k2_relat_1(sK4(X3,X0)) = sK6
    | v1_funct_1(sK5(X0,X1)) != iProver_top
    | v1_relat_1(sK5(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16552,c_2652])).

cnf(c_16572,plain,
    ( k1_funct_1(sK5(X0,X1),sK3(sK5(X0,X2),X2)) = X1
    | k2_relat_1(sK4(X3,X0)) = sK6
    | v1_funct_1(sK5(X0,X2)) != iProver_top
    | v1_relat_1(sK5(X0,X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16565,c_15])).

cnf(c_16605,plain,
    ( k1_funct_1(sK5(k1_xboole_0,X0),sK3(sK5(k1_xboole_0,X1),X1)) = X0
    | k2_relat_1(sK4(X2,k1_xboole_0)) = sK6
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(sK5(k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2886,c_16572])).

cnf(c_16666,plain,
    ( k1_funct_1(k1_xboole_0,sK3(sK5(k1_xboole_0,X0),X0)) = X1
    | k2_relat_1(sK4(X2,k1_xboole_0)) = sK6
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(sK5(k1_xboole_0,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16605,c_2886])).

cnf(c_16667,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1
    | k2_relat_1(k1_xboole_0) = sK6
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16666,c_2880,c_2886])).

cnf(c_16668,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1
    | k2_relat_1(k1_xboole_0) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16667])).

cnf(c_1654,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3912,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_relat_1(X2),sK6),k2_relat_1(X2))
    | X0 != sK0(k2_relat_1(X2),sK6)
    | X1 != k2_relat_1(X2) ),
    inference(instantiation,[status(thm)],[c_1654])).

cnf(c_12186,plain,
    ( r2_hidden(sK0(k2_relat_1(X0),sK6),X1)
    | ~ r2_hidden(sK0(k2_relat_1(X0),sK6),k2_relat_1(X0))
    | X1 != k2_relat_1(X0)
    | sK0(k2_relat_1(X0),sK6) != sK0(k2_relat_1(X0),sK6) ),
    inference(instantiation,[status(thm)],[c_3912])).

cnf(c_25066,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(X0),sK6),k2_relat_1(X0))
    | r2_hidden(sK0(k2_relat_1(X0),sK6),sK6)
    | sK0(k2_relat_1(X0),sK6) != sK0(k2_relat_1(X0),sK6)
    | sK6 != k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_12186])).

cnf(c_25067,plain,
    ( sK0(k2_relat_1(X0),sK6) != sK0(k2_relat_1(X0),sK6)
    | sK6 != k2_relat_1(X0)
    | r2_hidden(sK0(k2_relat_1(X0),sK6),k2_relat_1(X0)) != iProver_top
    | r2_hidden(sK0(k2_relat_1(X0),sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25066])).

cnf(c_25069,plain,
    ( sK0(k2_relat_1(k1_xboole_0),sK6) != sK0(k2_relat_1(k1_xboole_0),sK6)
    | sK6 != k2_relat_1(k1_xboole_0)
    | r2_hidden(sK0(k2_relat_1(k1_xboole_0),sK6),k2_relat_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK0(k2_relat_1(k1_xboole_0),sK6),sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_25067])).

cnf(c_7463,plain,
    ( k2_relat_1(sK4(X0,sK6)) = X1
    | r2_hidden(sK1(sK4(X0,sK6),X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4190,c_7373])).

cnf(c_8210,plain,
    ( k2_relat_1(sK4(X0,sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_7459,c_7373])).

cnf(c_8547,plain,
    ( sK6 = X0
    | r2_hidden(sK1(sK4(X1,sK6),X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7463,c_8210])).

cnf(c_8552,plain,
    ( k1_funct_1(sK5(X0,X1),sK1(sK4(X2,sK6),X0)) = X1
    | sK6 = X0 ),
    inference(superposition,[status(thm)],[c_8547,c_1921])).

cnf(c_35683,plain,
    ( sK6 = X0
    | r2_hidden(X1,k2_relat_1(sK5(X0,X1))) = iProver_top
    | r2_hidden(sK1(sK4(X2,sK6),X0),k1_relat_1(sK5(X0,X1))) != iProver_top
    | v1_funct_1(sK5(X0,X1)) != iProver_top
    | v1_relat_1(sK5(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8552,c_1927])).

cnf(c_35684,plain,
    ( sK6 = X0
    | r2_hidden(X1,k2_relat_1(sK5(X0,X1))) = iProver_top
    | r2_hidden(sK1(sK4(X2,sK6),X0),X0) != iProver_top
    | v1_funct_1(sK5(X0,X1)) != iProver_top
    | v1_relat_1(sK5(X0,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_35683,c_15])).

cnf(c_36477,plain,
    ( sK6 = X0
    | r2_hidden(X1,k2_relat_1(sK5(X0,X1))) = iProver_top
    | r2_hidden(sK1(sK4(X2,sK6),X0),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35684,c_23,c_26])).

cnf(c_36490,plain,
    ( sK6 = X0
    | r2_hidden(X1,k2_relat_1(sK5(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8547,c_36477])).

cnf(c_36744,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2886,c_36490])).

cnf(c_65151,plain,
    ( sK0(k2_relat_1(X0),sK6) = sK0(k2_relat_1(X0),sK6) ),
    inference(instantiation,[status(thm)],[c_1651])).

cnf(c_65153,plain,
    ( sK0(k2_relat_1(k1_xboole_0),sK6) = sK0(k2_relat_1(k1_xboole_0),sK6) ),
    inference(instantiation,[status(thm)],[c_65151])).

cnf(c_83160,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7822,c_19,c_34,c_37,c_39,c_659,c_1666,c_1958,c_2002,c_2068,c_2098,c_2156,c_2187,c_2278,c_3161,c_3166,c_16668,c_25069,c_36744,c_65153])).

cnf(c_3443,plain,
    ( k2_relat_1(sK5(X0,X1)) = X2
    | r2_hidden(sK2(sK5(X0,X1),X2),X0) = iProver_top
    | r2_hidden(sK1(sK5(X0,X1),X2),X2) = iProver_top
    | v1_funct_1(sK5(X0,X1)) != iProver_top
    | v1_relat_1(sK5(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1928])).

cnf(c_4260,plain,
    ( k2_relat_1(sK5(X0,X1)) = X2
    | r2_hidden(sK2(sK5(X0,X1),X2),X0) = iProver_top
    | r2_hidden(sK1(sK5(X0,X1),X2),X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3443,c_23,c_26])).

cnf(c_7460,plain,
    ( k2_relat_1(sK5(X0,X1)) = sK6
    | r2_hidden(sK2(sK5(X0,X1),sK6),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4260,c_7373])).

cnf(c_8387,plain,
    ( k2_relat_1(sK5(sK6,X0)) = sK6 ),
    inference(superposition,[status(thm)],[c_7460,c_7373])).

cnf(c_84053,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = sK6 ),
    inference(superposition,[status(thm)],[c_83160,c_8387])).

cnf(c_84135,plain,
    ( k1_relat_1(k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0))) = X1 ),
    inference(superposition,[status(thm)],[c_83160,c_11])).

cnf(c_84319,plain,
    ( k1_relat_1(k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_84135,c_2886])).

cnf(c_1922,plain,
    ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1923,plain,
    ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2058,plain,
    ( sK7 != X0
    | r2_hidden(sK0(k2_relat_1(sK4(X1,X0)),sK6),k2_relat_1(sK4(X1,X0))) = iProver_top
    | v1_funct_1(sK4(X1,X0)) != iProver_top
    | v1_relat_1(sK4(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1918])).

cnf(c_2121,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(X0,sK7)),sK6),k2_relat_1(sK4(X0,sK7))) = iProver_top
    | v1_funct_1(sK4(X0,sK7)) != iProver_top
    | v1_relat_1(sK4(X0,sK7)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2058])).

cnf(c_2041,plain,
    ( v1_funct_1(sK4(X0,sK7)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2042,plain,
    ( v1_funct_1(sK4(X0,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2041])).

cnf(c_2135,plain,
    ( v1_relat_1(sK4(X0,sK7)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2136,plain,
    ( v1_relat_1(sK4(X0,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2135])).

cnf(c_2172,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4(X0,sK7)),sK6),k2_relat_1(sK4(X0,sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2121,c_2042,c_2136])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK4(X2,X1),X0) = o_1_0_funct_1(X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1924,plain,
    ( k1_funct_1(sK4(X0,X1),X2) = o_1_0_funct_1(X0)
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2651,plain,
    ( k1_funct_1(sK4(X0,k1_relat_1(X1)),sK3(X1,X2)) = o_1_0_funct_1(X0)
    | r2_hidden(X2,k2_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1925,c_1924])).

cnf(c_4723,plain,
    ( k1_funct_1(sK4(X0,k1_relat_1(sK4(X1,sK7))),sK3(sK4(X1,sK7),sK0(k2_relat_1(sK4(X1,sK7)),sK6))) = o_1_0_funct_1(X0)
    | v1_funct_1(sK4(X1,sK7)) != iProver_top
    | v1_relat_1(sK4(X1,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2172,c_2651])).

cnf(c_4734,plain,
    ( k1_funct_1(sK4(X0,sK7),sK3(sK4(X1,sK7),sK0(k2_relat_1(sK4(X1,sK7)),sK6))) = o_1_0_funct_1(X0)
    | v1_funct_1(sK4(X1,sK7)) != iProver_top
    | v1_relat_1(sK4(X1,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4723,c_11])).

cnf(c_4835,plain,
    ( k1_funct_1(sK4(X0,sK7),sK3(sK4(X1,sK7),sK0(k2_relat_1(sK4(X1,sK7)),sK6))) = o_1_0_funct_1(X0)
    | v1_relat_1(sK4(X1,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1923,c_4734])).

cnf(c_5008,plain,
    ( k1_funct_1(sK4(X0,sK7),sK3(sK4(X1,sK7),sK0(k2_relat_1(sK4(X1,sK7)),sK6))) = o_1_0_funct_1(X0) ),
    inference(superposition,[status(thm)],[c_1922,c_4835])).

cnf(c_3244,plain,
    ( k1_funct_1(sK4(X0,sK7),sK3(sK4(X0,sK7),sK0(k2_relat_1(sK4(X0,sK7)),sK6))) = sK0(k2_relat_1(sK4(X0,sK7)),sK6)
    | v1_funct_1(sK4(X0,sK7)) != iProver_top
    | v1_relat_1(sK4(X0,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2172,c_1926])).

cnf(c_3627,plain,
    ( k1_funct_1(sK4(X0,sK7),sK3(sK4(X0,sK7),sK0(k2_relat_1(sK4(X0,sK7)),sK6))) = sK0(k2_relat_1(sK4(X0,sK7)),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3244,c_2042,c_2136])).

cnf(c_25427,plain,
    ( sK0(k2_relat_1(sK4(X0,sK7)),sK6) = o_1_0_funct_1(X0) ),
    inference(demodulation,[status(thm)],[c_5008,c_3627])).

cnf(c_84339,plain,
    ( k1_relat_1(k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0))) = o_1_0_funct_1(X1) ),
    inference(superposition,[status(thm)],[c_84135,c_25427])).

cnf(c_4724,plain,
    ( k1_funct_1(sK4(X0,k1_relat_1(sK5(sK7,X1))),sK3(sK5(sK7,X1),sK0(k2_relat_1(sK5(sK7,X1)),sK6))) = o_1_0_funct_1(X0)
    | v1_funct_1(sK5(sK7,X1)) != iProver_top
    | v1_relat_1(sK5(sK7,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2343,c_2651])).

cnf(c_4733,plain,
    ( k1_funct_1(sK4(X0,sK7),sK3(sK5(sK7,X1),sK0(k2_relat_1(sK5(sK7,X1)),sK6))) = o_1_0_funct_1(X0)
    | v1_funct_1(sK5(sK7,X1)) != iProver_top
    | v1_relat_1(sK5(sK7,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4724,c_15])).

cnf(c_4775,plain,
    ( k1_funct_1(sK4(X0,sK7),sK3(sK5(sK7,X1),sK0(k2_relat_1(sK5(sK7,X1)),sK6))) = o_1_0_funct_1(X0)
    | v1_relat_1(sK5(sK7,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1920,c_4733])).

cnf(c_4890,plain,
    ( k1_funct_1(sK4(X0,sK7),sK3(sK5(sK7,X1),sK0(k2_relat_1(sK5(sK7,X1)),sK6))) = o_1_0_funct_1(X0) ),
    inference(superposition,[status(thm)],[c_1919,c_4775])).

cnf(c_25012,plain,
    ( k1_funct_1(sK4(X0,sK7),sK3(sK5(sK7,X1),X1)) = o_1_0_funct_1(X0) ),
    inference(demodulation,[status(thm)],[c_4890,c_7358])).

cnf(c_84096,plain,
    ( k1_funct_1(k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)),sK3(sK5(sK7,X1),X1)) = o_1_0_funct_1(X2) ),
    inference(superposition,[status(thm)],[c_83160,c_25012])).

cnf(c_84159,plain,
    ( o_1_0_funct_1(X0) = sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_84096])).

cnf(c_84948,plain,
    ( k1_relat_1(k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_84339,c_84159])).

cnf(c_85011,plain,
    ( sP1_iProver_split = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_84319,c_84948])).

cnf(c_84090,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = o_1_0_funct_1(X1) ),
    inference(superposition,[status(thm)],[c_83160,c_25427])).

cnf(c_86243,plain,
    ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_84090,c_84159])).

cnf(c_86244,plain,
    ( k1_funct_1(sP1_iProver_split,sK3(sP1_iProver_split,X0)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_86243,c_85011])).

cnf(c_87423,plain,
    ( sP1_iProver_split = sK6 ),
    inference(light_normalisation,[status(thm)],[c_84053,c_85011,c_86244])).

cnf(c_92770,plain,
    ( r2_hidden(X0,sP1_iProver_split) != iProver_top ),
    inference(demodulation,[status(thm)],[c_87423,c_7373])).

cnf(c_7372,plain,
    ( r2_hidden(X0,k2_relat_1(sK5(sK7,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7358,c_2343])).

cnf(c_84084,plain,
    ( r2_hidden(X0,k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_83160,c_7372])).

cnf(c_87335,plain,
    ( r2_hidden(X0,k1_funct_1(sP1_iProver_split,sK3(sP1_iProver_split,X1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_84084,c_85011])).

cnf(c_87336,plain,
    ( r2_hidden(X0,sP1_iProver_split) = iProver_top ),
    inference(demodulation,[status(thm)],[c_87335,c_86244])).

cnf(c_92781,plain,
    ( r2_hidden(k1_xboole_0,sP1_iProver_split) != iProver_top ),
    inference(grounding,[status(thm)],[c_92770:[bind(X0,$fot(k1_xboole_0))]])).

cnf(c_92782,plain,
    ( r2_hidden(k1_xboole_0,sP1_iProver_split) = iProver_top ),
    inference(grounding,[status(thm)],[c_87336:[bind(X0,$fot(k1_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_92781,c_92782])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:30:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 31.55/4.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.55/4.49  
% 31.55/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.55/4.49  
% 31.55/4.49  ------  iProver source info
% 31.55/4.49  
% 31.55/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.55/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.55/4.49  git: non_committed_changes: false
% 31.55/4.49  git: last_make_outside_of_git: false
% 31.55/4.49  
% 31.55/4.49  ------ 
% 31.55/4.49  
% 31.55/4.49  ------ Input Options
% 31.55/4.49  
% 31.55/4.49  --out_options                           all
% 31.55/4.49  --tptp_safe_out                         true
% 31.55/4.49  --problem_path                          ""
% 31.55/4.49  --include_path                          ""
% 31.55/4.49  --clausifier                            res/vclausify_rel
% 31.55/4.49  --clausifier_options                    ""
% 31.55/4.49  --stdin                                 false
% 31.55/4.49  --stats_out                             all
% 31.55/4.49  
% 31.55/4.49  ------ General Options
% 31.55/4.49  
% 31.55/4.49  --fof                                   false
% 31.55/4.49  --time_out_real                         305.
% 31.55/4.49  --time_out_virtual                      -1.
% 31.55/4.49  --symbol_type_check                     false
% 31.55/4.49  --clausify_out                          false
% 31.55/4.49  --sig_cnt_out                           false
% 31.55/4.49  --trig_cnt_out                          false
% 31.55/4.49  --trig_cnt_out_tolerance                1.
% 31.55/4.49  --trig_cnt_out_sk_spl                   false
% 31.55/4.49  --abstr_cl_out                          false
% 31.55/4.49  
% 31.55/4.49  ------ Global Options
% 31.55/4.49  
% 31.55/4.49  --schedule                              default
% 31.55/4.49  --add_important_lit                     false
% 31.55/4.49  --prop_solver_per_cl                    1000
% 31.55/4.49  --min_unsat_core                        false
% 31.55/4.49  --soft_assumptions                      false
% 31.55/4.49  --soft_lemma_size                       3
% 31.55/4.49  --prop_impl_unit_size                   0
% 31.55/4.49  --prop_impl_unit                        []
% 31.55/4.49  --share_sel_clauses                     true
% 31.55/4.49  --reset_solvers                         false
% 31.55/4.49  --bc_imp_inh                            [conj_cone]
% 31.55/4.49  --conj_cone_tolerance                   3.
% 31.55/4.49  --extra_neg_conj                        none
% 31.55/4.49  --large_theory_mode                     true
% 31.55/4.49  --prolific_symb_bound                   200
% 31.55/4.49  --lt_threshold                          2000
% 31.55/4.49  --clause_weak_htbl                      true
% 31.55/4.49  --gc_record_bc_elim                     false
% 31.55/4.49  
% 31.55/4.49  ------ Preprocessing Options
% 31.55/4.49  
% 31.55/4.49  --preprocessing_flag                    true
% 31.55/4.49  --time_out_prep_mult                    0.1
% 31.55/4.49  --splitting_mode                        input
% 31.55/4.49  --splitting_grd                         true
% 31.55/4.49  --splitting_cvd                         false
% 31.55/4.49  --splitting_cvd_svl                     false
% 31.55/4.49  --splitting_nvd                         32
% 31.55/4.49  --sub_typing                            true
% 31.55/4.49  --prep_gs_sim                           true
% 31.55/4.49  --prep_unflatten                        true
% 31.55/4.49  --prep_res_sim                          true
% 31.55/4.49  --prep_upred                            true
% 31.55/4.49  --prep_sem_filter                       exhaustive
% 31.55/4.49  --prep_sem_filter_out                   false
% 31.55/4.49  --pred_elim                             true
% 31.55/4.49  --res_sim_input                         true
% 31.55/4.49  --eq_ax_congr_red                       true
% 31.55/4.49  --pure_diseq_elim                       true
% 31.55/4.49  --brand_transform                       false
% 31.55/4.49  --non_eq_to_eq                          false
% 31.55/4.49  --prep_def_merge                        true
% 31.55/4.49  --prep_def_merge_prop_impl              false
% 31.55/4.49  --prep_def_merge_mbd                    true
% 31.55/4.49  --prep_def_merge_tr_red                 false
% 31.55/4.49  --prep_def_merge_tr_cl                  false
% 31.55/4.49  --smt_preprocessing                     true
% 31.55/4.49  --smt_ac_axioms                         fast
% 31.55/4.49  --preprocessed_out                      false
% 31.55/4.49  --preprocessed_stats                    false
% 31.55/4.49  
% 31.55/4.49  ------ Abstraction refinement Options
% 31.55/4.49  
% 31.55/4.49  --abstr_ref                             []
% 31.55/4.49  --abstr_ref_prep                        false
% 31.55/4.49  --abstr_ref_until_sat                   false
% 31.55/4.49  --abstr_ref_sig_restrict                funpre
% 31.55/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.55/4.49  --abstr_ref_under                       []
% 31.55/4.49  
% 31.55/4.49  ------ SAT Options
% 31.55/4.49  
% 31.55/4.49  --sat_mode                              false
% 31.55/4.49  --sat_fm_restart_options                ""
% 31.55/4.49  --sat_gr_def                            false
% 31.55/4.49  --sat_epr_types                         true
% 31.55/4.49  --sat_non_cyclic_types                  false
% 31.55/4.49  --sat_finite_models                     false
% 31.55/4.49  --sat_fm_lemmas                         false
% 31.55/4.49  --sat_fm_prep                           false
% 31.55/4.49  --sat_fm_uc_incr                        true
% 31.55/4.49  --sat_out_model                         small
% 31.55/4.49  --sat_out_clauses                       false
% 31.55/4.49  
% 31.55/4.49  ------ QBF Options
% 31.55/4.49  
% 31.55/4.49  --qbf_mode                              false
% 31.55/4.49  --qbf_elim_univ                         false
% 31.55/4.49  --qbf_dom_inst                          none
% 31.55/4.49  --qbf_dom_pre_inst                      false
% 31.55/4.49  --qbf_sk_in                             false
% 31.55/4.49  --qbf_pred_elim                         true
% 31.55/4.49  --qbf_split                             512
% 31.55/4.49  
% 31.55/4.49  ------ BMC1 Options
% 31.55/4.49  
% 31.55/4.49  --bmc1_incremental                      false
% 31.55/4.49  --bmc1_axioms                           reachable_all
% 31.55/4.49  --bmc1_min_bound                        0
% 31.55/4.49  --bmc1_max_bound                        -1
% 31.55/4.49  --bmc1_max_bound_default                -1
% 31.55/4.49  --bmc1_symbol_reachability              true
% 31.55/4.49  --bmc1_property_lemmas                  false
% 31.55/4.49  --bmc1_k_induction                      false
% 31.55/4.49  --bmc1_non_equiv_states                 false
% 31.55/4.49  --bmc1_deadlock                         false
% 31.55/4.49  --bmc1_ucm                              false
% 31.55/4.49  --bmc1_add_unsat_core                   none
% 31.55/4.49  --bmc1_unsat_core_children              false
% 31.55/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.55/4.49  --bmc1_out_stat                         full
% 31.55/4.49  --bmc1_ground_init                      false
% 31.55/4.49  --bmc1_pre_inst_next_state              false
% 31.55/4.49  --bmc1_pre_inst_state                   false
% 31.55/4.49  --bmc1_pre_inst_reach_state             false
% 31.55/4.49  --bmc1_out_unsat_core                   false
% 31.55/4.49  --bmc1_aig_witness_out                  false
% 31.55/4.49  --bmc1_verbose                          false
% 31.55/4.49  --bmc1_dump_clauses_tptp                false
% 31.55/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.55/4.49  --bmc1_dump_file                        -
% 31.55/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.55/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.55/4.49  --bmc1_ucm_extend_mode                  1
% 31.55/4.49  --bmc1_ucm_init_mode                    2
% 31.55/4.49  --bmc1_ucm_cone_mode                    none
% 31.55/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.55/4.49  --bmc1_ucm_relax_model                  4
% 31.55/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.55/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.55/4.49  --bmc1_ucm_layered_model                none
% 31.55/4.49  --bmc1_ucm_max_lemma_size               10
% 31.55/4.49  
% 31.55/4.49  ------ AIG Options
% 31.55/4.49  
% 31.55/4.49  --aig_mode                              false
% 31.55/4.49  
% 31.55/4.49  ------ Instantiation Options
% 31.55/4.49  
% 31.55/4.49  --instantiation_flag                    true
% 31.55/4.49  --inst_sos_flag                         true
% 31.55/4.49  --inst_sos_phase                        true
% 31.55/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.55/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.55/4.49  --inst_lit_sel_side                     num_symb
% 31.55/4.49  --inst_solver_per_active                1400
% 31.55/4.49  --inst_solver_calls_frac                1.
% 31.55/4.49  --inst_passive_queue_type               priority_queues
% 31.55/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.55/4.49  --inst_passive_queues_freq              [25;2]
% 31.55/4.49  --inst_dismatching                      true
% 31.55/4.49  --inst_eager_unprocessed_to_passive     true
% 31.55/4.49  --inst_prop_sim_given                   true
% 31.55/4.49  --inst_prop_sim_new                     false
% 31.55/4.49  --inst_subs_new                         false
% 31.55/4.49  --inst_eq_res_simp                      false
% 31.55/4.49  --inst_subs_given                       false
% 31.55/4.49  --inst_orphan_elimination               true
% 31.55/4.49  --inst_learning_loop_flag               true
% 31.55/4.49  --inst_learning_start                   3000
% 31.55/4.49  --inst_learning_factor                  2
% 31.55/4.49  --inst_start_prop_sim_after_learn       3
% 31.55/4.49  --inst_sel_renew                        solver
% 31.55/4.49  --inst_lit_activity_flag                true
% 31.55/4.49  --inst_restr_to_given                   false
% 31.55/4.49  --inst_activity_threshold               500
% 31.55/4.49  --inst_out_proof                        true
% 31.55/4.49  
% 31.55/4.49  ------ Resolution Options
% 31.55/4.49  
% 31.55/4.49  --resolution_flag                       true
% 31.55/4.49  --res_lit_sel                           adaptive
% 31.55/4.49  --res_lit_sel_side                      none
% 31.55/4.49  --res_ordering                          kbo
% 31.55/4.49  --res_to_prop_solver                    active
% 31.55/4.49  --res_prop_simpl_new                    false
% 31.55/4.49  --res_prop_simpl_given                  true
% 31.55/4.49  --res_passive_queue_type                priority_queues
% 31.55/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.55/4.49  --res_passive_queues_freq               [15;5]
% 31.55/4.49  --res_forward_subs                      full
% 31.55/4.49  --res_backward_subs                     full
% 31.55/4.49  --res_forward_subs_resolution           true
% 31.55/4.49  --res_backward_subs_resolution          true
% 31.55/4.49  --res_orphan_elimination                true
% 31.55/4.49  --res_time_limit                        2.
% 31.55/4.49  --res_out_proof                         true
% 31.55/4.49  
% 31.55/4.49  ------ Superposition Options
% 31.55/4.49  
% 31.55/4.49  --superposition_flag                    true
% 31.55/4.49  --sup_passive_queue_type                priority_queues
% 31.55/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.55/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.55/4.49  --demod_completeness_check              fast
% 31.55/4.49  --demod_use_ground                      true
% 31.55/4.49  --sup_to_prop_solver                    passive
% 31.55/4.49  --sup_prop_simpl_new                    true
% 31.55/4.49  --sup_prop_simpl_given                  true
% 31.55/4.49  --sup_fun_splitting                     true
% 31.55/4.49  --sup_smt_interval                      50000
% 31.55/4.49  
% 31.55/4.49  ------ Superposition Simplification Setup
% 31.55/4.49  
% 31.55/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.55/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.55/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.55/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.55/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.55/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.55/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.55/4.49  --sup_immed_triv                        [TrivRules]
% 31.55/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.55/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.55/4.49  --sup_immed_bw_main                     []
% 31.55/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.55/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.55/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.55/4.49  --sup_input_bw                          []
% 31.55/4.49  
% 31.55/4.49  ------ Combination Options
% 31.55/4.49  
% 31.55/4.49  --comb_res_mult                         3
% 31.55/4.49  --comb_sup_mult                         2
% 31.55/4.49  --comb_inst_mult                        10
% 31.55/4.49  
% 31.55/4.49  ------ Debug Options
% 31.55/4.49  
% 31.55/4.49  --dbg_backtrace                         false
% 31.55/4.49  --dbg_dump_prop_clauses                 false
% 31.55/4.49  --dbg_dump_prop_clauses_file            -
% 31.55/4.49  --dbg_out_stat                          false
% 31.55/4.49  ------ Parsing...
% 31.55/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.55/4.49  
% 31.55/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 31.55/4.49  
% 31.55/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.55/4.49  
% 31.55/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.55/4.49  ------ Proving...
% 31.55/4.49  ------ Problem Properties 
% 31.55/4.49  
% 31.55/4.49  
% 31.55/4.49  clauses                                 19
% 31.55/4.49  conjectures                             1
% 31.55/4.49  EPR                                     1
% 31.55/4.49  Horn                                    17
% 31.55/4.49  unary                                   6
% 31.55/4.49  binary                                  3
% 31.55/4.49  lits                                    54
% 31.55/4.49  lits eq                                 18
% 31.55/4.49  fd_pure                                 0
% 31.55/4.49  fd_pseudo                               0
% 31.55/4.49  fd_cond                                 2
% 31.55/4.49  fd_pseudo_cond                          3
% 31.55/4.49  AC symbols                              0
% 31.55/4.49  
% 31.55/4.49  ------ Schedule dynamic 5 is on 
% 31.55/4.49  
% 31.55/4.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.55/4.49  
% 31.55/4.49  
% 31.55/4.49  ------ 
% 31.55/4.49  Current options:
% 31.55/4.49  ------ 
% 31.55/4.49  
% 31.55/4.49  ------ Input Options
% 31.55/4.49  
% 31.55/4.49  --out_options                           all
% 31.55/4.49  --tptp_safe_out                         true
% 31.55/4.49  --problem_path                          ""
% 31.55/4.49  --include_path                          ""
% 31.55/4.49  --clausifier                            res/vclausify_rel
% 31.55/4.49  --clausifier_options                    ""
% 31.55/4.49  --stdin                                 false
% 31.55/4.49  --stats_out                             all
% 31.55/4.49  
% 31.55/4.49  ------ General Options
% 31.55/4.49  
% 31.55/4.49  --fof                                   false
% 31.55/4.49  --time_out_real                         305.
% 31.55/4.49  --time_out_virtual                      -1.
% 31.55/4.49  --symbol_type_check                     false
% 31.55/4.49  --clausify_out                          false
% 31.55/4.49  --sig_cnt_out                           false
% 31.55/4.49  --trig_cnt_out                          false
% 31.55/4.49  --trig_cnt_out_tolerance                1.
% 31.55/4.49  --trig_cnt_out_sk_spl                   false
% 31.55/4.49  --abstr_cl_out                          false
% 31.55/4.49  
% 31.55/4.49  ------ Global Options
% 31.55/4.49  
% 31.55/4.49  --schedule                              default
% 31.55/4.49  --add_important_lit                     false
% 31.55/4.49  --prop_solver_per_cl                    1000
% 31.55/4.49  --min_unsat_core                        false
% 31.55/4.49  --soft_assumptions                      false
% 31.55/4.49  --soft_lemma_size                       3
% 31.55/4.49  --prop_impl_unit_size                   0
% 31.55/4.49  --prop_impl_unit                        []
% 31.55/4.49  --share_sel_clauses                     true
% 31.55/4.49  --reset_solvers                         false
% 31.55/4.49  --bc_imp_inh                            [conj_cone]
% 31.55/4.49  --conj_cone_tolerance                   3.
% 31.55/4.49  --extra_neg_conj                        none
% 31.55/4.49  --large_theory_mode                     true
% 31.55/4.49  --prolific_symb_bound                   200
% 31.55/4.49  --lt_threshold                          2000
% 31.55/4.49  --clause_weak_htbl                      true
% 31.55/4.49  --gc_record_bc_elim                     false
% 31.55/4.49  
% 31.55/4.49  ------ Preprocessing Options
% 31.55/4.49  
% 31.55/4.49  --preprocessing_flag                    true
% 31.55/4.49  --time_out_prep_mult                    0.1
% 31.55/4.49  --splitting_mode                        input
% 31.55/4.49  --splitting_grd                         true
% 31.55/4.49  --splitting_cvd                         false
% 31.55/4.49  --splitting_cvd_svl                     false
% 31.55/4.49  --splitting_nvd                         32
% 31.55/4.49  --sub_typing                            true
% 31.55/4.49  --prep_gs_sim                           true
% 31.55/4.49  --prep_unflatten                        true
% 31.55/4.49  --prep_res_sim                          true
% 31.55/4.49  --prep_upred                            true
% 31.55/4.49  --prep_sem_filter                       exhaustive
% 31.55/4.49  --prep_sem_filter_out                   false
% 31.55/4.49  --pred_elim                             true
% 31.55/4.49  --res_sim_input                         true
% 31.55/4.49  --eq_ax_congr_red                       true
% 31.55/4.49  --pure_diseq_elim                       true
% 31.55/4.49  --brand_transform                       false
% 31.55/4.49  --non_eq_to_eq                          false
% 31.55/4.49  --prep_def_merge                        true
% 31.55/4.49  --prep_def_merge_prop_impl              false
% 31.55/4.49  --prep_def_merge_mbd                    true
% 31.55/4.49  --prep_def_merge_tr_red                 false
% 31.55/4.49  --prep_def_merge_tr_cl                  false
% 31.55/4.49  --smt_preprocessing                     true
% 31.55/4.49  --smt_ac_axioms                         fast
% 31.55/4.49  --preprocessed_out                      false
% 31.55/4.49  --preprocessed_stats                    false
% 31.55/4.49  
% 31.55/4.49  ------ Abstraction refinement Options
% 31.55/4.49  
% 31.55/4.49  --abstr_ref                             []
% 31.55/4.49  --abstr_ref_prep                        false
% 31.55/4.49  --abstr_ref_until_sat                   false
% 31.55/4.49  --abstr_ref_sig_restrict                funpre
% 31.55/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.55/4.49  --abstr_ref_under                       []
% 31.55/4.49  
% 31.55/4.49  ------ SAT Options
% 31.55/4.49  
% 31.55/4.49  --sat_mode                              false
% 31.55/4.49  --sat_fm_restart_options                ""
% 31.55/4.49  --sat_gr_def                            false
% 31.55/4.49  --sat_epr_types                         true
% 31.55/4.49  --sat_non_cyclic_types                  false
% 31.55/4.49  --sat_finite_models                     false
% 31.55/4.49  --sat_fm_lemmas                         false
% 31.55/4.49  --sat_fm_prep                           false
% 31.55/4.49  --sat_fm_uc_incr                        true
% 31.55/4.49  --sat_out_model                         small
% 31.55/4.49  --sat_out_clauses                       false
% 31.55/4.49  
% 31.55/4.49  ------ QBF Options
% 31.55/4.49  
% 31.55/4.49  --qbf_mode                              false
% 31.55/4.49  --qbf_elim_univ                         false
% 31.55/4.49  --qbf_dom_inst                          none
% 31.55/4.49  --qbf_dom_pre_inst                      false
% 31.55/4.49  --qbf_sk_in                             false
% 31.55/4.49  --qbf_pred_elim                         true
% 31.55/4.49  --qbf_split                             512
% 31.55/4.49  
% 31.55/4.49  ------ BMC1 Options
% 31.55/4.49  
% 31.55/4.49  --bmc1_incremental                      false
% 31.55/4.49  --bmc1_axioms                           reachable_all
% 31.55/4.49  --bmc1_min_bound                        0
% 31.55/4.49  --bmc1_max_bound                        -1
% 31.55/4.49  --bmc1_max_bound_default                -1
% 31.55/4.49  --bmc1_symbol_reachability              true
% 31.55/4.49  --bmc1_property_lemmas                  false
% 31.55/4.49  --bmc1_k_induction                      false
% 31.55/4.49  --bmc1_non_equiv_states                 false
% 31.55/4.49  --bmc1_deadlock                         false
% 31.55/4.49  --bmc1_ucm                              false
% 31.55/4.49  --bmc1_add_unsat_core                   none
% 31.55/4.49  --bmc1_unsat_core_children              false
% 31.55/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.55/4.49  --bmc1_out_stat                         full
% 31.55/4.49  --bmc1_ground_init                      false
% 31.55/4.49  --bmc1_pre_inst_next_state              false
% 31.55/4.49  --bmc1_pre_inst_state                   false
% 31.55/4.49  --bmc1_pre_inst_reach_state             false
% 31.55/4.49  --bmc1_out_unsat_core                   false
% 31.55/4.49  --bmc1_aig_witness_out                  false
% 31.55/4.49  --bmc1_verbose                          false
% 31.55/4.49  --bmc1_dump_clauses_tptp                false
% 31.55/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.55/4.49  --bmc1_dump_file                        -
% 31.55/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.55/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.55/4.49  --bmc1_ucm_extend_mode                  1
% 31.55/4.49  --bmc1_ucm_init_mode                    2
% 31.55/4.49  --bmc1_ucm_cone_mode                    none
% 31.55/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.55/4.49  --bmc1_ucm_relax_model                  4
% 31.55/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.55/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.55/4.49  --bmc1_ucm_layered_model                none
% 31.55/4.49  --bmc1_ucm_max_lemma_size               10
% 31.55/4.49  
% 31.55/4.49  ------ AIG Options
% 31.55/4.49  
% 31.55/4.49  --aig_mode                              false
% 31.55/4.49  
% 31.55/4.49  ------ Instantiation Options
% 31.55/4.49  
% 31.55/4.49  --instantiation_flag                    true
% 31.55/4.49  --inst_sos_flag                         true
% 31.55/4.49  --inst_sos_phase                        true
% 31.55/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.55/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.55/4.49  --inst_lit_sel_side                     none
% 31.55/4.49  --inst_solver_per_active                1400
% 31.55/4.49  --inst_solver_calls_frac                1.
% 31.55/4.49  --inst_passive_queue_type               priority_queues
% 31.55/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.55/4.49  --inst_passive_queues_freq              [25;2]
% 31.55/4.49  --inst_dismatching                      true
% 31.55/4.49  --inst_eager_unprocessed_to_passive     true
% 31.55/4.49  --inst_prop_sim_given                   true
% 31.55/4.49  --inst_prop_sim_new                     false
% 31.55/4.49  --inst_subs_new                         false
% 31.55/4.49  --inst_eq_res_simp                      false
% 31.55/4.49  --inst_subs_given                       false
% 31.55/4.49  --inst_orphan_elimination               true
% 31.55/4.49  --inst_learning_loop_flag               true
% 31.55/4.49  --inst_learning_start                   3000
% 31.55/4.49  --inst_learning_factor                  2
% 31.55/4.49  --inst_start_prop_sim_after_learn       3
% 31.55/4.49  --inst_sel_renew                        solver
% 31.55/4.49  --inst_lit_activity_flag                true
% 31.55/4.49  --inst_restr_to_given                   false
% 31.55/4.49  --inst_activity_threshold               500
% 31.55/4.49  --inst_out_proof                        true
% 31.55/4.49  
% 31.55/4.49  ------ Resolution Options
% 31.55/4.49  
% 31.55/4.49  --resolution_flag                       false
% 31.55/4.49  --res_lit_sel                           adaptive
% 31.55/4.49  --res_lit_sel_side                      none
% 31.55/4.49  --res_ordering                          kbo
% 31.55/4.49  --res_to_prop_solver                    active
% 31.55/4.49  --res_prop_simpl_new                    false
% 31.55/4.49  --res_prop_simpl_given                  true
% 31.55/4.49  --res_passive_queue_type                priority_queues
% 31.55/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.55/4.49  --res_passive_queues_freq               [15;5]
% 31.55/4.49  --res_forward_subs                      full
% 31.55/4.49  --res_backward_subs                     full
% 31.55/4.49  --res_forward_subs_resolution           true
% 31.55/4.49  --res_backward_subs_resolution          true
% 31.55/4.49  --res_orphan_elimination                true
% 31.55/4.49  --res_time_limit                        2.
% 31.55/4.49  --res_out_proof                         true
% 31.55/4.49  
% 31.55/4.49  ------ Superposition Options
% 31.55/4.49  
% 31.55/4.49  --superposition_flag                    true
% 31.55/4.49  --sup_passive_queue_type                priority_queues
% 31.55/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.55/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.55/4.49  --demod_completeness_check              fast
% 31.55/4.49  --demod_use_ground                      true
% 31.55/4.49  --sup_to_prop_solver                    passive
% 31.55/4.49  --sup_prop_simpl_new                    true
% 31.55/4.49  --sup_prop_simpl_given                  true
% 31.55/4.49  --sup_fun_splitting                     true
% 31.55/4.49  --sup_smt_interval                      50000
% 31.55/4.49  
% 31.55/4.49  ------ Superposition Simplification Setup
% 31.55/4.49  
% 31.55/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.55/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.55/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.55/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.55/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.55/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.55/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.55/4.49  --sup_immed_triv                        [TrivRules]
% 31.55/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.55/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.55/4.49  --sup_immed_bw_main                     []
% 31.55/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.55/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.55/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.55/4.49  --sup_input_bw                          []
% 31.55/4.49  
% 31.55/4.49  ------ Combination Options
% 31.55/4.49  
% 31.55/4.49  --comb_res_mult                         3
% 31.55/4.49  --comb_sup_mult                         2
% 31.55/4.49  --comb_inst_mult                        10
% 31.55/4.49  
% 31.55/4.49  ------ Debug Options
% 31.55/4.49  
% 31.55/4.49  --dbg_backtrace                         false
% 31.55/4.49  --dbg_dump_prop_clauses                 false
% 31.55/4.49  --dbg_dump_prop_clauses_file            -
% 31.55/4.49  --dbg_out_stat                          false
% 31.55/4.49  
% 31.55/4.49  
% 31.55/4.49  
% 31.55/4.49  
% 31.55/4.49  ------ Proving...
% 31.55/4.49  
% 31.55/4.49  
% 31.55/4.49  % SZS status Theorem for theBenchmark.p
% 31.55/4.49  
% 31.55/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.55/4.49  
% 31.55/4.49  fof(f4,axiom,(
% 31.55/4.49    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X1) => k1_funct_1(X2,X3) = o_1_0_funct_1(X0)) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2))),
% 31.55/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.55/4.49  
% 31.55/4.49  fof(f14,plain,(
% 31.55/4.49    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = o_1_0_funct_1(X0) | ~r2_hidden(X3,X1)) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2))),
% 31.55/4.49    inference(ennf_transformation,[],[f4])).
% 31.55/4.49  
% 31.55/4.49  fof(f26,plain,(
% 31.55/4.49    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = o_1_0_funct_1(X0) | ~r2_hidden(X3,X1)) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = o_1_0_funct_1(X0) | ~r2_hidden(X3,X1)) & k1_relat_1(sK4(X0,X1)) = X1 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))))),
% 31.55/4.49    introduced(choice_axiom,[])).
% 31.55/4.49  
% 31.55/4.49  fof(f27,plain,(
% 31.55/4.49    ! [X0,X1] : (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = o_1_0_funct_1(X0) | ~r2_hidden(X3,X1)) & k1_relat_1(sK4(X0,X1)) = X1 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1)))),
% 31.55/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f26])).
% 31.55/4.49  
% 31.55/4.49  fof(f44,plain,(
% 31.55/4.49    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X1) )),
% 31.55/4.49    inference(cnf_transformation,[],[f27])).
% 31.55/4.49  
% 31.55/4.49  fof(f2,axiom,(
% 31.55/4.49    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 31.55/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.55/4.49  
% 31.55/4.49  fof(f10,plain,(
% 31.55/4.49    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 31.55/4.49    inference(ennf_transformation,[],[f2])).
% 31.55/4.49  
% 31.55/4.49  fof(f11,plain,(
% 31.55/4.49    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 31.55/4.49    inference(flattening,[],[f10])).
% 31.55/4.49  
% 31.55/4.49  fof(f34,plain,(
% 31.55/4.49    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 31.55/4.49    inference(cnf_transformation,[],[f11])).
% 31.55/4.49  
% 31.55/4.49  fof(f42,plain,(
% 31.55/4.49    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1))) )),
% 31.55/4.49    inference(cnf_transformation,[],[f27])).
% 31.55/4.49  
% 31.55/4.49  fof(f3,axiom,(
% 31.55/4.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 31.55/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.55/4.49  
% 31.55/4.49  fof(f12,plain,(
% 31.55/4.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.55/4.49    inference(ennf_transformation,[],[f3])).
% 31.55/4.49  
% 31.55/4.49  fof(f13,plain,(
% 31.55/4.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.55/4.49    inference(flattening,[],[f12])).
% 31.55/4.49  
% 31.55/4.49  fof(f20,plain,(
% 31.55/4.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.55/4.49    inference(nnf_transformation,[],[f13])).
% 31.55/4.49  
% 31.55/4.49  fof(f21,plain,(
% 31.55/4.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.55/4.49    inference(rectify,[],[f20])).
% 31.55/4.49  
% 31.55/4.49  fof(f24,plain,(
% 31.55/4.49    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 31.55/4.49    introduced(choice_axiom,[])).
% 31.55/4.49  
% 31.55/4.49  fof(f23,plain,(
% 31.55/4.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 31.55/4.49    introduced(choice_axiom,[])).
% 31.55/4.49  
% 31.55/4.49  fof(f22,plain,(
% 31.55/4.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 31.55/4.49    introduced(choice_axiom,[])).
% 31.55/4.49  
% 31.55/4.49  fof(f25,plain,(
% 31.55/4.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.55/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f24,f23,f22])).
% 31.55/4.49  
% 31.55/4.49  fof(f36,plain,(
% 31.55/4.49    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.55/4.49    inference(cnf_transformation,[],[f25])).
% 31.55/4.49  
% 31.55/4.49  fof(f55,plain,(
% 31.55/4.49    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.55/4.49    inference(equality_resolution,[],[f36])).
% 31.55/4.49  
% 31.55/4.49  fof(f43,plain,(
% 31.55/4.49    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1))) )),
% 31.55/4.49    inference(cnf_transformation,[],[f27])).
% 31.55/4.49  
% 31.55/4.49  fof(f5,axiom,(
% 31.55/4.49    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 31.55/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.55/4.49  
% 31.55/4.49  fof(f15,plain,(
% 31.55/4.49    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 31.55/4.49    inference(ennf_transformation,[],[f5])).
% 31.55/4.49  
% 31.55/4.49  fof(f28,plain,(
% 31.55/4.49    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK5(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1))))),
% 31.55/4.49    introduced(choice_axiom,[])).
% 31.55/4.49  
% 31.55/4.49  fof(f29,plain,(
% 31.55/4.49    ! [X0,X1] : (! [X3] : (k1_funct_1(sK5(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1)))),
% 31.55/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f28])).
% 31.55/4.49  
% 31.55/4.49  fof(f49,plain,(
% 31.55/4.49    ( ! [X0,X3,X1] : (k1_funct_1(sK5(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 31.55/4.49    inference(cnf_transformation,[],[f29])).
% 31.55/4.49  
% 31.55/4.49  fof(f48,plain,(
% 31.55/4.49    ( ! [X0,X1] : (k1_relat_1(sK5(X0,X1)) = X0) )),
% 31.55/4.49    inference(cnf_transformation,[],[f29])).
% 31.55/4.49  
% 31.55/4.49  fof(f46,plain,(
% 31.55/4.49    ( ! [X0,X1] : (v1_relat_1(sK5(X0,X1))) )),
% 31.55/4.49    inference(cnf_transformation,[],[f29])).
% 31.55/4.49  
% 31.55/4.49  fof(f6,conjecture,(
% 31.55/4.49    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 31.55/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.55/4.49  
% 31.55/4.49  fof(f7,negated_conjecture,(
% 31.55/4.49    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 31.55/4.49    inference(negated_conjecture,[],[f6])).
% 31.55/4.49  
% 31.55/4.49  fof(f16,plain,(
% 31.55/4.49    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 31.55/4.49    inference(ennf_transformation,[],[f7])).
% 31.55/4.49  
% 31.55/4.49  fof(f17,plain,(
% 31.55/4.49    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 31.55/4.49    inference(flattening,[],[f16])).
% 31.55/4.49  
% 31.55/4.49  fof(f30,plain,(
% 31.55/4.49    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK6) | k1_relat_1(X2) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK7 | k1_xboole_0 != sK6))),
% 31.55/4.49    introduced(choice_axiom,[])).
% 31.55/4.49  
% 31.55/4.49  fof(f31,plain,(
% 31.55/4.49    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK6) | k1_relat_1(X2) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK7 | k1_xboole_0 != sK6)),
% 31.55/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f17,f30])).
% 31.55/4.49  
% 31.55/4.49  fof(f50,plain,(
% 31.55/4.49    k1_xboole_0 = sK7 | k1_xboole_0 != sK6),
% 31.55/4.49    inference(cnf_transformation,[],[f31])).
% 31.55/4.49  
% 31.55/4.49  fof(f1,axiom,(
% 31.55/4.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 31.55/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.55/4.49  
% 31.55/4.49  fof(f8,plain,(
% 31.55/4.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 31.55/4.49    inference(unused_predicate_definition_removal,[],[f1])).
% 31.55/4.49  
% 31.55/4.49  fof(f9,plain,(
% 31.55/4.49    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 31.55/4.49    inference(ennf_transformation,[],[f8])).
% 31.55/4.49  
% 31.55/4.49  fof(f18,plain,(
% 31.55/4.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 31.55/4.49    introduced(choice_axiom,[])).
% 31.55/4.49  
% 31.55/4.49  fof(f19,plain,(
% 31.55/4.49    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 31.55/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f18])).
% 31.55/4.49  
% 31.55/4.49  fof(f32,plain,(
% 31.55/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 31.55/4.49    inference(cnf_transformation,[],[f19])).
% 31.55/4.49  
% 31.55/4.49  fof(f51,plain,(
% 31.55/4.49    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK6) | k1_relat_1(X2) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 31.55/4.49    inference(cnf_transformation,[],[f31])).
% 31.55/4.49  
% 31.55/4.49  fof(f33,plain,(
% 31.55/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 31.55/4.49    inference(cnf_transformation,[],[f19])).
% 31.55/4.49  
% 31.55/4.49  fof(f39,plain,(
% 31.55/4.49    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.55/4.49    inference(cnf_transformation,[],[f25])).
% 31.55/4.49  
% 31.55/4.49  fof(f47,plain,(
% 31.55/4.49    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1))) )),
% 31.55/4.49    inference(cnf_transformation,[],[f29])).
% 31.55/4.49  
% 31.55/4.49  fof(f37,plain,(
% 31.55/4.49    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.55/4.49    inference(cnf_transformation,[],[f25])).
% 31.55/4.49  
% 31.55/4.49  fof(f54,plain,(
% 31.55/4.49    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.55/4.49    inference(equality_resolution,[],[f37])).
% 31.55/4.49  
% 31.55/4.49  fof(f38,plain,(
% 31.55/4.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.55/4.49    inference(cnf_transformation,[],[f25])).
% 31.55/4.49  
% 31.55/4.49  fof(f52,plain,(
% 31.55/4.49    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.55/4.49    inference(equality_resolution,[],[f38])).
% 31.55/4.49  
% 31.55/4.49  fof(f53,plain,(
% 31.55/4.49    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.55/4.49    inference(equality_resolution,[],[f52])).
% 31.55/4.49  
% 31.55/4.49  fof(f45,plain,(
% 31.55/4.49    ( ! [X0,X3,X1] : (k1_funct_1(sK4(X0,X1),X3) = o_1_0_funct_1(X0) | ~r2_hidden(X3,X1)) )),
% 31.55/4.49    inference(cnf_transformation,[],[f27])).
% 31.55/4.49  
% 31.55/4.49  cnf(c_11,plain,
% 31.55/4.49      ( k1_relat_1(sK4(X0,X1)) = X1 ),
% 31.55/4.49      inference(cnf_transformation,[],[f44]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_3,plain,
% 31.55/4.49      ( ~ v1_relat_1(X0)
% 31.55/4.49      | k1_relat_1(X0) != k1_xboole_0
% 31.55/4.49      | k1_xboole_0 = X0 ),
% 31.55/4.49      inference(cnf_transformation,[],[f34]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1931,plain,
% 31.55/4.49      ( k1_relat_1(X0) != k1_xboole_0
% 31.55/4.49      | k1_xboole_0 = X0
% 31.55/4.49      | v1_relat_1(X0) != iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2787,plain,
% 31.55/4.49      ( sK4(X0,X1) = k1_xboole_0
% 31.55/4.49      | k1_xboole_0 != X1
% 31.55/4.49      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_11,c_1931]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_13,plain,
% 31.55/4.49      ( v1_relat_1(sK4(X0,X1)) ),
% 31.55/4.49      inference(cnf_transformation,[],[f42]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_33,plain,
% 31.55/4.49      ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2877,plain,
% 31.55/4.49      ( k1_xboole_0 != X1 | sK4(X0,X1) = k1_xboole_0 ),
% 31.55/4.49      inference(global_propositional_subsumption,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_2787,c_33]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2878,plain,
% 31.55/4.49      ( sK4(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1 ),
% 31.55/4.49      inference(renaming,[status(thm)],[c_2877]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2880,plain,
% 31.55/4.49      ( sK4(X0,k1_xboole_0) = k1_xboole_0 ),
% 31.55/4.49      inference(equality_resolution,[status(thm)],[c_2878]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_3023,plain,
% 31.55/4.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_2880,c_11]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_9,plain,
% 31.55/4.49      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 31.55/4.49      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 31.55/4.49      | ~ v1_funct_1(X1)
% 31.55/4.49      | ~ v1_relat_1(X1) ),
% 31.55/4.49      inference(cnf_transformation,[],[f55]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1925,plain,
% 31.55/4.49      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 31.55/4.49      | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
% 31.55/4.49      | v1_funct_1(X1) != iProver_top
% 31.55/4.49      | v1_relat_1(X1) != iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_3061,plain,
% 31.55/4.49      ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top
% 31.55/4.49      | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 31.55/4.49      | v1_funct_1(k1_xboole_0) != iProver_top
% 31.55/4.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_3023,c_1925]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_35,plain,
% 31.55/4.49      ( v1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_33]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_12,plain,
% 31.55/4.49      ( v1_funct_1(sK4(X0,X1)) ),
% 31.55/4.49      inference(cnf_transformation,[],[f43]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_36,plain,
% 31.55/4.49      ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_38,plain,
% 31.55/4.49      ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_36]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_39,plain,
% 31.55/4.49      ( k1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_11]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_657,plain,
% 31.55/4.49      ( sK4(X0,X1) != X2
% 31.55/4.49      | k1_relat_1(X2) != k1_xboole_0
% 31.55/4.49      | k1_xboole_0 = X2 ),
% 31.55/4.49      inference(resolution_lifted,[status(thm)],[c_3,c_13]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_658,plain,
% 31.55/4.49      ( k1_relat_1(sK4(X0,X1)) != k1_xboole_0
% 31.55/4.49      | k1_xboole_0 = sK4(X0,X1) ),
% 31.55/4.49      inference(unflattening,[status(thm)],[c_657]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_659,plain,
% 31.55/4.49      ( k1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
% 31.55/4.49      | k1_xboole_0 = sK4(k1_xboole_0,k1_xboole_0) ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_658]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1658,plain,
% 31.55/4.49      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 31.55/4.49      theory(equality) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2000,plain,
% 31.55/4.49      ( v1_funct_1(X0) | ~ v1_funct_1(sK4(X1,X2)) | X0 != sK4(X1,X2) ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_1658]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2001,plain,
% 31.55/4.49      ( X0 != sK4(X1,X2)
% 31.55/4.49      | v1_funct_1(X0) = iProver_top
% 31.55/4.49      | v1_funct_1(sK4(X1,X2)) != iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_2000]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2003,plain,
% 31.55/4.49      ( k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0)
% 31.55/4.49      | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) != iProver_top
% 31.55/4.49      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_2001]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1655,plain,
% 31.55/4.49      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 31.55/4.49      theory(equality) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2066,plain,
% 31.55/4.49      ( v1_relat_1(X0) | ~ v1_relat_1(sK4(X1,X2)) | X0 != sK4(X1,X2) ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_1655]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2067,plain,
% 31.55/4.49      ( X0 != sK4(X1,X2)
% 31.55/4.49      | v1_relat_1(X0) = iProver_top
% 31.55/4.49      | v1_relat_1(sK4(X1,X2)) != iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_2066]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2069,plain,
% 31.55/4.49      ( k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0)
% 31.55/4.49      | v1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) != iProver_top
% 31.55/4.49      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_2067]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_7814,plain,
% 31.55/4.49      ( r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top
% 31.55/4.49      | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 31.55/4.49      inference(global_propositional_subsumption,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_3061,c_35,c_38,c_39,c_659,c_2003,c_2069]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_14,plain,
% 31.55/4.49      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK5(X1,X2),X0) = X2 ),
% 31.55/4.49      inference(cnf_transformation,[],[f49]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1921,plain,
% 31.55/4.49      ( k1_funct_1(sK5(X0,X1),X2) = X1
% 31.55/4.49      | r2_hidden(X2,X0) != iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_7821,plain,
% 31.55/4.49      ( k1_funct_1(sK5(k1_xboole_0,X0),sK3(k1_xboole_0,X1)) = X0
% 31.55/4.49      | r2_hidden(X1,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_7814,c_1921]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_15,plain,
% 31.55/4.49      ( k1_relat_1(sK5(X0,X1)) = X0 ),
% 31.55/4.49      inference(cnf_transformation,[],[f48]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2788,plain,
% 31.55/4.49      ( sK5(X0,X1) = k1_xboole_0
% 31.55/4.49      | k1_xboole_0 != X0
% 31.55/4.49      | v1_relat_1(sK5(X0,X1)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_15,c_1931]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_17,plain,
% 31.55/4.49      ( v1_relat_1(sK5(X0,X1)) ),
% 31.55/4.49      inference(cnf_transformation,[],[f46]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_23,plain,
% 31.55/4.49      ( v1_relat_1(sK5(X0,X1)) = iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2883,plain,
% 31.55/4.49      ( k1_xboole_0 != X0 | sK5(X0,X1) = k1_xboole_0 ),
% 31.55/4.49      inference(global_propositional_subsumption,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_2788,c_23]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2884,plain,
% 31.55/4.49      ( sK5(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 31.55/4.49      inference(renaming,[status(thm)],[c_2883]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2886,plain,
% 31.55/4.49      ( sK5(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.55/4.49      inference(equality_resolution,[status(thm)],[c_2884]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_7822,plain,
% 31.55/4.49      ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1
% 31.55/4.49      | r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 31.55/4.49      inference(light_normalisation,[status(thm)],[c_7821,c_2886]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_19,negated_conjecture,
% 31.55/4.49      ( k1_xboole_0 = sK7 | k1_xboole_0 != sK6 ),
% 31.55/4.49      inference(cnf_transformation,[],[f50]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_34,plain,
% 31.55/4.49      ( v1_relat_1(sK4(k1_xboole_0,k1_xboole_0)) ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_13]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_37,plain,
% 31.55/4.49      ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_12]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1651,plain,( X0 = X0 ),theory(equality) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1666,plain,
% 31.55/4.49      ( k1_xboole_0 = k1_xboole_0 ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_1651]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1652,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1957,plain,
% 31.55/4.49      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_1652]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1958,plain,
% 31.55/4.49      ( sK6 != k1_xboole_0
% 31.55/4.49      | k1_xboole_0 = sK6
% 31.55/4.49      | k1_xboole_0 != k1_xboole_0 ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_1957]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2002,plain,
% 31.55/4.49      ( ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0))
% 31.55/4.49      | v1_funct_1(k1_xboole_0)
% 31.55/4.49      | k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0) ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_2000]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2068,plain,
% 31.55/4.49      ( ~ v1_relat_1(sK4(k1_xboole_0,k1_xboole_0))
% 31.55/4.49      | v1_relat_1(k1_xboole_0)
% 31.55/4.49      | k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0) ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_2066]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1979,plain,
% 31.55/4.49      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_1652]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2026,plain,
% 31.55/4.49      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_1979]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2097,plain,
% 31.55/4.49      ( k2_relat_1(X0) != sK6 | sK6 = k2_relat_1(X0) | sK6 != sK6 ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_2026]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2098,plain,
% 31.55/4.49      ( k2_relat_1(k1_xboole_0) != sK6
% 31.55/4.49      | sK6 = k2_relat_1(k1_xboole_0)
% 31.55/4.49      | sK6 != sK6 ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_2097]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2156,plain,
% 31.55/4.49      ( sK6 = sK6 ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_1651]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2054,plain,
% 31.55/4.49      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_1652]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2186,plain,
% 31.55/4.49      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_2054]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2187,plain,
% 31.55/4.49      ( sK7 != sK7 | sK7 = k1_xboole_0 | k1_xboole_0 != sK7 ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_2186]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2278,plain,
% 31.55/4.49      ( sK7 = sK7 ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_1651]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1,plain,
% 31.55/4.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 31.55/4.49      inference(cnf_transformation,[],[f32]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_18,negated_conjecture,
% 31.55/4.49      ( ~ r1_tarski(k2_relat_1(X0),sK6)
% 31.55/4.49      | ~ v1_funct_1(X0)
% 31.55/4.49      | ~ v1_relat_1(X0)
% 31.55/4.49      | k1_relat_1(X0) != sK7 ),
% 31.55/4.49      inference(cnf_transformation,[],[f51]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_205,plain,
% 31.55/4.49      ( r2_hidden(sK0(X0,X1),X0)
% 31.55/4.49      | ~ v1_funct_1(X2)
% 31.55/4.49      | ~ v1_relat_1(X2)
% 31.55/4.49      | k1_relat_1(X2) != sK7
% 31.55/4.49      | k2_relat_1(X2) != X0
% 31.55/4.49      | sK6 != X1 ),
% 31.55/4.49      inference(resolution_lifted,[status(thm)],[c_1,c_18]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_206,plain,
% 31.55/4.49      ( r2_hidden(sK0(k2_relat_1(X0),sK6),k2_relat_1(X0))
% 31.55/4.49      | ~ v1_funct_1(X0)
% 31.55/4.49      | ~ v1_relat_1(X0)
% 31.55/4.49      | k1_relat_1(X0) != sK7 ),
% 31.55/4.49      inference(unflattening,[status(thm)],[c_205]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1918,plain,
% 31.55/4.49      ( k1_relat_1(X0) != sK7
% 31.55/4.49      | r2_hidden(sK0(k2_relat_1(X0),sK6),k2_relat_1(X0)) = iProver_top
% 31.55/4.49      | v1_funct_1(X0) != iProver_top
% 31.55/4.49      | v1_relat_1(X0) != iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_206]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_3059,plain,
% 31.55/4.49      ( sK7 != k1_xboole_0
% 31.55/4.49      | r2_hidden(sK0(k2_relat_1(k1_xboole_0),sK6),k2_relat_1(k1_xboole_0)) = iProver_top
% 31.55/4.49      | v1_funct_1(k1_xboole_0) != iProver_top
% 31.55/4.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_3023,c_1918]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_3161,plain,
% 31.55/4.49      ( sK7 != k1_xboole_0
% 31.55/4.49      | r2_hidden(sK0(k2_relat_1(k1_xboole_0),sK6),k2_relat_1(k1_xboole_0)) = iProver_top ),
% 31.55/4.49      inference(global_propositional_subsumption,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_3059,c_35,c_38,c_39,c_659,c_2003,c_2069]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_0,plain,
% 31.55/4.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 31.55/4.49      inference(cnf_transformation,[],[f33]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_223,plain,
% 31.55/4.49      ( ~ r2_hidden(sK0(X0,X1),X1)
% 31.55/4.49      | ~ v1_funct_1(X2)
% 31.55/4.49      | ~ v1_relat_1(X2)
% 31.55/4.49      | k1_relat_1(X2) != sK7
% 31.55/4.49      | k2_relat_1(X2) != X0
% 31.55/4.49      | sK6 != X1 ),
% 31.55/4.49      inference(resolution_lifted,[status(thm)],[c_0,c_18]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_224,plain,
% 31.55/4.49      ( ~ r2_hidden(sK0(k2_relat_1(X0),sK6),sK6)
% 31.55/4.49      | ~ v1_funct_1(X0)
% 31.55/4.49      | ~ v1_relat_1(X0)
% 31.55/4.49      | k1_relat_1(X0) != sK7 ),
% 31.55/4.49      inference(unflattening,[status(thm)],[c_223]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1917,plain,
% 31.55/4.49      ( k1_relat_1(X0) != sK7
% 31.55/4.49      | r2_hidden(sK0(k2_relat_1(X0),sK6),sK6) != iProver_top
% 31.55/4.49      | v1_funct_1(X0) != iProver_top
% 31.55/4.49      | v1_relat_1(X0) != iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_3060,plain,
% 31.55/4.49      ( sK7 != k1_xboole_0
% 31.55/4.49      | r2_hidden(sK0(k2_relat_1(k1_xboole_0),sK6),sK6) != iProver_top
% 31.55/4.49      | v1_funct_1(k1_xboole_0) != iProver_top
% 31.55/4.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_3023,c_1917]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_3166,plain,
% 31.55/4.49      ( sK7 != k1_xboole_0
% 31.55/4.49      | r2_hidden(sK0(k2_relat_1(k1_xboole_0),sK6),sK6) != iProver_top ),
% 31.55/4.49      inference(global_propositional_subsumption,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_3060,c_35,c_38,c_39,c_659,c_2003,c_2069]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_6,plain,
% 31.55/4.49      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 31.55/4.49      | r2_hidden(sK1(X0,X1),X1)
% 31.55/4.49      | ~ v1_funct_1(X0)
% 31.55/4.49      | ~ v1_relat_1(X0)
% 31.55/4.49      | k2_relat_1(X0) = X1 ),
% 31.55/4.49      inference(cnf_transformation,[],[f39]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1928,plain,
% 31.55/4.49      ( k2_relat_1(X0) = X1
% 31.55/4.49      | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) = iProver_top
% 31.55/4.49      | r2_hidden(sK1(X0,X1),X1) = iProver_top
% 31.55/4.49      | v1_funct_1(X0) != iProver_top
% 31.55/4.49      | v1_relat_1(X0) != iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_3442,plain,
% 31.55/4.49      ( k2_relat_1(sK4(X0,X1)) = X2
% 31.55/4.49      | r2_hidden(sK2(sK4(X0,X1),X2),X1) = iProver_top
% 31.55/4.49      | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top
% 31.55/4.49      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_11,c_1928]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_4190,plain,
% 31.55/4.49      ( k2_relat_1(sK4(X0,X1)) = X2
% 31.55/4.49      | r2_hidden(sK2(sK4(X0,X1),X2),X1) = iProver_top
% 31.55/4.49      | r2_hidden(sK1(sK4(X0,X1),X2),X2) = iProver_top ),
% 31.55/4.49      inference(global_propositional_subsumption,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_3442,c_33,c_36]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1919,plain,
% 31.55/4.49      ( v1_relat_1(sK5(X0,X1)) = iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_16,plain,
% 31.55/4.49      ( v1_funct_1(sK5(X0,X1)) ),
% 31.55/4.49      inference(cnf_transformation,[],[f47]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1920,plain,
% 31.55/4.49      ( v1_funct_1(sK5(X0,X1)) = iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2190,plain,
% 31.55/4.49      ( sK7 != X0
% 31.55/4.49      | r2_hidden(sK0(k2_relat_1(sK5(X0,X1)),sK6),k2_relat_1(sK5(X0,X1))) = iProver_top
% 31.55/4.49      | v1_funct_1(sK5(X0,X1)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(X0,X1)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_15,c_1918]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_26,plain,
% 31.55/4.49      ( v1_funct_1(sK5(X0,X1)) = iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2337,plain,
% 31.55/4.49      ( sK7 != X0
% 31.55/4.49      | r2_hidden(sK0(k2_relat_1(sK5(X0,X1)),sK6),k2_relat_1(sK5(X0,X1))) = iProver_top ),
% 31.55/4.49      inference(global_propositional_subsumption,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_2190,c_23,c_26]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2343,plain,
% 31.55/4.49      ( r2_hidden(sK0(k2_relat_1(sK5(sK7,X0)),sK6),k2_relat_1(sK5(sK7,X0))) = iProver_top ),
% 31.55/4.49      inference(equality_resolution,[status(thm)],[c_2337]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2652,plain,
% 31.55/4.49      ( k1_funct_1(sK5(k1_relat_1(X0),X1),sK3(X0,X2)) = X1
% 31.55/4.49      | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
% 31.55/4.49      | v1_funct_1(X0) != iProver_top
% 31.55/4.49      | v1_relat_1(X0) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_1925,c_1921]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_5544,plain,
% 31.55/4.49      ( k1_funct_1(sK5(k1_relat_1(sK5(sK7,X0)),X1),sK3(sK5(sK7,X0),sK0(k2_relat_1(sK5(sK7,X0)),sK6))) = X1
% 31.55/4.49      | v1_funct_1(sK5(sK7,X0)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(sK7,X0)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_2343,c_2652]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_5557,plain,
% 31.55/4.49      ( k1_funct_1(sK5(sK7,X0),sK3(sK5(sK7,X1),sK0(k2_relat_1(sK5(sK7,X1)),sK6))) = X0
% 31.55/4.49      | v1_funct_1(sK5(sK7,X1)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(sK7,X1)) != iProver_top ),
% 31.55/4.49      inference(demodulation,[status(thm)],[c_5544,c_15]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_5759,plain,
% 31.55/4.49      ( k1_funct_1(sK5(sK7,X0),sK3(sK5(sK7,X1),sK0(k2_relat_1(sK5(sK7,X1)),sK6))) = X0
% 31.55/4.49      | v1_relat_1(sK5(sK7,X1)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_1920,c_5557]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_6382,plain,
% 31.55/4.49      ( k1_funct_1(sK5(sK7,X0),sK3(sK5(sK7,X1),sK0(k2_relat_1(sK5(sK7,X1)),sK6))) = X0 ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_1919,c_5759]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_8,plain,
% 31.55/4.49      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 31.55/4.49      | ~ v1_funct_1(X1)
% 31.55/4.49      | ~ v1_relat_1(X1)
% 31.55/4.49      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 31.55/4.49      inference(cnf_transformation,[],[f54]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1926,plain,
% 31.55/4.49      ( k1_funct_1(X0,sK3(X0,X1)) = X1
% 31.55/4.49      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 31.55/4.49      | v1_funct_1(X0) != iProver_top
% 31.55/4.49      | v1_relat_1(X0) != iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_3245,plain,
% 31.55/4.49      ( k1_funct_1(sK5(sK7,X0),sK3(sK5(sK7,X0),sK0(k2_relat_1(sK5(sK7,X0)),sK6))) = sK0(k2_relat_1(sK5(sK7,X0)),sK6)
% 31.55/4.49      | v1_funct_1(sK5(sK7,X0)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(sK7,X0)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_2343,c_1926]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2046,plain,
% 31.55/4.49      ( v1_funct_1(sK5(sK7,X0)) ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_16]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2047,plain,
% 31.55/4.49      ( v1_funct_1(sK5(sK7,X0)) = iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_2046]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2145,plain,
% 31.55/4.49      ( v1_relat_1(sK5(sK7,X0)) ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_17]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2146,plain,
% 31.55/4.49      ( v1_relat_1(sK5(sK7,X0)) = iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_2145]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_3653,plain,
% 31.55/4.49      ( k1_funct_1(sK5(sK7,X0),sK3(sK5(sK7,X0),sK0(k2_relat_1(sK5(sK7,X0)),sK6))) = sK0(k2_relat_1(sK5(sK7,X0)),sK6) ),
% 31.55/4.49      inference(global_propositional_subsumption,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_3245,c_2047,c_2146]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_7358,plain,
% 31.55/4.49      ( sK0(k2_relat_1(sK5(sK7,X0)),sK6) = X0 ),
% 31.55/4.49      inference(demodulation,[status(thm)],[c_6382,c_3653]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2191,plain,
% 31.55/4.49      ( sK7 != X0
% 31.55/4.49      | r2_hidden(sK0(k2_relat_1(sK5(X0,X1)),sK6),sK6) != iProver_top
% 31.55/4.49      | v1_funct_1(sK5(X0,X1)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(X0,X1)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_15,c_1917]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2253,plain,
% 31.55/4.49      ( sK7 != X0
% 31.55/4.49      | r2_hidden(sK0(k2_relat_1(sK5(X0,X1)),sK6),sK6) != iProver_top ),
% 31.55/4.49      inference(global_propositional_subsumption,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_2191,c_23,c_26]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2259,plain,
% 31.55/4.49      ( r2_hidden(sK0(k2_relat_1(sK5(sK7,X0)),sK6),sK6) != iProver_top ),
% 31.55/4.49      inference(equality_resolution,[status(thm)],[c_2253]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_7373,plain,
% 31.55/4.49      ( r2_hidden(X0,sK6) != iProver_top ),
% 31.55/4.49      inference(demodulation,[status(thm)],[c_7358,c_2259]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_7459,plain,
% 31.55/4.49      ( k2_relat_1(sK4(X0,X1)) = sK6
% 31.55/4.49      | r2_hidden(sK2(sK4(X0,X1),sK6),X1) = iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_4190,c_7373]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_8208,plain,
% 31.55/4.49      ( k1_funct_1(sK5(X0,X1),sK2(sK4(X2,X0),sK6)) = X1
% 31.55/4.49      | k2_relat_1(sK4(X2,X0)) = sK6 ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_7459,c_1921]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_7,plain,
% 31.55/4.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 31.55/4.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 31.55/4.49      | ~ v1_funct_1(X1)
% 31.55/4.49      | ~ v1_relat_1(X1) ),
% 31.55/4.49      inference(cnf_transformation,[],[f53]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1927,plain,
% 31.55/4.49      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 31.55/4.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 31.55/4.49      | v1_funct_1(X1) != iProver_top
% 31.55/4.49      | v1_relat_1(X1) != iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_16231,plain,
% 31.55/4.49      ( k2_relat_1(sK4(X0,X1)) = sK6
% 31.55/4.49      | r2_hidden(X2,k2_relat_1(sK5(X1,X2))) = iProver_top
% 31.55/4.49      | r2_hidden(sK2(sK4(X0,X1),sK6),k1_relat_1(sK5(X1,X2))) != iProver_top
% 31.55/4.49      | v1_funct_1(sK5(X1,X2)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(X1,X2)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_8208,c_1927]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_16232,plain,
% 31.55/4.49      ( k2_relat_1(sK4(X0,X1)) = sK6
% 31.55/4.49      | r2_hidden(X2,k2_relat_1(sK5(X1,X2))) = iProver_top
% 31.55/4.49      | r2_hidden(sK2(sK4(X0,X1),sK6),X1) != iProver_top
% 31.55/4.49      | v1_funct_1(sK5(X1,X2)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(X1,X2)) != iProver_top ),
% 31.55/4.49      inference(demodulation,[status(thm)],[c_16231,c_15]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_16551,plain,
% 31.55/4.49      ( r2_hidden(X2,k2_relat_1(sK5(X1,X2))) = iProver_top
% 31.55/4.49      | k2_relat_1(sK4(X0,X1)) = sK6
% 31.55/4.49      | v1_funct_1(sK5(X1,X2)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(X1,X2)) != iProver_top ),
% 31.55/4.49      inference(global_propositional_subsumption,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_16232,c_7459]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_16552,plain,
% 31.55/4.49      ( k2_relat_1(sK4(X0,X1)) = sK6
% 31.55/4.49      | r2_hidden(X2,k2_relat_1(sK5(X1,X2))) = iProver_top
% 31.55/4.49      | v1_funct_1(sK5(X1,X2)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(X1,X2)) != iProver_top ),
% 31.55/4.49      inference(renaming,[status(thm)],[c_16551]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_16565,plain,
% 31.55/4.49      ( k1_funct_1(sK5(k1_relat_1(sK5(X0,X1)),X2),sK3(sK5(X0,X1),X1)) = X2
% 31.55/4.49      | k2_relat_1(sK4(X3,X0)) = sK6
% 31.55/4.49      | v1_funct_1(sK5(X0,X1)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(X0,X1)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_16552,c_2652]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_16572,plain,
% 31.55/4.49      ( k1_funct_1(sK5(X0,X1),sK3(sK5(X0,X2),X2)) = X1
% 31.55/4.49      | k2_relat_1(sK4(X3,X0)) = sK6
% 31.55/4.49      | v1_funct_1(sK5(X0,X2)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(X0,X2)) != iProver_top ),
% 31.55/4.49      inference(light_normalisation,[status(thm)],[c_16565,c_15]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_16605,plain,
% 31.55/4.49      ( k1_funct_1(sK5(k1_xboole_0,X0),sK3(sK5(k1_xboole_0,X1),X1)) = X0
% 31.55/4.49      | k2_relat_1(sK4(X2,k1_xboole_0)) = sK6
% 31.55/4.49      | v1_funct_1(k1_xboole_0) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(k1_xboole_0,X1)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_2886,c_16572]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_16666,plain,
% 31.55/4.49      ( k1_funct_1(k1_xboole_0,sK3(sK5(k1_xboole_0,X0),X0)) = X1
% 31.55/4.49      | k2_relat_1(sK4(X2,k1_xboole_0)) = sK6
% 31.55/4.49      | v1_funct_1(k1_xboole_0) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(k1_xboole_0,X0)) != iProver_top ),
% 31.55/4.49      inference(light_normalisation,[status(thm)],[c_16605,c_2886]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_16667,plain,
% 31.55/4.49      ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1
% 31.55/4.49      | k2_relat_1(k1_xboole_0) = sK6
% 31.55/4.49      | v1_funct_1(k1_xboole_0) != iProver_top
% 31.55/4.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 31.55/4.49      inference(demodulation,[status(thm)],[c_16666,c_2880,c_2886]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_16668,plain,
% 31.55/4.49      ( ~ v1_funct_1(k1_xboole_0)
% 31.55/4.49      | ~ v1_relat_1(k1_xboole_0)
% 31.55/4.49      | k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1
% 31.55/4.49      | k2_relat_1(k1_xboole_0) = sK6 ),
% 31.55/4.49      inference(predicate_to_equality_rev,[status(thm)],[c_16667]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1654,plain,
% 31.55/4.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.55/4.49      theory(equality) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_3912,plain,
% 31.55/4.49      ( r2_hidden(X0,X1)
% 31.55/4.49      | ~ r2_hidden(sK0(k2_relat_1(X2),sK6),k2_relat_1(X2))
% 31.55/4.49      | X0 != sK0(k2_relat_1(X2),sK6)
% 31.55/4.49      | X1 != k2_relat_1(X2) ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_1654]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_12186,plain,
% 31.55/4.49      ( r2_hidden(sK0(k2_relat_1(X0),sK6),X1)
% 31.55/4.49      | ~ r2_hidden(sK0(k2_relat_1(X0),sK6),k2_relat_1(X0))
% 31.55/4.49      | X1 != k2_relat_1(X0)
% 31.55/4.49      | sK0(k2_relat_1(X0),sK6) != sK0(k2_relat_1(X0),sK6) ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_3912]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_25066,plain,
% 31.55/4.49      ( ~ r2_hidden(sK0(k2_relat_1(X0),sK6),k2_relat_1(X0))
% 31.55/4.49      | r2_hidden(sK0(k2_relat_1(X0),sK6),sK6)
% 31.55/4.49      | sK0(k2_relat_1(X0),sK6) != sK0(k2_relat_1(X0),sK6)
% 31.55/4.49      | sK6 != k2_relat_1(X0) ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_12186]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_25067,plain,
% 31.55/4.49      ( sK0(k2_relat_1(X0),sK6) != sK0(k2_relat_1(X0),sK6)
% 31.55/4.49      | sK6 != k2_relat_1(X0)
% 31.55/4.49      | r2_hidden(sK0(k2_relat_1(X0),sK6),k2_relat_1(X0)) != iProver_top
% 31.55/4.49      | r2_hidden(sK0(k2_relat_1(X0),sK6),sK6) = iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_25066]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_25069,plain,
% 31.55/4.49      ( sK0(k2_relat_1(k1_xboole_0),sK6) != sK0(k2_relat_1(k1_xboole_0),sK6)
% 31.55/4.49      | sK6 != k2_relat_1(k1_xboole_0)
% 31.55/4.49      | r2_hidden(sK0(k2_relat_1(k1_xboole_0),sK6),k2_relat_1(k1_xboole_0)) != iProver_top
% 31.55/4.49      | r2_hidden(sK0(k2_relat_1(k1_xboole_0),sK6),sK6) = iProver_top ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_25067]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_7463,plain,
% 31.55/4.49      ( k2_relat_1(sK4(X0,sK6)) = X1
% 31.55/4.49      | r2_hidden(sK1(sK4(X0,sK6),X1),X1) = iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_4190,c_7373]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_8210,plain,
% 31.55/4.49      ( k2_relat_1(sK4(X0,sK6)) = sK6 ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_7459,c_7373]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_8547,plain,
% 31.55/4.49      ( sK6 = X0 | r2_hidden(sK1(sK4(X1,sK6),X0),X0) = iProver_top ),
% 31.55/4.49      inference(demodulation,[status(thm)],[c_7463,c_8210]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_8552,plain,
% 31.55/4.49      ( k1_funct_1(sK5(X0,X1),sK1(sK4(X2,sK6),X0)) = X1 | sK6 = X0 ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_8547,c_1921]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_35683,plain,
% 31.55/4.49      ( sK6 = X0
% 31.55/4.49      | r2_hidden(X1,k2_relat_1(sK5(X0,X1))) = iProver_top
% 31.55/4.49      | r2_hidden(sK1(sK4(X2,sK6),X0),k1_relat_1(sK5(X0,X1))) != iProver_top
% 31.55/4.49      | v1_funct_1(sK5(X0,X1)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(X0,X1)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_8552,c_1927]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_35684,plain,
% 31.55/4.49      ( sK6 = X0
% 31.55/4.49      | r2_hidden(X1,k2_relat_1(sK5(X0,X1))) = iProver_top
% 31.55/4.49      | r2_hidden(sK1(sK4(X2,sK6),X0),X0) != iProver_top
% 31.55/4.49      | v1_funct_1(sK5(X0,X1)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(X0,X1)) != iProver_top ),
% 31.55/4.49      inference(light_normalisation,[status(thm)],[c_35683,c_15]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_36477,plain,
% 31.55/4.49      ( sK6 = X0
% 31.55/4.49      | r2_hidden(X1,k2_relat_1(sK5(X0,X1))) = iProver_top
% 31.55/4.49      | r2_hidden(sK1(sK4(X2,sK6),X0),X0) != iProver_top ),
% 31.55/4.49      inference(global_propositional_subsumption,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_35684,c_23,c_26]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_36490,plain,
% 31.55/4.49      ( sK6 = X0 | r2_hidden(X1,k2_relat_1(sK5(X0,X1))) = iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_8547,c_36477]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_36744,plain,
% 31.55/4.49      ( sK6 = k1_xboole_0
% 31.55/4.49      | r2_hidden(X0,k2_relat_1(k1_xboole_0)) = iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_2886,c_36490]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_65151,plain,
% 31.55/4.49      ( sK0(k2_relat_1(X0),sK6) = sK0(k2_relat_1(X0),sK6) ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_1651]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_65153,plain,
% 31.55/4.49      ( sK0(k2_relat_1(k1_xboole_0),sK6) = sK0(k2_relat_1(k1_xboole_0),sK6) ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_65151]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_83160,plain,
% 31.55/4.49      ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = X1 ),
% 31.55/4.49      inference(global_propositional_subsumption,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_7822,c_19,c_34,c_37,c_39,c_659,c_1666,c_1958,c_2002,
% 31.55/4.49                 c_2068,c_2098,c_2156,c_2187,c_2278,c_3161,c_3166,
% 31.55/4.49                 c_16668,c_25069,c_36744,c_65153]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_3443,plain,
% 31.55/4.49      ( k2_relat_1(sK5(X0,X1)) = X2
% 31.55/4.49      | r2_hidden(sK2(sK5(X0,X1),X2),X0) = iProver_top
% 31.55/4.49      | r2_hidden(sK1(sK5(X0,X1),X2),X2) = iProver_top
% 31.55/4.49      | v1_funct_1(sK5(X0,X1)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(X0,X1)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_15,c_1928]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_4260,plain,
% 31.55/4.49      ( k2_relat_1(sK5(X0,X1)) = X2
% 31.55/4.49      | r2_hidden(sK2(sK5(X0,X1),X2),X0) = iProver_top
% 31.55/4.49      | r2_hidden(sK1(sK5(X0,X1),X2),X2) = iProver_top ),
% 31.55/4.49      inference(global_propositional_subsumption,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_3443,c_23,c_26]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_7460,plain,
% 31.55/4.49      ( k2_relat_1(sK5(X0,X1)) = sK6
% 31.55/4.49      | r2_hidden(sK2(sK5(X0,X1),sK6),X0) = iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_4260,c_7373]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_8387,plain,
% 31.55/4.49      ( k2_relat_1(sK5(sK6,X0)) = sK6 ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_7460,c_7373]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_84053,plain,
% 31.55/4.49      ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = sK6 ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_83160,c_8387]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_84135,plain,
% 31.55/4.49      ( k1_relat_1(k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0))) = X1 ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_83160,c_11]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_84319,plain,
% 31.55/4.49      ( k1_relat_1(k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0))) = k1_xboole_0 ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_84135,c_2886]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1922,plain,
% 31.55/4.49      ( v1_relat_1(sK4(X0,X1)) = iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1923,plain,
% 31.55/4.49      ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2058,plain,
% 31.55/4.49      ( sK7 != X0
% 31.55/4.49      | r2_hidden(sK0(k2_relat_1(sK4(X1,X0)),sK6),k2_relat_1(sK4(X1,X0))) = iProver_top
% 31.55/4.49      | v1_funct_1(sK4(X1,X0)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK4(X1,X0)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_11,c_1918]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2121,plain,
% 31.55/4.49      ( r2_hidden(sK0(k2_relat_1(sK4(X0,sK7)),sK6),k2_relat_1(sK4(X0,sK7))) = iProver_top
% 31.55/4.49      | v1_funct_1(sK4(X0,sK7)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK4(X0,sK7)) != iProver_top ),
% 31.55/4.49      inference(equality_resolution,[status(thm)],[c_2058]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2041,plain,
% 31.55/4.49      ( v1_funct_1(sK4(X0,sK7)) ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_12]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2042,plain,
% 31.55/4.49      ( v1_funct_1(sK4(X0,sK7)) = iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_2041]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2135,plain,
% 31.55/4.49      ( v1_relat_1(sK4(X0,sK7)) ),
% 31.55/4.49      inference(instantiation,[status(thm)],[c_13]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2136,plain,
% 31.55/4.49      ( v1_relat_1(sK4(X0,sK7)) = iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_2135]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2172,plain,
% 31.55/4.49      ( r2_hidden(sK0(k2_relat_1(sK4(X0,sK7)),sK6),k2_relat_1(sK4(X0,sK7))) = iProver_top ),
% 31.55/4.49      inference(global_propositional_subsumption,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_2121,c_2042,c_2136]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_10,plain,
% 31.55/4.49      ( ~ r2_hidden(X0,X1)
% 31.55/4.49      | k1_funct_1(sK4(X2,X1),X0) = o_1_0_funct_1(X2) ),
% 31.55/4.49      inference(cnf_transformation,[],[f45]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_1924,plain,
% 31.55/4.49      ( k1_funct_1(sK4(X0,X1),X2) = o_1_0_funct_1(X0)
% 31.55/4.49      | r2_hidden(X2,X1) != iProver_top ),
% 31.55/4.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_2651,plain,
% 31.55/4.49      ( k1_funct_1(sK4(X0,k1_relat_1(X1)),sK3(X1,X2)) = o_1_0_funct_1(X0)
% 31.55/4.49      | r2_hidden(X2,k2_relat_1(X1)) != iProver_top
% 31.55/4.49      | v1_funct_1(X1) != iProver_top
% 31.55/4.49      | v1_relat_1(X1) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_1925,c_1924]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_4723,plain,
% 31.55/4.49      ( k1_funct_1(sK4(X0,k1_relat_1(sK4(X1,sK7))),sK3(sK4(X1,sK7),sK0(k2_relat_1(sK4(X1,sK7)),sK6))) = o_1_0_funct_1(X0)
% 31.55/4.49      | v1_funct_1(sK4(X1,sK7)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK4(X1,sK7)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_2172,c_2651]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_4734,plain,
% 31.55/4.49      ( k1_funct_1(sK4(X0,sK7),sK3(sK4(X1,sK7),sK0(k2_relat_1(sK4(X1,sK7)),sK6))) = o_1_0_funct_1(X0)
% 31.55/4.49      | v1_funct_1(sK4(X1,sK7)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK4(X1,sK7)) != iProver_top ),
% 31.55/4.49      inference(demodulation,[status(thm)],[c_4723,c_11]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_4835,plain,
% 31.55/4.49      ( k1_funct_1(sK4(X0,sK7),sK3(sK4(X1,sK7),sK0(k2_relat_1(sK4(X1,sK7)),sK6))) = o_1_0_funct_1(X0)
% 31.55/4.49      | v1_relat_1(sK4(X1,sK7)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_1923,c_4734]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_5008,plain,
% 31.55/4.49      ( k1_funct_1(sK4(X0,sK7),sK3(sK4(X1,sK7),sK0(k2_relat_1(sK4(X1,sK7)),sK6))) = o_1_0_funct_1(X0) ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_1922,c_4835]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_3244,plain,
% 31.55/4.49      ( k1_funct_1(sK4(X0,sK7),sK3(sK4(X0,sK7),sK0(k2_relat_1(sK4(X0,sK7)),sK6))) = sK0(k2_relat_1(sK4(X0,sK7)),sK6)
% 31.55/4.49      | v1_funct_1(sK4(X0,sK7)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK4(X0,sK7)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_2172,c_1926]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_3627,plain,
% 31.55/4.49      ( k1_funct_1(sK4(X0,sK7),sK3(sK4(X0,sK7),sK0(k2_relat_1(sK4(X0,sK7)),sK6))) = sK0(k2_relat_1(sK4(X0,sK7)),sK6) ),
% 31.55/4.49      inference(global_propositional_subsumption,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_3244,c_2042,c_2136]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_25427,plain,
% 31.55/4.49      ( sK0(k2_relat_1(sK4(X0,sK7)),sK6) = o_1_0_funct_1(X0) ),
% 31.55/4.49      inference(demodulation,[status(thm)],[c_5008,c_3627]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_84339,plain,
% 31.55/4.49      ( k1_relat_1(k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0))) = o_1_0_funct_1(X1) ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_84135,c_25427]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_4724,plain,
% 31.55/4.49      ( k1_funct_1(sK4(X0,k1_relat_1(sK5(sK7,X1))),sK3(sK5(sK7,X1),sK0(k2_relat_1(sK5(sK7,X1)),sK6))) = o_1_0_funct_1(X0)
% 31.55/4.49      | v1_funct_1(sK5(sK7,X1)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(sK7,X1)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_2343,c_2651]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_4733,plain,
% 31.55/4.49      ( k1_funct_1(sK4(X0,sK7),sK3(sK5(sK7,X1),sK0(k2_relat_1(sK5(sK7,X1)),sK6))) = o_1_0_funct_1(X0)
% 31.55/4.49      | v1_funct_1(sK5(sK7,X1)) != iProver_top
% 31.55/4.49      | v1_relat_1(sK5(sK7,X1)) != iProver_top ),
% 31.55/4.49      inference(demodulation,[status(thm)],[c_4724,c_15]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_4775,plain,
% 31.55/4.49      ( k1_funct_1(sK4(X0,sK7),sK3(sK5(sK7,X1),sK0(k2_relat_1(sK5(sK7,X1)),sK6))) = o_1_0_funct_1(X0)
% 31.55/4.49      | v1_relat_1(sK5(sK7,X1)) != iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_1920,c_4733]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_4890,plain,
% 31.55/4.49      ( k1_funct_1(sK4(X0,sK7),sK3(sK5(sK7,X1),sK0(k2_relat_1(sK5(sK7,X1)),sK6))) = o_1_0_funct_1(X0) ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_1919,c_4775]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_25012,plain,
% 31.55/4.49      ( k1_funct_1(sK4(X0,sK7),sK3(sK5(sK7,X1),X1)) = o_1_0_funct_1(X0) ),
% 31.55/4.49      inference(demodulation,[status(thm)],[c_4890,c_7358]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_84096,plain,
% 31.55/4.49      ( k1_funct_1(k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)),sK3(sK5(sK7,X1),X1)) = o_1_0_funct_1(X2) ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_83160,c_25012]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_84159,plain,
% 31.55/4.49      ( o_1_0_funct_1(X0) = sP1_iProver_split ),
% 31.55/4.49      inference(splitting,
% 31.55/4.49                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 31.55/4.49                [c_84096]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_84948,plain,
% 31.55/4.49      ( k1_relat_1(k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0))) = sP1_iProver_split ),
% 31.55/4.49      inference(demodulation,[status(thm)],[c_84339,c_84159]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_85011,plain,
% 31.55/4.49      ( sP1_iProver_split = k1_xboole_0 ),
% 31.55/4.49      inference(demodulation,[status(thm)],[c_84319,c_84948]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_84090,plain,
% 31.55/4.49      ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = o_1_0_funct_1(X1) ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_83160,c_25427]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_86243,plain,
% 31.55/4.49      ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X0)) = sP1_iProver_split ),
% 31.55/4.49      inference(demodulation,[status(thm)],[c_84090,c_84159]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_86244,plain,
% 31.55/4.49      ( k1_funct_1(sP1_iProver_split,sK3(sP1_iProver_split,X0)) = sP1_iProver_split ),
% 31.55/4.49      inference(light_normalisation,[status(thm)],[c_86243,c_85011]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_87423,plain,
% 31.55/4.49      ( sP1_iProver_split = sK6 ),
% 31.55/4.49      inference(light_normalisation,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_84053,c_85011,c_86244]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_92770,plain,
% 31.55/4.49      ( r2_hidden(X0,sP1_iProver_split) != iProver_top ),
% 31.55/4.49      inference(demodulation,[status(thm)],[c_87423,c_7373]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_7372,plain,
% 31.55/4.49      ( r2_hidden(X0,k2_relat_1(sK5(sK7,X0))) = iProver_top ),
% 31.55/4.49      inference(demodulation,[status(thm)],[c_7358,c_2343]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_84084,plain,
% 31.55/4.49      ( r2_hidden(X0,k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,X1))) = iProver_top ),
% 31.55/4.49      inference(superposition,[status(thm)],[c_83160,c_7372]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_87335,plain,
% 31.55/4.49      ( r2_hidden(X0,k1_funct_1(sP1_iProver_split,sK3(sP1_iProver_split,X1))) = iProver_top ),
% 31.55/4.49      inference(light_normalisation,[status(thm)],[c_84084,c_85011]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_87336,plain,
% 31.55/4.49      ( r2_hidden(X0,sP1_iProver_split) = iProver_top ),
% 31.55/4.49      inference(demodulation,[status(thm)],[c_87335,c_86244]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_92781,plain,
% 31.55/4.49      ( r2_hidden(k1_xboole_0,sP1_iProver_split) != iProver_top ),
% 31.55/4.49      inference(grounding,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_92770:[bind(X0,$fot(k1_xboole_0))]]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(c_92782,plain,
% 31.55/4.49      ( r2_hidden(k1_xboole_0,sP1_iProver_split) = iProver_top ),
% 31.55/4.49      inference(grounding,
% 31.55/4.49                [status(thm)],
% 31.55/4.49                [c_87336:[bind(X0,$fot(k1_xboole_0))]]) ).
% 31.55/4.49  
% 31.55/4.49  cnf(contradiction,plain,
% 31.55/4.49      ( $false ),
% 31.55/4.49      inference(minisat,[status(thm)],[c_92781,c_92782]) ).
% 31.55/4.49  
% 31.55/4.49  
% 31.55/4.49  % SZS output end CNFRefutation for theBenchmark.p
% 31.55/4.49  
% 31.55/4.49  ------                               Statistics
% 31.55/4.49  
% 31.55/4.49  ------ General
% 31.55/4.49  
% 31.55/4.49  abstr_ref_over_cycles:                  0
% 31.55/4.49  abstr_ref_under_cycles:                 0
% 31.55/4.49  gc_basic_clause_elim:                   0
% 31.55/4.49  forced_gc_time:                         0
% 31.55/4.49  parsing_time:                           0.008
% 31.55/4.49  unif_index_cands_time:                  0.
% 31.55/4.49  unif_index_add_time:                    0.
% 31.55/4.49  orderings_time:                         0.
% 31.55/4.49  out_proof_time:                         0.024
% 31.55/4.49  total_time:                             3.664
% 31.55/4.49  num_of_symbols:                         50
% 31.55/4.49  num_of_terms:                           117190
% 31.55/4.49  
% 31.55/4.49  ------ Preprocessing
% 31.55/4.49  
% 31.55/4.49  num_of_splits:                          0
% 31.55/4.49  num_of_split_atoms:                     2
% 31.55/4.49  num_of_reused_defs:                     58
% 31.55/4.49  num_eq_ax_congr_red:                    38
% 31.55/4.49  num_of_sem_filtered_clauses:            1
% 31.55/4.49  num_of_subtypes:                        0
% 31.55/4.49  monotx_restored_types:                  0
% 31.55/4.49  sat_num_of_epr_types:                   0
% 31.55/4.49  sat_num_of_non_cyclic_types:            0
% 31.55/4.49  sat_guarded_non_collapsed_types:        0
% 31.55/4.49  num_pure_diseq_elim:                    0
% 31.55/4.49  simp_replaced_by:                       0
% 31.55/4.49  res_preprocessed:                       94
% 31.55/4.49  prep_upred:                             0
% 31.55/4.49  prep_unflattend:                        76
% 31.55/4.49  smt_new_axioms:                         0
% 31.55/4.49  pred_elim_cands:                        3
% 31.55/4.49  pred_elim:                              1
% 31.55/4.49  pred_elim_cl:                           1
% 31.55/4.49  pred_elim_cycles:                       5
% 31.55/4.49  merged_defs:                            0
% 31.55/4.49  merged_defs_ncl:                        0
% 31.55/4.49  bin_hyper_res:                          0
% 31.55/4.49  prep_cycles:                            4
% 31.55/4.49  pred_elim_time:                         0.02
% 31.55/4.49  splitting_time:                         0.
% 31.55/4.49  sem_filter_time:                        0.
% 31.55/4.49  monotx_time:                            0.
% 31.55/4.49  subtype_inf_time:                       0.
% 31.55/4.49  
% 31.55/4.49  ------ Problem properties
% 31.55/4.49  
% 31.55/4.49  clauses:                                19
% 31.55/4.49  conjectures:                            1
% 31.55/4.49  epr:                                    1
% 31.55/4.49  horn:                                   17
% 31.55/4.49  ground:                                 1
% 31.55/4.49  unary:                                  6
% 31.55/4.49  binary:                                 3
% 31.55/4.49  lits:                                   54
% 31.55/4.49  lits_eq:                                18
% 31.55/4.49  fd_pure:                                0
% 31.55/4.49  fd_pseudo:                              0
% 31.55/4.49  fd_cond:                                2
% 31.55/4.49  fd_pseudo_cond:                         3
% 31.55/4.49  ac_symbols:                             0
% 31.55/4.49  
% 31.55/4.49  ------ Propositional Solver
% 31.55/4.49  
% 31.55/4.49  prop_solver_calls:                      49
% 31.55/4.49  prop_fast_solver_calls:                 4898
% 31.55/4.49  smt_solver_calls:                       0
% 31.55/4.49  smt_fast_solver_calls:                  0
% 31.55/4.49  prop_num_of_clauses:                    42450
% 31.55/4.49  prop_preprocess_simplified:             67110
% 31.55/4.49  prop_fo_subsumed:                       338
% 31.55/4.49  prop_solver_time:                       0.
% 31.55/4.49  smt_solver_time:                        0.
% 31.55/4.49  smt_fast_solver_time:                   0.
% 31.55/4.49  prop_fast_solver_time:                  0.
% 31.55/4.49  prop_unsat_core_time:                   0.004
% 31.55/4.49  
% 31.55/4.49  ------ QBF
% 31.55/4.49  
% 31.55/4.49  qbf_q_res:                              0
% 31.55/4.49  qbf_num_tautologies:                    0
% 31.55/4.49  qbf_prep_cycles:                        0
% 31.55/4.49  
% 31.55/4.49  ------ BMC1
% 31.55/4.49  
% 31.55/4.49  bmc1_current_bound:                     -1
% 31.55/4.49  bmc1_last_solved_bound:                 -1
% 31.55/4.49  bmc1_unsat_core_size:                   -1
% 31.55/4.49  bmc1_unsat_core_parents_size:           -1
% 31.55/4.49  bmc1_merge_next_fun:                    0
% 31.55/4.49  bmc1_unsat_core_clauses_time:           0.
% 31.55/4.49  
% 31.55/4.49  ------ Instantiation
% 31.55/4.49  
% 31.55/4.49  inst_num_of_clauses:                    3566
% 31.55/4.49  inst_num_in_passive:                    1249
% 31.55/4.49  inst_num_in_active:                     2446
% 31.55/4.49  inst_num_in_unprocessed:                1588
% 31.55/4.49  inst_num_of_loops:                      3799
% 31.55/4.49  inst_num_of_learning_restarts:          1
% 31.55/4.49  inst_num_moves_active_passive:          1345
% 31.55/4.49  inst_lit_activity:                      0
% 31.55/4.49  inst_lit_activity_moves:                2
% 31.55/4.49  inst_num_tautologies:                   0
% 31.55/4.49  inst_num_prop_implied:                  0
% 31.55/4.49  inst_num_existing_simplified:           0
% 31.55/4.49  inst_num_eq_res_simplified:             0
% 31.55/4.49  inst_num_child_elim:                    0
% 31.55/4.49  inst_num_of_dismatching_blockings:      7177
% 31.55/4.49  inst_num_of_non_proper_insts:           11156
% 31.55/4.49  inst_num_of_duplicates:                 0
% 31.55/4.49  inst_inst_num_from_inst_to_res:         0
% 31.55/4.49  inst_dismatching_checking_time:         0.
% 31.55/4.49  
% 31.55/4.49  ------ Resolution
% 31.55/4.49  
% 31.55/4.49  res_num_of_clauses:                     27
% 31.55/4.49  res_num_in_passive:                     27
% 31.55/4.49  res_num_in_active:                      0
% 31.55/4.49  res_num_of_loops:                       98
% 31.55/4.49  res_forward_subset_subsumed:            501
% 31.55/4.49  res_backward_subset_subsumed:           14
% 31.55/4.49  res_forward_subsumed:                   0
% 31.55/4.49  res_backward_subsumed:                  0
% 31.55/4.49  res_forward_subsumption_resolution:     8
% 31.55/4.49  res_backward_subsumption_resolution:    0
% 31.55/4.49  res_clause_to_clause_subsumption:       15578
% 31.55/4.49  res_orphan_elimination:                 0
% 31.55/4.49  res_tautology_del:                      501
% 31.55/4.49  res_num_eq_res_simplified:              0
% 31.55/4.49  res_num_sel_changes:                    0
% 31.55/4.49  res_moves_from_active_to_pass:          0
% 31.55/4.49  
% 31.55/4.49  ------ Superposition
% 31.55/4.49  
% 31.55/4.49  sup_time_total:                         0.
% 31.55/4.49  sup_time_generating:                    0.
% 31.55/4.49  sup_time_sim_full:                      0.
% 31.55/4.49  sup_time_sim_immed:                     0.
% 31.55/4.49  
% 31.55/4.49  sup_num_of_clauses:                     2839
% 31.55/4.49  sup_num_in_active:                      23
% 31.55/4.49  sup_num_in_passive:                     2816
% 31.55/4.49  sup_num_of_loops:                       758
% 31.55/4.49  sup_fw_superposition:                   4255
% 31.55/4.49  sup_bw_superposition:                   3812
% 31.55/4.49  sup_immediate_simplified:               5750
% 31.55/4.49  sup_given_eliminated:                   174
% 31.55/4.49  comparisons_done:                       0
% 31.55/4.49  comparisons_avoided:                    753
% 31.55/4.49  
% 31.55/4.49  ------ Simplifications
% 31.55/4.49  
% 31.55/4.49  
% 31.55/4.49  sim_fw_subset_subsumed:                 1101
% 31.55/4.49  sim_bw_subset_subsumed:                 286
% 31.55/4.49  sim_fw_subsumed:                        1363
% 31.55/4.49  sim_bw_subsumed:                        448
% 31.55/4.49  sim_fw_subsumption_res:                 0
% 31.55/4.49  sim_bw_subsumption_res:                 0
% 31.55/4.49  sim_tautology_del:                      28
% 31.55/4.49  sim_eq_tautology_del:                   1943
% 31.55/4.49  sim_eq_res_simp:                        12
% 31.55/4.49  sim_fw_demodulated:                     3349
% 31.55/4.49  sim_bw_demodulated:                     1467
% 31.55/4.49  sim_light_normalised:                   1861
% 31.55/4.49  sim_joinable_taut:                      0
% 31.55/4.49  sim_joinable_simp:                      0
% 31.55/4.49  sim_ac_normalised:                      0
% 31.55/4.49  sim_smt_subsumption:                    0
% 31.55/4.49  
%------------------------------------------------------------------------------
