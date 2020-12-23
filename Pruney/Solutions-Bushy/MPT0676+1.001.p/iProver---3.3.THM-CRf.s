%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0676+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:52 EST 2020

% Result     : Theorem 11.37s
% Output     : CNFRefutation 11.37s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 844 expanded)
%              Number of clauses        :   76 ( 264 expanded)
%              Number of leaves         :   18 ( 184 expanded)
%              Depth                    :   25
%              Number of atoms          :  614 (3751 expanded)
%              Number of equality atoms :  189 ( 690 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) = X1
      <=> sP0(X2,X1,X0) )
      | ~ sP1(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ( ! [X3] :
            ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
            | ~ r2_hidden(X3,k1_relat_1(X1)) )
        & ! [X4] :
            ( r2_hidden(X4,k1_relat_1(X1))
          <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
              & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP1(X0,X1,X2)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f17,f21,f20])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( k8_relat_1(X0,X2) = X1
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k8_relat_1(X0,X2) != X1 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k8_relat_1(X0,X2) != X1
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X2,X0] :
      ( sP0(X2,k8_relat_1(X0,X2),X0)
      | ~ sP1(X0,k8_relat_1(X0,X2),X2) ) ),
    inference(equality_resolution,[],[f53])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))
      & v1_funct_1(sK10)
      & v1_relat_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r1_tarski(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))
    & v1_funct_1(sK10)
    & v1_relat_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f19,f38])).

fof(f68,plain,(
    ~ r1_tarski(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
        & r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK2(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK2(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK2(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK3(X0,X1,X2)) = sK2(X0,X1,X2)
                  & r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
                    & r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f27,f26,f25])).

fof(f40,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f42,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f66,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f39])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ? [X3] :
            ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
              | ~ r2_hidden(X4,k1_relat_1(X2))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                & r2_hidden(X4,k1_relat_1(X2)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & ! [X4] :
              ( ( r2_hidden(X4,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                | ~ r2_hidden(X4,k1_relat_1(X2)) )
              & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                  & r2_hidden(X4,k1_relat_1(X2)) )
                | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ? [X3] :
            ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
              | ~ r2_hidden(X4,k1_relat_1(X2))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                & r2_hidden(X4,k1_relat_1(X2)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & ! [X4] :
              ( ( r2_hidden(X4,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                | ~ r2_hidden(X4,k1_relat_1(X2)) )
              & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                  & r2_hidden(X4,k1_relat_1(X2)) )
                | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X0,X4),X2)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X0,X4),X2)
                & r2_hidden(X4,k1_relat_1(X0)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X5] :
              ( k1_funct_1(X0,X5) = k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,k1_relat_1(X1)) )
          & ! [X6] :
              ( ( r2_hidden(X6,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X0,X6),X2)
                | ~ r2_hidden(X6,k1_relat_1(X0)) )
              & ( ( r2_hidden(k1_funct_1(X0,X6),X2)
                  & r2_hidden(X6,k1_relat_1(X0)) )
                | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f33])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X4),X2)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X4,k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X0,X4),X2)
              & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X4,k1_relat_1(X1)) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK7(X0,X1,X2)),X2)
          | ~ r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK7(X0,X1,X2),k1_relat_1(X1)) )
        & ( ( r2_hidden(k1_funct_1(X0,sK7(X0,X1,X2)),X2)
            & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X0,sK6(X0,X1)) != k1_funct_1(X1,sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( k1_funct_1(X0,sK6(X0,X1)) != k1_funct_1(X1,sK6(X0,X1))
          & r2_hidden(sK6(X0,X1),k1_relat_1(X1)) )
        | ( ( ~ r2_hidden(k1_funct_1(X0,sK7(X0,X1,X2)),X2)
            | ~ r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0))
            | ~ r2_hidden(sK7(X0,X1,X2),k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X0,sK7(X0,X1,X2)),X2)
              & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0)) )
            | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X1)) ) ) )
      & ( ( ! [X5] :
              ( k1_funct_1(X0,X5) = k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,k1_relat_1(X1)) )
          & ! [X6] :
              ( ( r2_hidden(X6,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X0,X6),X2)
                | ~ r2_hidden(X6,k1_relat_1(X0)) )
              & ( ( r2_hidden(k1_funct_1(X0,X6),X2)
                  & r2_hidden(X6,k1_relat_1(X0)) )
                | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f34,f36,f35])).

fof(f57,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X1))
      | ~ r2_hidden(k1_funct_1(X0,X6),X2)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    ! [X2,X0,X5,X1] :
      ( k1_funct_1(X0,X5) = k1_funct_1(X1,X5)
      | ~ r2_hidden(X5,k1_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f43,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f70,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f41,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2430,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3050,plain,
    ( X0 != X1
    | sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) != X1
    | sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) = X0 ),
    inference(instantiation,[status(thm)],[c_2430])).

cnf(c_3449,plain,
    ( X0 != sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))
    | sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) = X0
    | sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) != sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) ),
    inference(instantiation,[status(thm)],[c_3050])).

cnf(c_25152,plain,
    ( sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) != sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))
    | sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) = k1_funct_1(X0,sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))))
    | k1_funct_1(X0,sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)))) != sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) ),
    inference(instantiation,[status(thm)],[c_3449])).

cnf(c_25168,plain,
    ( sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) != sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))
    | sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) = k1_funct_1(sK10,sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))))
    | k1_funct_1(sK10,sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)))) != sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) ),
    inference(instantiation,[status(thm)],[c_25152])).

cnf(c_2433,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2897,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)),k9_relat_1(sK10,sK9))
    | sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) != X0
    | k9_relat_1(sK10,sK9) != X1 ),
    inference(instantiation,[status(thm)],[c_2433])).

cnf(c_2910,plain,
    ( r2_hidden(sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)),k9_relat_1(sK10,sK9))
    | ~ r2_hidden(k1_funct_1(X0,X1),k9_relat_1(X0,X2))
    | sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) != k1_funct_1(X0,X1)
    | k9_relat_1(sK10,sK9) != k9_relat_1(X0,X2) ),
    inference(instantiation,[status(thm)],[c_2897])).

cnf(c_3035,plain,
    ( r2_hidden(sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)),k9_relat_1(sK10,sK9))
    | ~ r2_hidden(k1_funct_1(sK10,X0),k9_relat_1(sK10,sK9))
    | sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) != k1_funct_1(sK10,X0)
    | k9_relat_1(sK10,sK9) != k9_relat_1(sK10,sK9) ),
    inference(instantiation,[status(thm)],[c_2910])).

cnf(c_6688,plain,
    ( r2_hidden(sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)),k9_relat_1(sK10,sK9))
    | ~ r2_hidden(k1_funct_1(sK10,sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)))),k9_relat_1(sK10,sK9))
    | sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) != k1_funct_1(sK10,sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))))
    | k9_relat_1(sK10,sK9) != k9_relat_1(sK10,sK9) ),
    inference(instantiation,[status(thm)],[c_3035])).

cnf(c_25,plain,
    ( sP1(X0,X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_14,plain,
    ( ~ sP1(X0,k8_relat_1(X0,X1),X1)
    | sP0(X1,k8_relat_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_364,plain,
    ( sP0(X0,k8_relat_1(X1,X0),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X0 != X2
    | X1 != X4
    | k8_relat_1(X1,X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_14])).

cnf(c_365,plain,
    ( sP0(X0,k8_relat_1(X1,X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k8_relat_1(X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k8_relat_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_369,plain,
    ( ~ v1_funct_1(X0)
    | sP0(X0,k8_relat_1(X1,X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_12,c_11])).

cnf(c_370,plain,
    ( sP0(X0,k8_relat_1(X1,X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_369])).

cnf(c_2841,plain,
    ( sP0(X0,k8_relat_1(X1,X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK5(X0,X1),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_26,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_323,plain,
    ( r2_hidden(sK5(X0,X1),X0)
    | k9_relat_1(k8_relat_1(sK8,sK10),sK9) != X0
    | k9_relat_1(sK10,sK9) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_26])).

cnf(c_324,plain,
    ( r2_hidden(sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)),k9_relat_1(k8_relat_1(sK8,sK10),sK9)) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_2844,plain,
    ( r2_hidden(sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)),k9_relat_1(k8_relat_1(sK8,sK10),sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2859,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2857,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k8_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK4(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2861,plain,
    ( k1_funct_1(X0,sK4(X0,X1,X2)) = X2
    | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3545,plain,
    ( k1_funct_1(k8_relat_1(sK8,sK10),sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)))) = sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))
    | v1_relat_1(k8_relat_1(sK8,sK10)) != iProver_top
    | v1_funct_1(k8_relat_1(sK8,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2844,c_2861])).

cnf(c_28,negated_conjecture,
    ( v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_29,plain,
    ( v1_relat_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3504,plain,
    ( v1_relat_1(k8_relat_1(sK8,sK10))
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3505,plain,
    ( v1_relat_1(k8_relat_1(sK8,sK10)) = iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3504])).

cnf(c_3551,plain,
    ( k1_funct_1(k8_relat_1(sK8,sK10),sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)))) = sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))
    | v1_funct_1(k8_relat_1(sK8,sK10)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3545,c_29,c_3505])).

cnf(c_3555,plain,
    ( k1_funct_1(k8_relat_1(sK8,sK10),sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)))) = sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))
    | v1_relat_1(sK10) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_2857,c_3551])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,plain,
    ( v1_funct_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3616,plain,
    ( k1_funct_1(k8_relat_1(sK8,sK10),sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)))) = sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3555,c_29,c_30])).

cnf(c_22,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(X3,k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X0,X3),X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2849,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,k1_relat_1(X0)) != iProver_top
    | r2_hidden(X3,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k1_funct_1(X0,X3),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3807,plain,
    ( sP0(k8_relat_1(sK8,sK10),X0,X1) != iProver_top
    | r2_hidden(sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))),k1_relat_1(k8_relat_1(sK8,sK10))) != iProver_top
    | r2_hidden(sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3616,c_2849])).

cnf(c_3812,plain,
    ( sP0(k8_relat_1(sK8,sK10),X0,X1) != iProver_top
    | r2_hidden(sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)),X1) != iProver_top
    | r2_hidden(sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)),k9_relat_1(k8_relat_1(sK8,sK10),sK9)) != iProver_top
    | v1_relat_1(k8_relat_1(sK8,sK10)) != iProver_top
    | v1_funct_1(k8_relat_1(sK8,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2859,c_3807])).

cnf(c_325,plain,
    ( r2_hidden(sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)),k9_relat_1(k8_relat_1(sK8,sK10),sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_3926,plain,
    ( sP0(k8_relat_1(sK8,sK10),X0,X1) != iProver_top
    | r2_hidden(sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))),k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)),X1) != iProver_top
    | v1_funct_1(k8_relat_1(sK8,sK10)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3812,c_29,c_325,c_3505])).

cnf(c_3932,plain,
    ( sP0(k8_relat_1(sK8,sK10),X0,k9_relat_1(k8_relat_1(sK8,sK10),sK9)) != iProver_top
    | r2_hidden(sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(k8_relat_1(sK8,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2844,c_3926])).

cnf(c_4035,plain,
    ( ~ v1_relat_1(sK10)
    | v1_funct_1(k8_relat_1(sK8,sK10))
    | ~ v1_funct_1(sK10) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4036,plain,
    ( v1_relat_1(sK10) != iProver_top
    | v1_funct_1(k8_relat_1(sK8,sK10)) = iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4035])).

cnf(c_4348,plain,
    ( r2_hidden(sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))),k1_relat_1(X0)) = iProver_top
    | sP0(k8_relat_1(sK8,sK10),X0,k9_relat_1(k8_relat_1(sK8,sK10),sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3932,c_29,c_30,c_4036])).

cnf(c_4349,plain,
    ( sP0(k8_relat_1(sK8,sK10),X0,k9_relat_1(k8_relat_1(sK8,sK10),sK9)) != iProver_top
    | r2_hidden(sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))),k1_relat_1(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4348])).

cnf(c_24,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | r2_hidden(X3,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2847,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X3,k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3182,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(k8_relat_1(X2,X1))) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2841,c_2847])).

cnf(c_4354,plain,
    ( sP0(k8_relat_1(sK8,sK10),k8_relat_1(X0,X1),k9_relat_1(k8_relat_1(sK8,sK10),sK9)) != iProver_top
    | r2_hidden(sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4349,c_3182])).

cnf(c_4367,plain,
    ( r2_hidden(sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))),k1_relat_1(k8_relat_1(sK8,sK10))) = iProver_top
    | v1_relat_1(k8_relat_1(sK8,sK10)) != iProver_top
    | v1_funct_1(k8_relat_1(sK8,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2841,c_4354])).

cnf(c_4865,plain,
    ( r2_hidden(sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))),k1_relat_1(k8_relat_1(sK8,sK10))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4367,c_29,c_30,c_3505,c_4036])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2850,plain,
    ( k1_funct_1(X0,X1) = k1_funct_1(X2,X1)
    | sP0(X2,X0,X3) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3468,plain,
    ( k1_funct_1(k8_relat_1(X0,X1),X2) = k1_funct_1(X1,X2)
    | r2_hidden(X2,k1_relat_1(k8_relat_1(X0,X1))) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2841,c_2850])).

cnf(c_6028,plain,
    ( k1_funct_1(k8_relat_1(sK8,sK10),sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)))) = k1_funct_1(sK10,sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))))
    | v1_relat_1(sK10) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_4865,c_3468])).

cnf(c_6033,plain,
    ( k1_funct_1(sK10,sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)))) = sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))
    | v1_relat_1(sK10) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6028,c_3616])).

cnf(c_4869,plain,
    ( r2_hidden(sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))),k1_relat_1(sK10)) = iProver_top
    | v1_relat_1(sK10) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_4865,c_3182])).

cnf(c_4871,plain,
    ( r2_hidden(sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))),k1_relat_1(sK10))
    | ~ v1_relat_1(sK10)
    | ~ v1_funct_1(sK10) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4869])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3399,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK10))
    | ~ r2_hidden(X0,sK9)
    | r2_hidden(k1_funct_1(sK10,X0),k9_relat_1(sK10,sK9))
    | ~ v1_relat_1(sK10)
    | ~ v1_funct_1(sK10) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4794,plain,
    ( ~ r2_hidden(sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))),k1_relat_1(sK10))
    | ~ r2_hidden(sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))),sK9)
    | r2_hidden(k1_funct_1(sK10,sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)))),k9_relat_1(sK10,sK9))
    | ~ v1_relat_1(sK10)
    | ~ v1_funct_1(sK10) ),
    inference(instantiation,[status(thm)],[c_3399])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3914,plain,
    ( r2_hidden(sK4(k8_relat_1(sK8,sK10),sK9,sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9))),sK9)
    | ~ r2_hidden(sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)),k9_relat_1(k8_relat_1(sK8,sK10),sK9))
    | ~ v1_relat_1(k8_relat_1(sK8,sK10))
    | ~ v1_funct_1(k8_relat_1(sK8,sK10)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2429,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3072,plain,
    ( k9_relat_1(sK10,sK9) = k9_relat_1(sK10,sK9) ),
    inference(instantiation,[status(thm)],[c_2429])).

cnf(c_3021,plain,
    ( sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) = sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)) ),
    inference(instantiation,[status(thm)],[c_2429])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK5(X0,X1),X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_330,plain,
    ( ~ r2_hidden(sK5(X0,X1),X1)
    | k9_relat_1(k8_relat_1(sK8,sK10),sK9) != X0
    | k9_relat_1(sK10,sK9) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_26])).

cnf(c_331,plain,
    ( ~ r2_hidden(sK5(k9_relat_1(k8_relat_1(sK8,sK10),sK9),k9_relat_1(sK10,sK9)),k9_relat_1(sK10,sK9)) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25168,c_6688,c_6033,c_4871,c_4794,c_4035,c_3914,c_3504,c_3072,c_3021,c_331,c_324,c_30,c_27,c_29,c_28])).


%------------------------------------------------------------------------------
