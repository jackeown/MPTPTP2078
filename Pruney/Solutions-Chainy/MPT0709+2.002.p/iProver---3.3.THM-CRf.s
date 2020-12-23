%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:35 EST 2020

% Result     : Theorem 23.73s
% Output     : CNFRefutation 23.73s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 299 expanded)
%              Number of clauses        :   69 (  84 expanded)
%              Number of leaves         :   21 (  69 expanded)
%              Depth                    :   24
%              Number of atoms          :  420 ( 892 expanded)
%              Number of equality atoms :  132 ( 276 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f45,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f46,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f61,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k10_relat_1(sK4,k9_relat_1(sK4,sK3)) != sK3
      & v2_funct_1(sK4)
      & r1_tarski(sK3,k1_relat_1(sK4))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,sK3)) != sK3
    & v2_funct_1(sK4)
    & r1_tarski(sK3,k1_relat_1(sK4))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f46,f61])).

fof(f102,plain,(
    r1_tarski(sK3,k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f62])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f100,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f79,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f105,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f76,f77])).

fof(f106,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f75,f105])).

fof(f107,plain,(
    ! [X0,X1] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f78,f106])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f97,f107])).

fof(f101,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f23,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f110,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f99,f107])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f108,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f74,f106,f106])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f18,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f103,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f56])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
            & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
                | ~ r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
                  & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f58,f59])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f115,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f104,plain,(
    k10_relat_1(sK4,k9_relat_1(sK4,sK3)) != sK3 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_35,negated_conjecture,
    ( r1_tarski(sK3,k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_6698,plain,
    ( r1_tarski(sK3,k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_28,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_6699,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_37,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_6697,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_6706,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7578,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_6697,c_6706])).

cnf(c_30,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_513,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_36])).

cnf(c_514,plain,
    ( ~ v1_relat_1(sK4)
    | k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k9_relat_1(sK4,k1_relat_1(sK4)))) = k9_relat_1(sK4,k10_relat_1(sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_518,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k9_relat_1(sK4,k1_relat_1(sK4)))) = k9_relat_1(sK4,k10_relat_1(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_37])).

cnf(c_32,plain,
    ( k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_7142,plain,
    ( k5_relat_1(k6_relat_1(k9_relat_1(sK4,k1_relat_1(sK4))),k6_relat_1(X0)) = k6_relat_1(k9_relat_1(sK4,k10_relat_1(sK4,X0))) ),
    inference(superposition,[status(thm)],[c_518,c_32])).

cnf(c_7651,plain,
    ( k6_relat_1(k9_relat_1(sK4,k10_relat_1(sK4,X0))) = k5_relat_1(k6_relat_1(k2_relat_1(sK4)),k6_relat_1(X0)) ),
    inference(demodulation,[status(thm)],[c_7578,c_7142])).

cnf(c_11,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_7143,plain,
    ( k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_11,c_32])).

cnf(c_19,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_7145,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_32,c_19])).

cnf(c_7177,plain,
    ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(light_normalisation,[status(thm)],[c_7143,c_7145])).

cnf(c_9647,plain,
    ( k6_relat_1(k1_relat_1(k6_relat_1(k9_relat_1(sK4,k10_relat_1(sK4,X0))))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(sK4))) ),
    inference(superposition,[status(thm)],[c_7651,c_7177])).

cnf(c_9698,plain,
    ( k6_relat_1(k9_relat_1(sK4,k10_relat_1(sK4,X0))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(sK4))) ),
    inference(demodulation,[status(thm)],[c_9647,c_19])).

cnf(c_27,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_6700,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6701,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7560,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6700,c_6701])).

cnf(c_23483,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_6700,c_7560])).

cnf(c_23491,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_23483,c_19])).

cnf(c_23532,plain,
    ( k1_relat_1(k6_relat_1(k9_relat_1(sK4,k10_relat_1(sK4,X0)))) = k10_relat_1(k6_relat_1(X0),k2_relat_1(sK4)) ),
    inference(superposition,[status(thm)],[c_9698,c_23491])).

cnf(c_23553,plain,
    ( k10_relat_1(k6_relat_1(X0),k2_relat_1(sK4)) = k9_relat_1(sK4,k10_relat_1(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_23532,c_19])).

cnf(c_15,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_6703,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8116,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_6703])).

cnf(c_58,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8562,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8116,c_58])).

cnf(c_23576,plain,
    ( r1_tarski(k9_relat_1(sK4,k10_relat_1(sK4,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_23553,c_8562])).

cnf(c_31,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_396,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_34])).

cnf(c_397,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_399,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_37,c_36])).

cnf(c_6692,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_24524,plain,
    ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) = iProver_top
    | r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23576,c_6692])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_6715,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_608,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_609,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_613,plain,
    ( r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(X0,k10_relat_1(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_37])).

cnf(c_614,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
    | r2_hidden(X0,k1_relat_1(sK4)) ),
    inference(renaming,[status(thm)],[c_613])).

cnf(c_6687,plain,
    ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_7914,plain,
    ( r2_hidden(sK0(k10_relat_1(sK4,X0),X1),k1_relat_1(sK4)) = iProver_top
    | r1_tarski(k10_relat_1(sK4,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6715,c_6687])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_6716,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8312,plain,
    ( r1_tarski(k10_relat_1(sK4,X0),k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7914,c_6716])).

cnf(c_24784,plain,
    ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_24524,c_8312])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_6710,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_24794,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k10_relat_1(sK4,k9_relat_1(sK4,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_24784,c_6710])).

cnf(c_54797,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6699,c_24794])).

cnf(c_38,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_74419,plain,
    ( r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_54797,c_38])).

cnf(c_74420,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_74419])).

cnf(c_74430,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_6698,c_74420])).

cnf(c_33,negated_conjecture,
    ( k10_relat_1(sK4,k9_relat_1(sK4,sK3)) != sK3 ),
    inference(cnf_transformation,[],[f104])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_74430,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:18:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.73/3.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.73/3.50  
% 23.73/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.73/3.50  
% 23.73/3.50  ------  iProver source info
% 23.73/3.50  
% 23.73/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.73/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.73/3.50  git: non_committed_changes: false
% 23.73/3.50  git: last_make_outside_of_git: false
% 23.73/3.50  
% 23.73/3.50  ------ 
% 23.73/3.50  ------ Parsing...
% 23.73/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  ------ Proving...
% 23.73/3.50  ------ Problem Properties 
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  clauses                                 35
% 23.73/3.50  conjectures                             4
% 23.73/3.50  EPR                                     6
% 23.73/3.50  Horn                                    30
% 23.73/3.50  unary                                   11
% 23.73/3.50  binary                                  11
% 23.73/3.50  lits                                    74
% 23.73/3.50  lits eq                                 18
% 23.73/3.50  fd_pure                                 0
% 23.73/3.50  fd_pseudo                               0
% 23.73/3.50  fd_cond                                 0
% 23.73/3.50  fd_pseudo_cond                          4
% 23.73/3.50  AC symbols                              0
% 23.73/3.50  
% 23.73/3.50  ------ Input Options Time Limit: Unbounded
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 23.73/3.50  Current options:
% 23.73/3.50  ------ 
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.73/3.50  
% 23.73/3.50  ------ Proving...
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  % SZS status Theorem for theBenchmark.p
% 23.73/3.50  
% 23.73/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.73/3.50  
% 23.73/3.50  fof(f24,conjecture,(
% 23.73/3.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f25,negated_conjecture,(
% 23.73/3.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 23.73/3.50    inference(negated_conjecture,[],[f24])).
% 23.73/3.50  
% 23.73/3.50  fof(f45,plain,(
% 23.73/3.50    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 23.73/3.50    inference(ennf_transformation,[],[f25])).
% 23.73/3.50  
% 23.73/3.50  fof(f46,plain,(
% 23.73/3.50    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 23.73/3.50    inference(flattening,[],[f45])).
% 23.73/3.50  
% 23.73/3.50  fof(f61,plain,(
% 23.73/3.50    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k10_relat_1(sK4,k9_relat_1(sK4,sK3)) != sK3 & v2_funct_1(sK4) & r1_tarski(sK3,k1_relat_1(sK4)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 23.73/3.50    introduced(choice_axiom,[])).
% 23.73/3.50  
% 23.73/3.50  fof(f62,plain,(
% 23.73/3.50    k10_relat_1(sK4,k9_relat_1(sK4,sK3)) != sK3 & v2_funct_1(sK4) & r1_tarski(sK3,k1_relat_1(sK4)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 23.73/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f46,f61])).
% 23.73/3.50  
% 23.73/3.50  fof(f102,plain,(
% 23.73/3.50    r1_tarski(sK3,k1_relat_1(sK4))),
% 23.73/3.50    inference(cnf_transformation,[],[f62])).
% 23.73/3.50  
% 23.73/3.50  fof(f19,axiom,(
% 23.73/3.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f37,plain,(
% 23.73/3.50    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 23.73/3.50    inference(ennf_transformation,[],[f19])).
% 23.73/3.50  
% 23.73/3.50  fof(f38,plain,(
% 23.73/3.50    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 23.73/3.50    inference(flattening,[],[f37])).
% 23.73/3.50  
% 23.73/3.50  fof(f95,plain,(
% 23.73/3.50    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 23.73/3.50    inference(cnf_transformation,[],[f38])).
% 23.73/3.50  
% 23.73/3.50  fof(f100,plain,(
% 23.73/3.50    v1_relat_1(sK4)),
% 23.73/3.50    inference(cnf_transformation,[],[f62])).
% 23.73/3.50  
% 23.73/3.50  fof(f11,axiom,(
% 23.73/3.50    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f30,plain,(
% 23.73/3.50    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 23.73/3.50    inference(ennf_transformation,[],[f11])).
% 23.73/3.50  
% 23.73/3.50  fof(f79,plain,(
% 23.73/3.50    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 23.73/3.50    inference(cnf_transformation,[],[f30])).
% 23.73/3.50  
% 23.73/3.50  fof(f21,axiom,(
% 23.73/3.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f41,plain,(
% 23.73/3.50    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 23.73/3.50    inference(ennf_transformation,[],[f21])).
% 23.73/3.50  
% 23.73/3.50  fof(f42,plain,(
% 23.73/3.50    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 23.73/3.50    inference(flattening,[],[f41])).
% 23.73/3.50  
% 23.73/3.50  fof(f97,plain,(
% 23.73/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 23.73/3.50    inference(cnf_transformation,[],[f42])).
% 23.73/3.50  
% 23.73/3.50  fof(f10,axiom,(
% 23.73/3.50    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f78,plain,(
% 23.73/3.50    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 23.73/3.50    inference(cnf_transformation,[],[f10])).
% 23.73/3.50  
% 23.73/3.50  fof(f7,axiom,(
% 23.73/3.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f75,plain,(
% 23.73/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.73/3.50    inference(cnf_transformation,[],[f7])).
% 23.73/3.50  
% 23.73/3.50  fof(f8,axiom,(
% 23.73/3.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f76,plain,(
% 23.73/3.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.73/3.50    inference(cnf_transformation,[],[f8])).
% 23.73/3.50  
% 23.73/3.50  fof(f9,axiom,(
% 23.73/3.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f77,plain,(
% 23.73/3.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 23.73/3.50    inference(cnf_transformation,[],[f9])).
% 23.73/3.50  
% 23.73/3.50  fof(f105,plain,(
% 23.73/3.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 23.73/3.50    inference(definition_unfolding,[],[f76,f77])).
% 23.73/3.50  
% 23.73/3.50  fof(f106,plain,(
% 23.73/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 23.73/3.50    inference(definition_unfolding,[],[f75,f105])).
% 23.73/3.50  
% 23.73/3.50  fof(f107,plain,(
% 23.73/3.50    ( ! [X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 23.73/3.50    inference(definition_unfolding,[],[f78,f106])).
% 23.73/3.50  
% 23.73/3.50  fof(f109,plain,(
% 23.73/3.50    ( ! [X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 23.73/3.50    inference(definition_unfolding,[],[f97,f107])).
% 23.73/3.50  
% 23.73/3.50  fof(f101,plain,(
% 23.73/3.50    v1_funct_1(sK4)),
% 23.73/3.50    inference(cnf_transformation,[],[f62])).
% 23.73/3.50  
% 23.73/3.50  fof(f23,axiom,(
% 23.73/3.50    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f99,plain,(
% 23.73/3.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 23.73/3.50    inference(cnf_transformation,[],[f23])).
% 23.73/3.50  
% 23.73/3.50  fof(f110,plain,(
% 23.73/3.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 23.73/3.50    inference(definition_unfolding,[],[f99,f107])).
% 23.73/3.50  
% 23.73/3.50  fof(f6,axiom,(
% 23.73/3.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f74,plain,(
% 23.73/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 23.73/3.50    inference(cnf_transformation,[],[f6])).
% 23.73/3.50  
% 23.73/3.50  fof(f108,plain,(
% 23.73/3.50    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 23.73/3.50    inference(definition_unfolding,[],[f74,f106,f106])).
% 23.73/3.50  
% 23.73/3.50  fof(f16,axiom,(
% 23.73/3.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f85,plain,(
% 23.73/3.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 23.73/3.50    inference(cnf_transformation,[],[f16])).
% 23.73/3.50  
% 23.73/3.50  fof(f18,axiom,(
% 23.73/3.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f93,plain,(
% 23.73/3.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 23.73/3.50    inference(cnf_transformation,[],[f18])).
% 23.73/3.50  
% 23.73/3.50  fof(f15,axiom,(
% 23.73/3.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f34,plain,(
% 23.73/3.50    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 23.73/3.50    inference(ennf_transformation,[],[f15])).
% 23.73/3.50  
% 23.73/3.50  fof(f84,plain,(
% 23.73/3.50    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 23.73/3.50    inference(cnf_transformation,[],[f34])).
% 23.73/3.50  
% 23.73/3.50  fof(f13,axiom,(
% 23.73/3.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f32,plain,(
% 23.73/3.50    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 23.73/3.50    inference(ennf_transformation,[],[f13])).
% 23.73/3.50  
% 23.73/3.50  fof(f82,plain,(
% 23.73/3.50    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 23.73/3.50    inference(cnf_transformation,[],[f32])).
% 23.73/3.50  
% 23.73/3.50  fof(f22,axiom,(
% 23.73/3.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f43,plain,(
% 23.73/3.50    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 23.73/3.50    inference(ennf_transformation,[],[f22])).
% 23.73/3.50  
% 23.73/3.50  fof(f44,plain,(
% 23.73/3.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 23.73/3.50    inference(flattening,[],[f43])).
% 23.73/3.50  
% 23.73/3.50  fof(f98,plain,(
% 23.73/3.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 23.73/3.50    inference(cnf_transformation,[],[f44])).
% 23.73/3.50  
% 23.73/3.50  fof(f103,plain,(
% 23.73/3.50    v2_funct_1(sK4)),
% 23.73/3.50    inference(cnf_transformation,[],[f62])).
% 23.73/3.50  
% 23.73/3.50  fof(f1,axiom,(
% 23.73/3.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f27,plain,(
% 23.73/3.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 23.73/3.50    inference(ennf_transformation,[],[f1])).
% 23.73/3.50  
% 23.73/3.50  fof(f47,plain,(
% 23.73/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 23.73/3.50    inference(nnf_transformation,[],[f27])).
% 23.73/3.50  
% 23.73/3.50  fof(f48,plain,(
% 23.73/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.73/3.50    inference(rectify,[],[f47])).
% 23.73/3.50  
% 23.73/3.50  fof(f49,plain,(
% 23.73/3.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.73/3.50    introduced(choice_axiom,[])).
% 23.73/3.50  
% 23.73/3.50  fof(f50,plain,(
% 23.73/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.73/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 23.73/3.50  
% 23.73/3.50  fof(f64,plain,(
% 23.73/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 23.73/3.50    inference(cnf_transformation,[],[f50])).
% 23.73/3.50  
% 23.73/3.50  fof(f17,axiom,(
% 23.73/3.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f35,plain,(
% 23.73/3.50    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 23.73/3.50    inference(ennf_transformation,[],[f17])).
% 23.73/3.50  
% 23.73/3.50  fof(f36,plain,(
% 23.73/3.50    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.73/3.50    inference(flattening,[],[f35])).
% 23.73/3.50  
% 23.73/3.50  fof(f56,plain,(
% 23.73/3.50    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.73/3.50    inference(nnf_transformation,[],[f36])).
% 23.73/3.50  
% 23.73/3.50  fof(f57,plain,(
% 23.73/3.50    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.73/3.50    inference(flattening,[],[f56])).
% 23.73/3.50  
% 23.73/3.50  fof(f58,plain,(
% 23.73/3.50    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.73/3.50    inference(rectify,[],[f57])).
% 23.73/3.50  
% 23.73/3.50  fof(f59,plain,(
% 23.73/3.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 23.73/3.50    introduced(choice_axiom,[])).
% 23.73/3.50  
% 23.73/3.50  fof(f60,plain,(
% 23.73/3.50    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((~r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1) | ~r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.73/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f58,f59])).
% 23.73/3.50  
% 23.73/3.50  fof(f87,plain,(
% 23.73/3.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.73/3.50    inference(cnf_transformation,[],[f60])).
% 23.73/3.50  
% 23.73/3.50  fof(f115,plain,(
% 23.73/3.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.73/3.50    inference(equality_resolution,[],[f87])).
% 23.73/3.50  
% 23.73/3.50  fof(f65,plain,(
% 23.73/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 23.73/3.50    inference(cnf_transformation,[],[f50])).
% 23.73/3.50  
% 23.73/3.50  fof(f3,axiom,(
% 23.73/3.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.73/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.73/3.50  
% 23.73/3.50  fof(f53,plain,(
% 23.73/3.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.73/3.50    inference(nnf_transformation,[],[f3])).
% 23.73/3.50  
% 23.73/3.50  fof(f54,plain,(
% 23.73/3.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.73/3.50    inference(flattening,[],[f53])).
% 23.73/3.50  
% 23.73/3.50  fof(f71,plain,(
% 23.73/3.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.73/3.50    inference(cnf_transformation,[],[f54])).
% 23.73/3.50  
% 23.73/3.50  fof(f104,plain,(
% 23.73/3.50    k10_relat_1(sK4,k9_relat_1(sK4,sK3)) != sK3),
% 23.73/3.50    inference(cnf_transformation,[],[f62])).
% 23.73/3.50  
% 23.73/3.50  cnf(c_35,negated_conjecture,
% 23.73/3.50      ( r1_tarski(sK3,k1_relat_1(sK4)) ),
% 23.73/3.50      inference(cnf_transformation,[],[f102]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_6698,plain,
% 23.73/3.50      ( r1_tarski(sK3,k1_relat_1(sK4)) = iProver_top ),
% 23.73/3.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_28,plain,
% 23.73/3.50      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 23.73/3.50      | ~ r1_tarski(X0,k1_relat_1(X1))
% 23.73/3.50      | ~ v1_relat_1(X1) ),
% 23.73/3.50      inference(cnf_transformation,[],[f95]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_6699,plain,
% 23.73/3.50      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 23.73/3.50      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 23.73/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.73/3.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_37,negated_conjecture,
% 23.73/3.50      ( v1_relat_1(sK4) ),
% 23.73/3.50      inference(cnf_transformation,[],[f100]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_6697,plain,
% 23.73/3.50      ( v1_relat_1(sK4) = iProver_top ),
% 23.73/3.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_12,plain,
% 23.73/3.50      ( ~ v1_relat_1(X0)
% 23.73/3.50      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 23.73/3.50      inference(cnf_transformation,[],[f79]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_6706,plain,
% 23.73/3.50      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 23.73/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.73/3.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_7578,plain,
% 23.73/3.50      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 23.73/3.50      inference(superposition,[status(thm)],[c_6697,c_6706]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_30,plain,
% 23.73/3.50      ( ~ v1_funct_1(X0)
% 23.73/3.50      | ~ v1_relat_1(X0)
% 23.73/3.50      | k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 23.73/3.50      inference(cnf_transformation,[],[f109]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_36,negated_conjecture,
% 23.73/3.50      ( v1_funct_1(sK4) ),
% 23.73/3.50      inference(cnf_transformation,[],[f101]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_513,plain,
% 23.73/3.50      ( ~ v1_relat_1(X0)
% 23.73/3.50      | k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
% 23.73/3.50      | sK4 != X0 ),
% 23.73/3.50      inference(resolution_lifted,[status(thm)],[c_30,c_36]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_514,plain,
% 23.73/3.50      ( ~ v1_relat_1(sK4)
% 23.73/3.50      | k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k9_relat_1(sK4,k1_relat_1(sK4)))) = k9_relat_1(sK4,k10_relat_1(sK4,X0)) ),
% 23.73/3.50      inference(unflattening,[status(thm)],[c_513]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_518,plain,
% 23.73/3.50      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k9_relat_1(sK4,k1_relat_1(sK4)))) = k9_relat_1(sK4,k10_relat_1(sK4,X0)) ),
% 23.73/3.50      inference(global_propositional_subsumption,
% 23.73/3.50                [status(thm)],
% 23.73/3.50                [c_514,c_37]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_32,plain,
% 23.73/3.50      ( k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 23.73/3.50      inference(cnf_transformation,[],[f110]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_7142,plain,
% 23.73/3.50      ( k5_relat_1(k6_relat_1(k9_relat_1(sK4,k1_relat_1(sK4))),k6_relat_1(X0)) = k6_relat_1(k9_relat_1(sK4,k10_relat_1(sK4,X0))) ),
% 23.73/3.50      inference(superposition,[status(thm)],[c_518,c_32]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_7651,plain,
% 23.73/3.50      ( k6_relat_1(k9_relat_1(sK4,k10_relat_1(sK4,X0))) = k5_relat_1(k6_relat_1(k2_relat_1(sK4)),k6_relat_1(X0)) ),
% 23.73/3.50      inference(demodulation,[status(thm)],[c_7578,c_7142]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_11,plain,
% 23.73/3.50      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 23.73/3.50      inference(cnf_transformation,[],[f108]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_7143,plain,
% 23.73/3.50      ( k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 23.73/3.50      inference(superposition,[status(thm)],[c_11,c_32]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_19,plain,
% 23.73/3.50      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 23.73/3.50      inference(cnf_transformation,[],[f85]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_7145,plain,
% 23.73/3.50      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 23.73/3.50      inference(superposition,[status(thm)],[c_32,c_19]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_7177,plain,
% 23.73/3.50      ( k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 23.73/3.50      inference(light_normalisation,[status(thm)],[c_7143,c_7145]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_9647,plain,
% 23.73/3.50      ( k6_relat_1(k1_relat_1(k6_relat_1(k9_relat_1(sK4,k10_relat_1(sK4,X0))))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(sK4))) ),
% 23.73/3.50      inference(superposition,[status(thm)],[c_7651,c_7177]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_9698,plain,
% 23.73/3.50      ( k6_relat_1(k9_relat_1(sK4,k10_relat_1(sK4,X0))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(sK4))) ),
% 23.73/3.50      inference(demodulation,[status(thm)],[c_9647,c_19]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_27,plain,
% 23.73/3.50      ( v1_relat_1(k6_relat_1(X0)) ),
% 23.73/3.50      inference(cnf_transformation,[],[f93]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_6700,plain,
% 23.73/3.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 23.73/3.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_17,plain,
% 23.73/3.50      ( ~ v1_relat_1(X0)
% 23.73/3.50      | ~ v1_relat_1(X1)
% 23.73/3.50      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 23.73/3.50      inference(cnf_transformation,[],[f84]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_6701,plain,
% 23.73/3.50      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 23.73/3.50      | v1_relat_1(X0) != iProver_top
% 23.73/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.73/3.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_7560,plain,
% 23.73/3.50      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
% 23.73/3.50      | v1_relat_1(X1) != iProver_top ),
% 23.73/3.50      inference(superposition,[status(thm)],[c_6700,c_6701]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_23483,plain,
% 23.73/3.50      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
% 23.73/3.50      inference(superposition,[status(thm)],[c_6700,c_7560]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_23491,plain,
% 23.73/3.50      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
% 23.73/3.50      inference(demodulation,[status(thm)],[c_23483,c_19]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_23532,plain,
% 23.73/3.50      ( k1_relat_1(k6_relat_1(k9_relat_1(sK4,k10_relat_1(sK4,X0)))) = k10_relat_1(k6_relat_1(X0),k2_relat_1(sK4)) ),
% 23.73/3.50      inference(superposition,[status(thm)],[c_9698,c_23491]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_23553,plain,
% 23.73/3.50      ( k10_relat_1(k6_relat_1(X0),k2_relat_1(sK4)) = k9_relat_1(sK4,k10_relat_1(sK4,X0)) ),
% 23.73/3.50      inference(demodulation,[status(thm)],[c_23532,c_19]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_15,plain,
% 23.73/3.50      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 23.73/3.50      inference(cnf_transformation,[],[f82]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_6703,plain,
% 23.73/3.50      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 23.73/3.50      | v1_relat_1(X0) != iProver_top ),
% 23.73/3.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_8116,plain,
% 23.73/3.50      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top
% 23.73/3.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 23.73/3.50      inference(superposition,[status(thm)],[c_19,c_6703]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_58,plain,
% 23.73/3.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 23.73/3.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_8562,plain,
% 23.73/3.50      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
% 23.73/3.50      inference(global_propositional_subsumption,
% 23.73/3.50                [status(thm)],
% 23.73/3.50                [c_8116,c_58]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_23576,plain,
% 23.73/3.50      ( r1_tarski(k9_relat_1(sK4,k10_relat_1(sK4,X0)),X0) = iProver_top ),
% 23.73/3.50      inference(superposition,[status(thm)],[c_23553,c_8562]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_31,plain,
% 23.73/3.50      ( r1_tarski(X0,X1)
% 23.73/3.50      | ~ r1_tarski(X0,k1_relat_1(X2))
% 23.73/3.50      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 23.73/3.50      | ~ v2_funct_1(X2)
% 23.73/3.50      | ~ v1_funct_1(X2)
% 23.73/3.50      | ~ v1_relat_1(X2) ),
% 23.73/3.50      inference(cnf_transformation,[],[f98]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_34,negated_conjecture,
% 23.73/3.50      ( v2_funct_1(sK4) ),
% 23.73/3.50      inference(cnf_transformation,[],[f103]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_396,plain,
% 23.73/3.50      ( r1_tarski(X0,X1)
% 23.73/3.50      | ~ r1_tarski(X0,k1_relat_1(X2))
% 23.73/3.50      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 23.73/3.50      | ~ v1_funct_1(X2)
% 23.73/3.50      | ~ v1_relat_1(X2)
% 23.73/3.50      | sK4 != X2 ),
% 23.73/3.50      inference(resolution_lifted,[status(thm)],[c_31,c_34]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_397,plain,
% 23.73/3.50      ( r1_tarski(X0,X1)
% 23.73/3.50      | ~ r1_tarski(X0,k1_relat_1(sK4))
% 23.73/3.50      | ~ r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1))
% 23.73/3.50      | ~ v1_funct_1(sK4)
% 23.73/3.50      | ~ v1_relat_1(sK4) ),
% 23.73/3.50      inference(unflattening,[status(thm)],[c_396]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_399,plain,
% 23.73/3.50      ( r1_tarski(X0,X1)
% 23.73/3.50      | ~ r1_tarski(X0,k1_relat_1(sK4))
% 23.73/3.50      | ~ r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1)) ),
% 23.73/3.50      inference(global_propositional_subsumption,
% 23.73/3.50                [status(thm)],
% 23.73/3.50                [c_397,c_37,c_36]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_6692,plain,
% 23.73/3.50      ( r1_tarski(X0,X1) = iProver_top
% 23.73/3.50      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 23.73/3.50      | r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,X1)) != iProver_top ),
% 23.73/3.50      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_24524,plain,
% 23.73/3.50      ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) = iProver_top
% 23.73/3.50      | r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),k1_relat_1(sK4)) != iProver_top ),
% 23.73/3.50      inference(superposition,[status(thm)],[c_23576,c_6692]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_1,plain,
% 23.73/3.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 23.73/3.50      inference(cnf_transformation,[],[f64]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_6715,plain,
% 23.73/3.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 23.73/3.50      | r1_tarski(X0,X1) = iProver_top ),
% 23.73/3.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_25,plain,
% 23.73/3.50      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 23.73/3.50      | r2_hidden(X0,k1_relat_1(X1))
% 23.73/3.50      | ~ v1_funct_1(X1)
% 23.73/3.50      | ~ v1_relat_1(X1) ),
% 23.73/3.50      inference(cnf_transformation,[],[f115]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_608,plain,
% 23.73/3.50      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 23.73/3.50      | r2_hidden(X0,k1_relat_1(X1))
% 23.73/3.50      | ~ v1_relat_1(X1)
% 23.73/3.50      | sK4 != X1 ),
% 23.73/3.50      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_609,plain,
% 23.73/3.50      ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
% 23.73/3.50      | r2_hidden(X0,k1_relat_1(sK4))
% 23.73/3.50      | ~ v1_relat_1(sK4) ),
% 23.73/3.50      inference(unflattening,[status(thm)],[c_608]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_613,plain,
% 23.73/3.50      ( r2_hidden(X0,k1_relat_1(sK4))
% 23.73/3.50      | ~ r2_hidden(X0,k10_relat_1(sK4,X1)) ),
% 23.73/3.50      inference(global_propositional_subsumption,
% 23.73/3.50                [status(thm)],
% 23.73/3.50                [c_609,c_37]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_614,plain,
% 23.73/3.50      ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
% 23.73/3.50      | r2_hidden(X0,k1_relat_1(sK4)) ),
% 23.73/3.50      inference(renaming,[status(thm)],[c_613]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_6687,plain,
% 23.73/3.50      ( r2_hidden(X0,k10_relat_1(sK4,X1)) != iProver_top
% 23.73/3.50      | r2_hidden(X0,k1_relat_1(sK4)) = iProver_top ),
% 23.73/3.50      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_7914,plain,
% 23.73/3.50      ( r2_hidden(sK0(k10_relat_1(sK4,X0),X1),k1_relat_1(sK4)) = iProver_top
% 23.73/3.50      | r1_tarski(k10_relat_1(sK4,X0),X1) = iProver_top ),
% 23.73/3.50      inference(superposition,[status(thm)],[c_6715,c_6687]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_0,plain,
% 23.73/3.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 23.73/3.50      inference(cnf_transformation,[],[f65]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_6716,plain,
% 23.73/3.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 23.73/3.50      | r1_tarski(X0,X1) = iProver_top ),
% 23.73/3.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_8312,plain,
% 23.73/3.50      ( r1_tarski(k10_relat_1(sK4,X0),k1_relat_1(sK4)) = iProver_top ),
% 23.73/3.50      inference(superposition,[status(thm)],[c_7914,c_6716]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_24784,plain,
% 23.73/3.50      ( r1_tarski(k10_relat_1(sK4,k9_relat_1(sK4,X0)),X0) = iProver_top ),
% 23.73/3.50      inference(forward_subsumption_resolution,
% 23.73/3.50                [status(thm)],
% 23.73/3.50                [c_24524,c_8312]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_6,plain,
% 23.73/3.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 23.73/3.50      inference(cnf_transformation,[],[f71]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_6710,plain,
% 23.73/3.50      ( X0 = X1
% 23.73/3.50      | r1_tarski(X1,X0) != iProver_top
% 23.73/3.50      | r1_tarski(X0,X1) != iProver_top ),
% 23.73/3.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_24794,plain,
% 23.73/3.50      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 23.73/3.50      | r1_tarski(X0,k10_relat_1(sK4,k9_relat_1(sK4,X0))) != iProver_top ),
% 23.73/3.50      inference(superposition,[status(thm)],[c_24784,c_6710]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_54797,plain,
% 23.73/3.50      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 23.73/3.50      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 23.73/3.50      | v1_relat_1(sK4) != iProver_top ),
% 23.73/3.50      inference(superposition,[status(thm)],[c_6699,c_24794]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_38,plain,
% 23.73/3.50      ( v1_relat_1(sK4) = iProver_top ),
% 23.73/3.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_74419,plain,
% 23.73/3.50      ( r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 23.73/3.50      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 23.73/3.50      inference(global_propositional_subsumption,
% 23.73/3.50                [status(thm)],
% 23.73/3.50                [c_54797,c_38]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_74420,plain,
% 23.73/3.50      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 23.73/3.50      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
% 23.73/3.50      inference(renaming,[status(thm)],[c_74419]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_74430,plain,
% 23.73/3.50      ( k10_relat_1(sK4,k9_relat_1(sK4,sK3)) = sK3 ),
% 23.73/3.50      inference(superposition,[status(thm)],[c_6698,c_74420]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(c_33,negated_conjecture,
% 23.73/3.50      ( k10_relat_1(sK4,k9_relat_1(sK4,sK3)) != sK3 ),
% 23.73/3.50      inference(cnf_transformation,[],[f104]) ).
% 23.73/3.50  
% 23.73/3.50  cnf(contradiction,plain,
% 23.73/3.50      ( $false ),
% 23.73/3.50      inference(minisat,[status(thm)],[c_74430,c_33]) ).
% 23.73/3.50  
% 23.73/3.50  
% 23.73/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.73/3.50  
% 23.73/3.50  ------                               Statistics
% 23.73/3.50  
% 23.73/3.50  ------ Selected
% 23.73/3.50  
% 23.73/3.50  total_time:                             2.991
% 23.73/3.50  
%------------------------------------------------------------------------------
