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
% DateTime   : Thu Dec  3 11:52:58 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 355 expanded)
%              Number of clauses        :   67 ( 103 expanded)
%              Number of leaves         :   22 (  94 expanded)
%              Depth                    :   18
%              Number of atoms          :  435 (1820 expanded)
%              Number of equality atoms :  166 ( 408 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k1_relat_1(X1)
              & v5_funct_1(X0,X1) )
           => v2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k1_relat_1(X0) = k1_relat_1(X1)
                & v5_funct_1(X0,X1) )
             => v2_relat_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ~ v2_relat_1(sK3)
        & k1_relat_1(sK3) = k1_relat_1(X0)
        & v5_funct_1(X0,sK3)
        & v1_funct_1(sK3)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_relat_1(X1)
            & k1_relat_1(X0) = k1_relat_1(X1)
            & v5_funct_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(sK2) = k1_relat_1(X1)
          & v5_funct_1(sK2,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ v2_relat_1(sK3)
    & k1_relat_1(sK2) = k1_relat_1(sK3)
    & v5_funct_1(sK2,sK3)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f38,f37])).

fof(f64,plain,(
    k1_relat_1(sK2) = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_relat_1(X0)
      <=> ! [X1] :
            ~ ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ? [X1] :
              ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X1))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ? [X1] :
              ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X2] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X2))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(k1_funct_1(X0,X1))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( v1_xboole_0(k1_funct_1(X0,sK0(X0)))
        & r2_hidden(sK0(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ( v1_xboole_0(k1_funct_1(X0,sK0(X0)))
            & r2_hidden(sK0(X0),k1_relat_1(X0)) ) )
        & ( ! [X2] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X2))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f52,plain,(
    ! [X0] :
      ( v2_relat_1(X0)
      | v1_xboole_0(k1_funct_1(X0,sK0(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ~ v2_relat_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
      | ~ r2_hidden(X3,k1_relat_1(X1))
      | ~ v5_funct_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f42,f41,f43,f43])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_xboole_0(k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0)),k2_enumset1(k1_funct_1(X2,X1),k1_funct_1(X2,X1),k1_funct_1(X2,X1),k1_funct_1(X2,X1))),k3_xboole_0(k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0)),k2_enumset1(k1_funct_1(X2,X1),k1_funct_1(X2,X1),k1_funct_1(X2,X1),k1_funct_1(X2,X1)))) = k9_relat_1(X2,k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f58,f66,f66])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f44,f41,f43])).

fof(f51,plain,(
    ! [X0] :
      ( v2_relat_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    v5_funct_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,negated_conjecture,
    ( k1_relat_1(sK2) = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1117,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | v2_relat_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k1_funct_1(X0,sK0(X0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1127,plain,
    ( v1_funct_1(X0) != iProver_top
    | v2_relat_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(k1_funct_1(X0,sK0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1130,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2181,plain,
    ( k1_funct_1(X0,sK0(X0)) = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v2_relat_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1130])).

cnf(c_4360,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_xboole_0
    | v2_relat_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_2181])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,negated_conjecture,
    ( ~ v2_relat_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_28,plain,
    ( v2_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4566,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4360,c_25,c_28])).

cnf(c_12,plain,
    ( ~ v5_funct_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),k1_funct_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1122,plain,
    ( v5_funct_1(X0,X1) != iProver_top
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,X2),k1_funct_1(X1,X2)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4595,plain,
    ( v5_funct_1(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(X0,sK0(sK3)),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4566,c_1122])).

cnf(c_26,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4825,plain,
    ( v1_relat_1(X0) != iProver_top
    | v5_funct_1(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(X0,sK0(sK3)),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4595,c_25,c_26])).

cnf(c_4826,plain,
    ( v5_funct_1(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(X0,sK0(sK3)),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4825])).

cnf(c_6,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k5_xboole_0(k5_xboole_0(k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2)),k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))),k3_xboole_0(k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2)),k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)))) = k9_relat_1(X1,k5_xboole_0(k5_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X0,X0,X0,X0)),k3_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1120,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)),k2_enumset1(k1_funct_1(X0,X2),k1_funct_1(X0,X2),k1_funct_1(X0,X2),k1_funct_1(X0,X2))),k3_xboole_0(k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)),k2_enumset1(k1_funct_1(X0,X2),k1_funct_1(X0,X2),k1_funct_1(X0,X2),k1_funct_1(X0,X2)))) = k9_relat_1(X0,k5_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1584,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)),k2_enumset1(k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1))),k3_xboole_0(k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)),k2_enumset1(k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1)))) = k9_relat_1(k1_xboole_0,k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))))
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1120])).

cnf(c_1585,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)),k2_enumset1(k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1))),k3_xboole_0(k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)),k2_enumset1(k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1)))) = k9_relat_1(k1_xboole_0,k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))))
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1584,c_6])).

cnf(c_760,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_791,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_760])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1288,plain,
    ( ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1294,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1295,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1294])).

cnf(c_1297,plain,
    ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1304,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1305,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1304])).

cnf(c_1307,plain,
    ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_767,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1425,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k7_relat_1(sK3,X1))
    | X0 != k7_relat_1(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_1436,plain,
    ( X0 != k7_relat_1(sK3,X1)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1425])).

cnf(c_1438,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0)
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_773,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1457,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k7_relat_1(sK3,X1))
    | X0 != k7_relat_1(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_1463,plain,
    ( X0 != k7_relat_1(sK3,X1)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(k7_relat_1(sK3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1457])).

cnf(c_1465,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0)
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1463])).

cnf(c_761,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1806,plain,
    ( X0 != X1
    | X0 = k7_relat_1(sK3,X2)
    | k7_relat_1(sK3,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_1807,plain,
    ( k7_relat_1(sK3,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1806])).

cnf(c_3464,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)),k2_enumset1(k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1))),k3_xboole_0(k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)),k2_enumset1(k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1)))) = k9_relat_1(k1_xboole_0,k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))))
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1585,c_20,c_25,c_26,c_791,c_1288,c_1297,c_1307,c_1438,c_1465,c_1807])).

cnf(c_4,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3470,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)),k2_enumset1(k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1))),k3_xboole_0(k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)),k2_enumset1(k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1)))) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3464,c_4])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3474,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3470,c_1])).

cnf(c_4837,plain,
    ( v5_funct_1(X0,sK3) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4826,c_3474])).

cnf(c_4845,plain,
    ( v5_funct_1(X0,sK3) != iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4837,c_4826])).

cnf(c_7373,plain,
    ( v5_funct_1(sK2,sK3) != iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_4845])).

cnf(c_8,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_relat_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_312,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_313,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_314,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_18,negated_conjecture,
    ( v5_funct_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,plain,
    ( v5_funct_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7373,c_314,c_27,c_26,c_25,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:49:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.18/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/0.99  
% 3.18/0.99  ------  iProver source info
% 3.18/0.99  
% 3.18/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.18/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/0.99  git: non_committed_changes: false
% 3.18/0.99  git: last_make_outside_of_git: false
% 3.18/0.99  
% 3.18/0.99  ------ 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options
% 3.18/0.99  
% 3.18/0.99  --out_options                           all
% 3.18/0.99  --tptp_safe_out                         true
% 3.18/0.99  --problem_path                          ""
% 3.18/0.99  --include_path                          ""
% 3.18/0.99  --clausifier                            res/vclausify_rel
% 3.18/0.99  --clausifier_options                    --mode clausify
% 3.18/0.99  --stdin                                 false
% 3.18/0.99  --stats_out                             all
% 3.18/0.99  
% 3.18/0.99  ------ General Options
% 3.18/0.99  
% 3.18/0.99  --fof                                   false
% 3.18/0.99  --time_out_real                         305.
% 3.18/0.99  --time_out_virtual                      -1.
% 3.18/0.99  --symbol_type_check                     false
% 3.18/0.99  --clausify_out                          false
% 3.18/0.99  --sig_cnt_out                           false
% 3.18/0.99  --trig_cnt_out                          false
% 3.18/0.99  --trig_cnt_out_tolerance                1.
% 3.18/0.99  --trig_cnt_out_sk_spl                   false
% 3.18/0.99  --abstr_cl_out                          false
% 3.18/0.99  
% 3.18/0.99  ------ Global Options
% 3.18/0.99  
% 3.18/0.99  --schedule                              default
% 3.18/0.99  --add_important_lit                     false
% 3.18/0.99  --prop_solver_per_cl                    1000
% 3.18/0.99  --min_unsat_core                        false
% 3.18/0.99  --soft_assumptions                      false
% 3.18/0.99  --soft_lemma_size                       3
% 3.18/0.99  --prop_impl_unit_size                   0
% 3.18/0.99  --prop_impl_unit                        []
% 3.18/0.99  --share_sel_clauses                     true
% 3.18/0.99  --reset_solvers                         false
% 3.18/0.99  --bc_imp_inh                            [conj_cone]
% 3.18/0.99  --conj_cone_tolerance                   3.
% 3.18/0.99  --extra_neg_conj                        none
% 3.18/0.99  --large_theory_mode                     true
% 3.18/0.99  --prolific_symb_bound                   200
% 3.18/0.99  --lt_threshold                          2000
% 3.18/0.99  --clause_weak_htbl                      true
% 3.18/0.99  --gc_record_bc_elim                     false
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing Options
% 3.18/0.99  
% 3.18/0.99  --preprocessing_flag                    true
% 3.18/0.99  --time_out_prep_mult                    0.1
% 3.18/0.99  --splitting_mode                        input
% 3.18/0.99  --splitting_grd                         true
% 3.18/0.99  --splitting_cvd                         false
% 3.18/0.99  --splitting_cvd_svl                     false
% 3.18/0.99  --splitting_nvd                         32
% 3.18/0.99  --sub_typing                            true
% 3.18/0.99  --prep_gs_sim                           true
% 3.18/0.99  --prep_unflatten                        true
% 3.18/0.99  --prep_res_sim                          true
% 3.18/0.99  --prep_upred                            true
% 3.18/0.99  --prep_sem_filter                       exhaustive
% 3.18/0.99  --prep_sem_filter_out                   false
% 3.18/0.99  --pred_elim                             true
% 3.18/0.99  --res_sim_input                         true
% 3.18/0.99  --eq_ax_congr_red                       true
% 3.18/0.99  --pure_diseq_elim                       true
% 3.18/0.99  --brand_transform                       false
% 3.18/0.99  --non_eq_to_eq                          false
% 3.18/0.99  --prep_def_merge                        true
% 3.18/0.99  --prep_def_merge_prop_impl              false
% 3.18/0.99  --prep_def_merge_mbd                    true
% 3.18/0.99  --prep_def_merge_tr_red                 false
% 3.18/0.99  --prep_def_merge_tr_cl                  false
% 3.18/0.99  --smt_preprocessing                     true
% 3.18/0.99  --smt_ac_axioms                         fast
% 3.18/0.99  --preprocessed_out                      false
% 3.18/0.99  --preprocessed_stats                    false
% 3.18/0.99  
% 3.18/0.99  ------ Abstraction refinement Options
% 3.18/0.99  
% 3.18/0.99  --abstr_ref                             []
% 3.18/0.99  --abstr_ref_prep                        false
% 3.18/0.99  --abstr_ref_until_sat                   false
% 3.18/0.99  --abstr_ref_sig_restrict                funpre
% 3.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.99  --abstr_ref_under                       []
% 3.18/0.99  
% 3.18/0.99  ------ SAT Options
% 3.18/0.99  
% 3.18/0.99  --sat_mode                              false
% 3.18/0.99  --sat_fm_restart_options                ""
% 3.18/0.99  --sat_gr_def                            false
% 3.18/0.99  --sat_epr_types                         true
% 3.18/0.99  --sat_non_cyclic_types                  false
% 3.18/0.99  --sat_finite_models                     false
% 3.18/0.99  --sat_fm_lemmas                         false
% 3.18/0.99  --sat_fm_prep                           false
% 3.18/0.99  --sat_fm_uc_incr                        true
% 3.18/0.99  --sat_out_model                         small
% 3.18/0.99  --sat_out_clauses                       false
% 3.18/0.99  
% 3.18/0.99  ------ QBF Options
% 3.18/0.99  
% 3.18/0.99  --qbf_mode                              false
% 3.18/0.99  --qbf_elim_univ                         false
% 3.18/0.99  --qbf_dom_inst                          none
% 3.18/0.99  --qbf_dom_pre_inst                      false
% 3.18/0.99  --qbf_sk_in                             false
% 3.18/0.99  --qbf_pred_elim                         true
% 3.18/0.99  --qbf_split                             512
% 3.18/0.99  
% 3.18/0.99  ------ BMC1 Options
% 3.18/0.99  
% 3.18/0.99  --bmc1_incremental                      false
% 3.18/0.99  --bmc1_axioms                           reachable_all
% 3.18/0.99  --bmc1_min_bound                        0
% 3.18/0.99  --bmc1_max_bound                        -1
% 3.18/0.99  --bmc1_max_bound_default                -1
% 3.18/0.99  --bmc1_symbol_reachability              true
% 3.18/0.99  --bmc1_property_lemmas                  false
% 3.18/0.99  --bmc1_k_induction                      false
% 3.18/0.99  --bmc1_non_equiv_states                 false
% 3.18/0.99  --bmc1_deadlock                         false
% 3.18/0.99  --bmc1_ucm                              false
% 3.18/0.99  --bmc1_add_unsat_core                   none
% 3.18/0.99  --bmc1_unsat_core_children              false
% 3.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.99  --bmc1_out_stat                         full
% 3.18/0.99  --bmc1_ground_init                      false
% 3.18/0.99  --bmc1_pre_inst_next_state              false
% 3.18/0.99  --bmc1_pre_inst_state                   false
% 3.18/0.99  --bmc1_pre_inst_reach_state             false
% 3.18/0.99  --bmc1_out_unsat_core                   false
% 3.18/0.99  --bmc1_aig_witness_out                  false
% 3.18/0.99  --bmc1_verbose                          false
% 3.18/0.99  --bmc1_dump_clauses_tptp                false
% 3.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.99  --bmc1_dump_file                        -
% 3.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.99  --bmc1_ucm_extend_mode                  1
% 3.18/0.99  --bmc1_ucm_init_mode                    2
% 3.18/0.99  --bmc1_ucm_cone_mode                    none
% 3.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.99  --bmc1_ucm_relax_model                  4
% 3.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.99  --bmc1_ucm_layered_model                none
% 3.18/0.99  --bmc1_ucm_max_lemma_size               10
% 3.18/0.99  
% 3.18/0.99  ------ AIG Options
% 3.18/0.99  
% 3.18/0.99  --aig_mode                              false
% 3.18/0.99  
% 3.18/0.99  ------ Instantiation Options
% 3.18/0.99  
% 3.18/0.99  --instantiation_flag                    true
% 3.18/0.99  --inst_sos_flag                         false
% 3.18/0.99  --inst_sos_phase                        true
% 3.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel_side                     num_symb
% 3.18/0.99  --inst_solver_per_active                1400
% 3.18/0.99  --inst_solver_calls_frac                1.
% 3.18/0.99  --inst_passive_queue_type               priority_queues
% 3.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.99  --inst_passive_queues_freq              [25;2]
% 3.18/0.99  --inst_dismatching                      true
% 3.18/0.99  --inst_eager_unprocessed_to_passive     true
% 3.18/0.99  --inst_prop_sim_given                   true
% 3.18/0.99  --inst_prop_sim_new                     false
% 3.18/0.99  --inst_subs_new                         false
% 3.18/0.99  --inst_eq_res_simp                      false
% 3.18/0.99  --inst_subs_given                       false
% 3.18/0.99  --inst_orphan_elimination               true
% 3.18/0.99  --inst_learning_loop_flag               true
% 3.18/0.99  --inst_learning_start                   3000
% 3.18/0.99  --inst_learning_factor                  2
% 3.18/0.99  --inst_start_prop_sim_after_learn       3
% 3.18/0.99  --inst_sel_renew                        solver
% 3.18/0.99  --inst_lit_activity_flag                true
% 3.18/0.99  --inst_restr_to_given                   false
% 3.18/0.99  --inst_activity_threshold               500
% 3.18/0.99  --inst_out_proof                        true
% 3.18/0.99  
% 3.18/0.99  ------ Resolution Options
% 3.18/0.99  
% 3.18/0.99  --resolution_flag                       true
% 3.18/0.99  --res_lit_sel                           adaptive
% 3.18/0.99  --res_lit_sel_side                      none
% 3.18/0.99  --res_ordering                          kbo
% 3.18/0.99  --res_to_prop_solver                    active
% 3.18/0.99  --res_prop_simpl_new                    false
% 3.18/0.99  --res_prop_simpl_given                  true
% 3.18/0.99  --res_passive_queue_type                priority_queues
% 3.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.99  --res_passive_queues_freq               [15;5]
% 3.18/0.99  --res_forward_subs                      full
% 3.18/0.99  --res_backward_subs                     full
% 3.18/0.99  --res_forward_subs_resolution           true
% 3.18/0.99  --res_backward_subs_resolution          true
% 3.18/0.99  --res_orphan_elimination                true
% 3.18/0.99  --res_time_limit                        2.
% 3.18/0.99  --res_out_proof                         true
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Options
% 3.18/0.99  
% 3.18/0.99  --superposition_flag                    true
% 3.18/0.99  --sup_passive_queue_type                priority_queues
% 3.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.18/0.99  --demod_completeness_check              fast
% 3.18/0.99  --demod_use_ground                      true
% 3.18/0.99  --sup_to_prop_solver                    passive
% 3.18/0.99  --sup_prop_simpl_new                    true
% 3.18/0.99  --sup_prop_simpl_given                  true
% 3.18/0.99  --sup_fun_splitting                     false
% 3.18/0.99  --sup_smt_interval                      50000
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Simplification Setup
% 3.18/0.99  
% 3.18/0.99  --sup_indices_passive                   []
% 3.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_full_bw                           [BwDemod]
% 3.18/0.99  --sup_immed_triv                        [TrivRules]
% 3.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_immed_bw_main                     []
% 3.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  
% 3.18/0.99  ------ Combination Options
% 3.18/0.99  
% 3.18/0.99  --comb_res_mult                         3
% 3.18/0.99  --comb_sup_mult                         2
% 3.18/0.99  --comb_inst_mult                        10
% 3.18/0.99  
% 3.18/0.99  ------ Debug Options
% 3.18/0.99  
% 3.18/0.99  --dbg_backtrace                         false
% 3.18/0.99  --dbg_dump_prop_clauses                 false
% 3.18/0.99  --dbg_dump_prop_clauses_file            -
% 3.18/0.99  --dbg_out_stat                          false
% 3.18/0.99  ------ Parsing...
% 3.18/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.18/0.99  ------ Proving...
% 3.18/0.99  ------ Problem Properties 
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  clauses                                 22
% 3.18/0.99  conjectures                             7
% 3.18/0.99  EPR                                     7
% 3.18/0.99  Horn                                    19
% 3.18/0.99  unary                                   11
% 3.18/0.99  binary                                  3
% 3.18/0.99  lits                                    57
% 3.18/0.99  lits eq                                 8
% 3.18/0.99  fd_pure                                 0
% 3.18/0.99  fd_pseudo                               0
% 3.18/0.99  fd_cond                                 1
% 3.18/0.99  fd_pseudo_cond                          0
% 3.18/0.99  AC symbols                              0
% 3.18/0.99  
% 3.18/0.99  ------ Schedule dynamic 5 is on 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  ------ 
% 3.18/0.99  Current options:
% 3.18/0.99  ------ 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options
% 3.18/0.99  
% 3.18/0.99  --out_options                           all
% 3.18/0.99  --tptp_safe_out                         true
% 3.18/0.99  --problem_path                          ""
% 3.18/0.99  --include_path                          ""
% 3.18/0.99  --clausifier                            res/vclausify_rel
% 3.18/0.99  --clausifier_options                    --mode clausify
% 3.18/0.99  --stdin                                 false
% 3.18/0.99  --stats_out                             all
% 3.18/0.99  
% 3.18/0.99  ------ General Options
% 3.18/0.99  
% 3.18/0.99  --fof                                   false
% 3.18/0.99  --time_out_real                         305.
% 3.18/0.99  --time_out_virtual                      -1.
% 3.18/0.99  --symbol_type_check                     false
% 3.18/0.99  --clausify_out                          false
% 3.18/0.99  --sig_cnt_out                           false
% 3.18/0.99  --trig_cnt_out                          false
% 3.18/0.99  --trig_cnt_out_tolerance                1.
% 3.18/0.99  --trig_cnt_out_sk_spl                   false
% 3.18/0.99  --abstr_cl_out                          false
% 3.18/0.99  
% 3.18/0.99  ------ Global Options
% 3.18/0.99  
% 3.18/0.99  --schedule                              default
% 3.18/0.99  --add_important_lit                     false
% 3.18/0.99  --prop_solver_per_cl                    1000
% 3.18/0.99  --min_unsat_core                        false
% 3.18/0.99  --soft_assumptions                      false
% 3.18/0.99  --soft_lemma_size                       3
% 3.18/0.99  --prop_impl_unit_size                   0
% 3.18/0.99  --prop_impl_unit                        []
% 3.18/0.99  --share_sel_clauses                     true
% 3.18/0.99  --reset_solvers                         false
% 3.18/0.99  --bc_imp_inh                            [conj_cone]
% 3.18/0.99  --conj_cone_tolerance                   3.
% 3.18/0.99  --extra_neg_conj                        none
% 3.18/0.99  --large_theory_mode                     true
% 3.18/0.99  --prolific_symb_bound                   200
% 3.18/0.99  --lt_threshold                          2000
% 3.18/0.99  --clause_weak_htbl                      true
% 3.18/0.99  --gc_record_bc_elim                     false
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing Options
% 3.18/0.99  
% 3.18/0.99  --preprocessing_flag                    true
% 3.18/0.99  --time_out_prep_mult                    0.1
% 3.18/0.99  --splitting_mode                        input
% 3.18/0.99  --splitting_grd                         true
% 3.18/0.99  --splitting_cvd                         false
% 3.18/0.99  --splitting_cvd_svl                     false
% 3.18/0.99  --splitting_nvd                         32
% 3.18/0.99  --sub_typing                            true
% 3.18/0.99  --prep_gs_sim                           true
% 3.18/0.99  --prep_unflatten                        true
% 3.18/0.99  --prep_res_sim                          true
% 3.18/0.99  --prep_upred                            true
% 3.18/0.99  --prep_sem_filter                       exhaustive
% 3.18/0.99  --prep_sem_filter_out                   false
% 3.18/0.99  --pred_elim                             true
% 3.18/0.99  --res_sim_input                         true
% 3.18/0.99  --eq_ax_congr_red                       true
% 3.18/0.99  --pure_diseq_elim                       true
% 3.18/0.99  --brand_transform                       false
% 3.18/0.99  --non_eq_to_eq                          false
% 3.18/0.99  --prep_def_merge                        true
% 3.18/0.99  --prep_def_merge_prop_impl              false
% 3.18/0.99  --prep_def_merge_mbd                    true
% 3.18/0.99  --prep_def_merge_tr_red                 false
% 3.18/0.99  --prep_def_merge_tr_cl                  false
% 3.18/0.99  --smt_preprocessing                     true
% 3.18/0.99  --smt_ac_axioms                         fast
% 3.18/0.99  --preprocessed_out                      false
% 3.18/0.99  --preprocessed_stats                    false
% 3.18/0.99  
% 3.18/0.99  ------ Abstraction refinement Options
% 3.18/0.99  
% 3.18/0.99  --abstr_ref                             []
% 3.18/0.99  --abstr_ref_prep                        false
% 3.18/0.99  --abstr_ref_until_sat                   false
% 3.18/0.99  --abstr_ref_sig_restrict                funpre
% 3.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.99  --abstr_ref_under                       []
% 3.18/0.99  
% 3.18/0.99  ------ SAT Options
% 3.18/0.99  
% 3.18/0.99  --sat_mode                              false
% 3.18/0.99  --sat_fm_restart_options                ""
% 3.18/0.99  --sat_gr_def                            false
% 3.18/0.99  --sat_epr_types                         true
% 3.18/0.99  --sat_non_cyclic_types                  false
% 3.18/0.99  --sat_finite_models                     false
% 3.18/0.99  --sat_fm_lemmas                         false
% 3.18/0.99  --sat_fm_prep                           false
% 3.18/0.99  --sat_fm_uc_incr                        true
% 3.18/0.99  --sat_out_model                         small
% 3.18/0.99  --sat_out_clauses                       false
% 3.18/0.99  
% 3.18/0.99  ------ QBF Options
% 3.18/0.99  
% 3.18/0.99  --qbf_mode                              false
% 3.18/0.99  --qbf_elim_univ                         false
% 3.18/0.99  --qbf_dom_inst                          none
% 3.18/0.99  --qbf_dom_pre_inst                      false
% 3.18/0.99  --qbf_sk_in                             false
% 3.18/0.99  --qbf_pred_elim                         true
% 3.18/0.99  --qbf_split                             512
% 3.18/0.99  
% 3.18/0.99  ------ BMC1 Options
% 3.18/0.99  
% 3.18/0.99  --bmc1_incremental                      false
% 3.18/0.99  --bmc1_axioms                           reachable_all
% 3.18/0.99  --bmc1_min_bound                        0
% 3.18/0.99  --bmc1_max_bound                        -1
% 3.18/0.99  --bmc1_max_bound_default                -1
% 3.18/0.99  --bmc1_symbol_reachability              true
% 3.18/0.99  --bmc1_property_lemmas                  false
% 3.18/0.99  --bmc1_k_induction                      false
% 3.18/0.99  --bmc1_non_equiv_states                 false
% 3.18/0.99  --bmc1_deadlock                         false
% 3.18/0.99  --bmc1_ucm                              false
% 3.18/0.99  --bmc1_add_unsat_core                   none
% 3.18/0.99  --bmc1_unsat_core_children              false
% 3.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.99  --bmc1_out_stat                         full
% 3.18/0.99  --bmc1_ground_init                      false
% 3.18/0.99  --bmc1_pre_inst_next_state              false
% 3.18/0.99  --bmc1_pre_inst_state                   false
% 3.18/0.99  --bmc1_pre_inst_reach_state             false
% 3.18/0.99  --bmc1_out_unsat_core                   false
% 3.18/0.99  --bmc1_aig_witness_out                  false
% 3.18/0.99  --bmc1_verbose                          false
% 3.18/0.99  --bmc1_dump_clauses_tptp                false
% 3.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.99  --bmc1_dump_file                        -
% 3.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.99  --bmc1_ucm_extend_mode                  1
% 3.18/0.99  --bmc1_ucm_init_mode                    2
% 3.18/0.99  --bmc1_ucm_cone_mode                    none
% 3.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.99  --bmc1_ucm_relax_model                  4
% 3.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.99  --bmc1_ucm_layered_model                none
% 3.18/0.99  --bmc1_ucm_max_lemma_size               10
% 3.18/0.99  
% 3.18/0.99  ------ AIG Options
% 3.18/0.99  
% 3.18/0.99  --aig_mode                              false
% 3.18/0.99  
% 3.18/0.99  ------ Instantiation Options
% 3.18/0.99  
% 3.18/0.99  --instantiation_flag                    true
% 3.18/0.99  --inst_sos_flag                         false
% 3.18/0.99  --inst_sos_phase                        true
% 3.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel_side                     none
% 3.18/0.99  --inst_solver_per_active                1400
% 3.18/0.99  --inst_solver_calls_frac                1.
% 3.18/0.99  --inst_passive_queue_type               priority_queues
% 3.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.99  --inst_passive_queues_freq              [25;2]
% 3.18/0.99  --inst_dismatching                      true
% 3.18/0.99  --inst_eager_unprocessed_to_passive     true
% 3.18/0.99  --inst_prop_sim_given                   true
% 3.18/0.99  --inst_prop_sim_new                     false
% 3.18/0.99  --inst_subs_new                         false
% 3.18/0.99  --inst_eq_res_simp                      false
% 3.18/0.99  --inst_subs_given                       false
% 3.18/0.99  --inst_orphan_elimination               true
% 3.18/0.99  --inst_learning_loop_flag               true
% 3.18/0.99  --inst_learning_start                   3000
% 3.18/0.99  --inst_learning_factor                  2
% 3.18/0.99  --inst_start_prop_sim_after_learn       3
% 3.18/0.99  --inst_sel_renew                        solver
% 3.18/0.99  --inst_lit_activity_flag                true
% 3.18/0.99  --inst_restr_to_given                   false
% 3.18/0.99  --inst_activity_threshold               500
% 3.18/0.99  --inst_out_proof                        true
% 3.18/0.99  
% 3.18/0.99  ------ Resolution Options
% 3.18/0.99  
% 3.18/0.99  --resolution_flag                       false
% 3.18/0.99  --res_lit_sel                           adaptive
% 3.18/0.99  --res_lit_sel_side                      none
% 3.18/0.99  --res_ordering                          kbo
% 3.18/0.99  --res_to_prop_solver                    active
% 3.18/0.99  --res_prop_simpl_new                    false
% 3.18/0.99  --res_prop_simpl_given                  true
% 3.18/0.99  --res_passive_queue_type                priority_queues
% 3.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.99  --res_passive_queues_freq               [15;5]
% 3.18/0.99  --res_forward_subs                      full
% 3.18/0.99  --res_backward_subs                     full
% 3.18/0.99  --res_forward_subs_resolution           true
% 3.18/0.99  --res_backward_subs_resolution          true
% 3.18/0.99  --res_orphan_elimination                true
% 3.18/0.99  --res_time_limit                        2.
% 3.18/0.99  --res_out_proof                         true
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Options
% 3.18/0.99  
% 3.18/0.99  --superposition_flag                    true
% 3.18/0.99  --sup_passive_queue_type                priority_queues
% 3.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.18/0.99  --demod_completeness_check              fast
% 3.18/0.99  --demod_use_ground                      true
% 3.18/0.99  --sup_to_prop_solver                    passive
% 3.18/0.99  --sup_prop_simpl_new                    true
% 3.18/0.99  --sup_prop_simpl_given                  true
% 3.18/0.99  --sup_fun_splitting                     false
% 3.18/0.99  --sup_smt_interval                      50000
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Simplification Setup
% 3.18/0.99  
% 3.18/0.99  --sup_indices_passive                   []
% 3.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_full_bw                           [BwDemod]
% 3.18/0.99  --sup_immed_triv                        [TrivRules]
% 3.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_immed_bw_main                     []
% 3.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  
% 3.18/0.99  ------ Combination Options
% 3.18/0.99  
% 3.18/0.99  --comb_res_mult                         3
% 3.18/0.99  --comb_sup_mult                         2
% 3.18/0.99  --comb_inst_mult                        10
% 3.18/0.99  
% 3.18/0.99  ------ Debug Options
% 3.18/0.99  
% 3.18/0.99  --dbg_backtrace                         false
% 3.18/0.99  --dbg_dump_prop_clauses                 false
% 3.18/0.99  --dbg_dump_prop_clauses_file            -
% 3.18/0.99  --dbg_out_stat                          false
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  ------ Proving...
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  % SZS status Theorem for theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  fof(f14,conjecture,(
% 3.18/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1)) => v2_relat_1(X1))))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f15,negated_conjecture,(
% 3.18/0.99    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1)) => v2_relat_1(X1))))),
% 3.18/0.99    inference(negated_conjecture,[],[f14])).
% 3.18/0.99  
% 3.18/0.99  fof(f27,plain,(
% 3.18/0.99    ? [X0] : (? [X1] : ((~v2_relat_1(X1) & (k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.18/0.99    inference(ennf_transformation,[],[f15])).
% 3.18/0.99  
% 3.18/0.99  fof(f28,plain,(
% 3.18/0.99    ? [X0] : (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.18/0.99    inference(flattening,[],[f27])).
% 3.18/0.99  
% 3.18/0.99  fof(f38,plain,(
% 3.18/0.99    ( ! [X0] : (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~v2_relat_1(sK3) & k1_relat_1(sK3) = k1_relat_1(X0) & v5_funct_1(X0,sK3) & v1_funct_1(sK3) & v1_relat_1(sK3))) )),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f37,plain,(
% 3.18/0.99    ? [X0] : (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (~v2_relat_1(X1) & k1_relat_1(sK2) = k1_relat_1(X1) & v5_funct_1(sK2,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f39,plain,(
% 3.18/0.99    (~v2_relat_1(sK3) & k1_relat_1(sK2) = k1_relat_1(sK3) & v5_funct_1(sK2,sK3) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.18/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f38,f37])).
% 3.18/0.99  
% 3.18/0.99  fof(f64,plain,(
% 3.18/0.99    k1_relat_1(sK2) = k1_relat_1(sK3)),
% 3.18/0.99    inference(cnf_transformation,[],[f39])).
% 3.18/0.99  
% 3.18/0.99  fof(f62,plain,(
% 3.18/0.99    v1_funct_1(sK3)),
% 3.18/0.99    inference(cnf_transformation,[],[f39])).
% 3.18/0.99  
% 3.18/0.99  fof(f10,axiom,(
% 3.18/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_relat_1(X0) <=> ! [X1] : ~(v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f19,plain,(
% 3.18/0.99    ! [X0] : ((v2_relat_1(X0) <=> ! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.18/0.99    inference(ennf_transformation,[],[f10])).
% 3.18/0.99  
% 3.18/0.99  fof(f20,plain,(
% 3.18/0.99    ! [X0] : ((v2_relat_1(X0) <=> ! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/0.99    inference(flattening,[],[f19])).
% 3.18/0.99  
% 3.18/0.99  fof(f29,plain,(
% 3.18/0.99    ! [X0] : (((v2_relat_1(X0) | ? [X1] : (v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/0.99    inference(nnf_transformation,[],[f20])).
% 3.18/0.99  
% 3.18/0.99  fof(f30,plain,(
% 3.18/0.99    ! [X0] : (((v2_relat_1(X0) | ? [X1] : (v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X2] : (~v1_xboole_0(k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X0))) | ~v2_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/0.99    inference(rectify,[],[f29])).
% 3.18/0.99  
% 3.18/0.99  fof(f31,plain,(
% 3.18/0.99    ! [X0] : (? [X1] : (v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0))) => (v1_xboole_0(k1_funct_1(X0,sK0(X0))) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f32,plain,(
% 3.18/0.99    ! [X0] : (((v2_relat_1(X0) | (v1_xboole_0(k1_funct_1(X0,sK0(X0))) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X2] : (~v1_xboole_0(k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X0))) | ~v2_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.18/0.99  
% 3.18/0.99  fof(f52,plain,(
% 3.18/0.99    ( ! [X0] : (v2_relat_1(X0) | v1_xboole_0(k1_funct_1(X0,sK0(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f32])).
% 3.18/0.99  
% 3.18/0.99  fof(f1,axiom,(
% 3.18/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f16,plain,(
% 3.18/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f1])).
% 3.18/0.99  
% 3.18/0.99  fof(f40,plain,(
% 3.18/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f16])).
% 3.18/0.99  
% 3.18/0.99  fof(f61,plain,(
% 3.18/0.99    v1_relat_1(sK3)),
% 3.18/0.99    inference(cnf_transformation,[],[f39])).
% 3.18/0.99  
% 3.18/0.99  fof(f65,plain,(
% 3.18/0.99    ~v2_relat_1(sK3)),
% 3.18/0.99    inference(cnf_transformation,[],[f39])).
% 3.18/0.99  
% 3.18/0.99  fof(f11,axiom,(
% 3.18/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f21,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.18/0.99    inference(ennf_transformation,[],[f11])).
% 3.18/0.99  
% 3.18/0.99  fof(f22,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/0.99    inference(flattening,[],[f21])).
% 3.18/0.99  
% 3.18/0.99  fof(f33,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/0.99    inference(nnf_transformation,[],[f22])).
% 3.18/0.99  
% 3.18/0.99  fof(f34,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/0.99    inference(rectify,[],[f33])).
% 3.18/0.99  
% 3.18/0.99  fof(f35,plain,(
% 3.18/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1))))),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f36,plain,(
% 3.18/0.99    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 3.18/0.99  
% 3.18/0.99  fof(f53,plain,(
% 3.18/0.99    ( ! [X0,X3,X1] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~v5_funct_1(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f36])).
% 3.18/0.99  
% 3.18/0.99  fof(f9,axiom,(
% 3.18/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f48,plain,(
% 3.18/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.18/0.99    inference(cnf_transformation,[],[f9])).
% 3.18/0.99  
% 3.18/0.99  fof(f13,axiom,(
% 3.18/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f25,plain,(
% 3.18/0.99    ! [X0,X1,X2] : ((k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.18/0.99    inference(ennf_transformation,[],[f13])).
% 3.18/0.99  
% 3.18/0.99  fof(f26,plain,(
% 3.18/0.99    ! [X0,X1,X2] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.18/0.99    inference(flattening,[],[f25])).
% 3.18/0.99  
% 3.18/0.99  fof(f58,plain,(
% 3.18/0.99    ( ! [X2,X0,X1] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f26])).
% 3.18/0.99  
% 3.18/0.99  fof(f3,axiom,(
% 3.18/0.99    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f42,plain,(
% 3.18/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f3])).
% 3.18/0.99  
% 3.18/0.99  fof(f2,axiom,(
% 3.18/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f41,plain,(
% 3.18/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 3.18/0.99    inference(cnf_transformation,[],[f2])).
% 3.18/0.99  
% 3.18/0.99  fof(f4,axiom,(
% 3.18/0.99    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f43,plain,(
% 3.18/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f4])).
% 3.18/0.99  
% 3.18/0.99  fof(f66,plain,(
% 3.18/0.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) = k2_tarski(X0,X1)) )),
% 3.18/0.99    inference(definition_unfolding,[],[f42,f41,f43,f43])).
% 3.18/0.99  
% 3.18/0.99  fof(f68,plain,(
% 3.18/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0)),k2_enumset1(k1_funct_1(X2,X1),k1_funct_1(X2,X1),k1_funct_1(X2,X1),k1_funct_1(X2,X1))),k3_xboole_0(k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0)),k2_enumset1(k1_funct_1(X2,X1),k1_funct_1(X2,X1),k1_funct_1(X2,X1),k1_funct_1(X2,X1)))) = k9_relat_1(X2,k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.18/0.99    inference(definition_unfolding,[],[f58,f66,f66])).
% 3.18/0.99  
% 3.18/0.99  fof(f7,axiom,(
% 3.18/0.99    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f18,plain,(
% 3.18/0.99    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f7])).
% 3.18/0.99  
% 3.18/0.99  fof(f46,plain,(
% 3.18/0.99    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f18])).
% 3.18/0.99  
% 3.18/0.99  fof(f6,axiom,(
% 3.18/0.99    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f17,plain,(
% 3.18/0.99    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.18/0.99    inference(ennf_transformation,[],[f6])).
% 3.18/0.99  
% 3.18/0.99  fof(f45,plain,(
% 3.18/0.99    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f17])).
% 3.18/0.99  
% 3.18/0.99  fof(f12,axiom,(
% 3.18/0.99    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f23,plain,(
% 3.18/0.99    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.18/0.99    inference(ennf_transformation,[],[f12])).
% 3.18/0.99  
% 3.18/0.99  fof(f24,plain,(
% 3.18/0.99    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/0.99    inference(flattening,[],[f23])).
% 3.18/0.99  
% 3.18/0.99  fof(f57,plain,(
% 3.18/0.99    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f24])).
% 3.18/0.99  
% 3.18/0.99  fof(f8,axiom,(
% 3.18/0.99    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f47,plain,(
% 3.18/0.99    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f8])).
% 3.18/0.99  
% 3.18/0.99  fof(f5,axiom,(
% 3.18/0.99    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.18/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f44,plain,(
% 3.18/0.99    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f5])).
% 3.18/0.99  
% 3.18/0.99  fof(f67,plain,(
% 3.18/0.99    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) )),
% 3.18/0.99    inference(definition_unfolding,[],[f44,f41,f43])).
% 3.18/0.99  
% 3.18/0.99  fof(f51,plain,(
% 3.18/0.99    ( ! [X0] : (v2_relat_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f32])).
% 3.18/0.99  
% 3.18/0.99  fof(f63,plain,(
% 3.18/0.99    v5_funct_1(sK2,sK3)),
% 3.18/0.99    inference(cnf_transformation,[],[f39])).
% 3.18/0.99  
% 3.18/0.99  fof(f60,plain,(
% 3.18/0.99    v1_funct_1(sK2)),
% 3.18/0.99    inference(cnf_transformation,[],[f39])).
% 3.18/0.99  
% 3.18/0.99  fof(f59,plain,(
% 3.18/0.99    v1_relat_1(sK2)),
% 3.18/0.99    inference(cnf_transformation,[],[f39])).
% 3.18/0.99  
% 3.18/0.99  cnf(c_17,negated_conjecture,
% 3.18/0.99      ( k1_relat_1(sK2) = k1_relat_1(sK3) ),
% 3.18/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_19,negated_conjecture,
% 3.18/0.99      ( v1_funct_1(sK3) ),
% 3.18/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1117,plain,
% 3.18/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_7,plain,
% 3.18/0.99      ( ~ v1_funct_1(X0)
% 3.18/0.99      | v2_relat_1(X0)
% 3.18/0.99      | ~ v1_relat_1(X0)
% 3.18/0.99      | v1_xboole_0(k1_funct_1(X0,sK0(X0))) ),
% 3.18/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1127,plain,
% 3.18/0.99      ( v1_funct_1(X0) != iProver_top
% 3.18/0.99      | v2_relat_1(X0) = iProver_top
% 3.18/0.99      | v1_relat_1(X0) != iProver_top
% 3.18/0.99      | v1_xboole_0(k1_funct_1(X0,sK0(X0))) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_0,plain,
% 3.18/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.18/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1130,plain,
% 3.18/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2181,plain,
% 3.18/0.99      ( k1_funct_1(X0,sK0(X0)) = k1_xboole_0
% 3.18/0.99      | v1_funct_1(X0) != iProver_top
% 3.18/0.99      | v2_relat_1(X0) = iProver_top
% 3.18/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1127,c_1130]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4360,plain,
% 3.18/0.99      ( k1_funct_1(sK3,sK0(sK3)) = k1_xboole_0
% 3.18/0.99      | v2_relat_1(sK3) = iProver_top
% 3.18/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_1117,c_2181]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_20,negated_conjecture,
% 3.18/0.99      ( v1_relat_1(sK3) ),
% 3.18/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_25,plain,
% 3.18/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_16,negated_conjecture,
% 3.18/0.99      ( ~ v2_relat_1(sK3) ),
% 3.18/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_28,plain,
% 3.18/0.99      ( v2_relat_1(sK3) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4566,plain,
% 3.18/0.99      ( k1_funct_1(sK3,sK0(sK3)) = k1_xboole_0 ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_4360,c_25,c_28]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_12,plain,
% 3.18/0.99      ( ~ v5_funct_1(X0,X1)
% 3.18/0.99      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.18/0.99      | r2_hidden(k1_funct_1(X0,X2),k1_funct_1(X1,X2))
% 3.18/0.99      | ~ v1_funct_1(X1)
% 3.18/0.99      | ~ v1_funct_1(X0)
% 3.18/0.99      | ~ v1_relat_1(X1)
% 3.18/0.99      | ~ v1_relat_1(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1122,plain,
% 3.18/0.99      ( v5_funct_1(X0,X1) != iProver_top
% 3.18/0.99      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 3.18/0.99      | r2_hidden(k1_funct_1(X0,X2),k1_funct_1(X1,X2)) = iProver_top
% 3.18/0.99      | v1_funct_1(X1) != iProver_top
% 3.18/0.99      | v1_funct_1(X0) != iProver_top
% 3.18/0.99      | v1_relat_1(X1) != iProver_top
% 3.18/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4595,plain,
% 3.18/0.99      ( v5_funct_1(X0,sK3) != iProver_top
% 3.18/0.99      | r2_hidden(k1_funct_1(X0,sK0(sK3)),k1_xboole_0) = iProver_top
% 3.18/0.99      | r2_hidden(sK0(sK3),k1_relat_1(X0)) != iProver_top
% 3.18/0.99      | v1_funct_1(X0) != iProver_top
% 3.18/0.99      | v1_funct_1(sK3) != iProver_top
% 3.18/0.99      | v1_relat_1(X0) != iProver_top
% 3.18/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_4566,c_1122]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_26,plain,
% 3.18/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4825,plain,
% 3.18/0.99      ( v1_relat_1(X0) != iProver_top
% 3.18/0.99      | v5_funct_1(X0,sK3) != iProver_top
% 3.18/0.99      | r2_hidden(k1_funct_1(X0,sK0(sK3)),k1_xboole_0) = iProver_top
% 3.18/0.99      | r2_hidden(sK0(sK3),k1_relat_1(X0)) != iProver_top
% 3.18/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_4595,c_25,c_26]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4826,plain,
% 3.18/0.99      ( v5_funct_1(X0,sK3) != iProver_top
% 3.18/0.99      | r2_hidden(k1_funct_1(X0,sK0(sK3)),k1_xboole_0) = iProver_top
% 3.18/0.99      | r2_hidden(sK0(sK3),k1_relat_1(X0)) != iProver_top
% 3.18/0.99      | v1_funct_1(X0) != iProver_top
% 3.18/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.18/0.99      inference(renaming,[status(thm)],[c_4825]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6,plain,
% 3.18/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.18/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_15,plain,
% 3.18/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.18/0.99      | ~ r2_hidden(X2,k1_relat_1(X1))
% 3.18/0.99      | ~ v1_funct_1(X1)
% 3.18/0.99      | ~ v1_relat_1(X1)
% 3.18/0.99      | k5_xboole_0(k5_xboole_0(k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2)),k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))),k3_xboole_0(k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2)),k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)))) = k9_relat_1(X1,k5_xboole_0(k5_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X0,X0,X0,X0)),k3_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X0,X0,X0,X0)))) ),
% 3.18/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1120,plain,
% 3.18/0.99      ( k5_xboole_0(k5_xboole_0(k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)),k2_enumset1(k1_funct_1(X0,X2),k1_funct_1(X0,X2),k1_funct_1(X0,X2),k1_funct_1(X0,X2))),k3_xboole_0(k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)),k2_enumset1(k1_funct_1(X0,X2),k1_funct_1(X0,X2),k1_funct_1(X0,X2),k1_funct_1(X0,X2)))) = k9_relat_1(X0,k5_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))))
% 3.18/0.99      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 3.18/0.99      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.18/0.99      | v1_funct_1(X0) != iProver_top
% 3.18/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1584,plain,
% 3.18/1.00      ( k5_xboole_0(k5_xboole_0(k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)),k2_enumset1(k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1))),k3_xboole_0(k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)),k2_enumset1(k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1)))) = k9_relat_1(k1_xboole_0,k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))))
% 3.18/1.00      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 3.18/1.00      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 3.18/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.18/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_6,c_1120]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1585,plain,
% 3.18/1.00      ( k5_xboole_0(k5_xboole_0(k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)),k2_enumset1(k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1))),k3_xboole_0(k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)),k2_enumset1(k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1)))) = k9_relat_1(k1_xboole_0,k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))))
% 3.18/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.18/1.00      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 3.18/1.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.18/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_1584,c_6]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_760,plain,( X0 = X0 ),theory(equality) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_791,plain,
% 3.18/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_760]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3,plain,
% 3.18/1.00      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.18/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1288,plain,
% 3.18/1.00      ( ~ v1_relat_1(sK3) | k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2,plain,
% 3.18/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1294,plain,
% 3.18/1.00      ( v1_relat_1(k7_relat_1(sK3,X0)) | ~ v1_relat_1(sK3) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1295,plain,
% 3.18/1.00      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 3.18/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1294]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1297,plain,
% 3.18/1.00      ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
% 3.18/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_1295]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_13,plain,
% 3.18/1.00      ( ~ v1_funct_1(X0)
% 3.18/1.00      | v1_funct_1(k7_relat_1(X0,X1))
% 3.18/1.00      | ~ v1_relat_1(X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1304,plain,
% 3.18/1.00      ( v1_funct_1(k7_relat_1(sK3,X0))
% 3.18/1.00      | ~ v1_funct_1(sK3)
% 3.18/1.00      | ~ v1_relat_1(sK3) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1305,plain,
% 3.18/1.00      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
% 3.18/1.00      | v1_funct_1(sK3) != iProver_top
% 3.18/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1304]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1307,plain,
% 3.18/1.00      ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
% 3.18/1.00      | v1_funct_1(sK3) != iProver_top
% 3.18/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_1305]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_767,plain,
% 3.18/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.18/1.00      theory(equality) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1425,plain,
% 3.18/1.00      ( v1_relat_1(X0)
% 3.18/1.00      | ~ v1_relat_1(k7_relat_1(sK3,X1))
% 3.18/1.00      | X0 != k7_relat_1(sK3,X1) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_767]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1436,plain,
% 3.18/1.00      ( X0 != k7_relat_1(sK3,X1)
% 3.18/1.00      | v1_relat_1(X0) = iProver_top
% 3.18/1.00      | v1_relat_1(k7_relat_1(sK3,X1)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1425]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1438,plain,
% 3.18/1.00      ( k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0)
% 3.18/1.00      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
% 3.18/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_1436]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_773,plain,
% 3.18/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.18/1.00      theory(equality) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1457,plain,
% 3.18/1.00      ( v1_funct_1(X0)
% 3.18/1.00      | ~ v1_funct_1(k7_relat_1(sK3,X1))
% 3.18/1.00      | X0 != k7_relat_1(sK3,X1) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_773]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1463,plain,
% 3.18/1.00      ( X0 != k7_relat_1(sK3,X1)
% 3.18/1.00      | v1_funct_1(X0) = iProver_top
% 3.18/1.00      | v1_funct_1(k7_relat_1(sK3,X1)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1457]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1465,plain,
% 3.18/1.00      ( k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0)
% 3.18/1.00      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
% 3.18/1.00      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_1463]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_761,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1806,plain,
% 3.18/1.00      ( X0 != X1 | X0 = k7_relat_1(sK3,X2) | k7_relat_1(sK3,X2) != X1 ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_761]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1807,plain,
% 3.18/1.00      ( k7_relat_1(sK3,k1_xboole_0) != k1_xboole_0
% 3.18/1.00      | k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
% 3.18/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_1806]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3464,plain,
% 3.18/1.00      ( k5_xboole_0(k5_xboole_0(k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)),k2_enumset1(k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1))),k3_xboole_0(k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)),k2_enumset1(k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1)))) = k9_relat_1(k1_xboole_0,k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))))
% 3.18/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.18/1.00      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_1585,c_20,c_25,c_26,c_791,c_1288,c_1297,c_1307,c_1438,
% 3.18/1.00                 c_1465,c_1807]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4,plain,
% 3.18/1.00      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.18/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3470,plain,
% 3.18/1.00      ( k5_xboole_0(k5_xboole_0(k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)),k2_enumset1(k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1))),k3_xboole_0(k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)),k2_enumset1(k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1),k1_funct_1(k1_xboole_0,X1)))) = k1_xboole_0
% 3.18/1.00      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.18/1.00      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_3464,c_4]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1,plain,
% 3.18/1.00      ( k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) != k1_xboole_0 ),
% 3.18/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3474,plain,
% 3.18/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.18/1.00      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 3.18/1.00      inference(forward_subsumption_resolution,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_3470,c_1]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4837,plain,
% 3.18/1.00      ( v5_funct_1(X0,sK3) != iProver_top
% 3.18/1.00      | r2_hidden(X1,k1_xboole_0) != iProver_top
% 3.18/1.00      | r2_hidden(sK0(sK3),k1_relat_1(X0)) != iProver_top
% 3.18/1.00      | v1_funct_1(X0) != iProver_top
% 3.18/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_4826,c_3474]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4845,plain,
% 3.18/1.00      ( v5_funct_1(X0,sK3) != iProver_top
% 3.18/1.00      | r2_hidden(sK0(sK3),k1_relat_1(X0)) != iProver_top
% 3.18/1.00      | v1_funct_1(X0) != iProver_top
% 3.18/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.18/1.00      inference(backward_subsumption_resolution,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_4837,c_4826]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7373,plain,
% 3.18/1.00      ( v5_funct_1(sK2,sK3) != iProver_top
% 3.18/1.00      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) != iProver_top
% 3.18/1.00      | v1_funct_1(sK2) != iProver_top
% 3.18/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_17,c_4845]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8,plain,
% 3.18/1.00      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 3.18/1.00      | ~ v1_funct_1(X0)
% 3.18/1.00      | v2_relat_1(X0)
% 3.18/1.00      | ~ v1_relat_1(X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_312,plain,
% 3.18/1.00      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 3.18/1.00      | ~ v1_funct_1(X0)
% 3.18/1.00      | ~ v1_relat_1(X0)
% 3.18/1.00      | sK3 != X0 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_313,plain,
% 3.18/1.00      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 3.18/1.00      | ~ v1_funct_1(sK3)
% 3.18/1.00      | ~ v1_relat_1(sK3) ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_312]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_314,plain,
% 3.18/1.00      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 3.18/1.00      | v1_funct_1(sK3) != iProver_top
% 3.18/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_18,negated_conjecture,
% 3.18/1.00      ( v5_funct_1(sK2,sK3) ),
% 3.18/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_27,plain,
% 3.18/1.00      ( v5_funct_1(sK2,sK3) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_21,negated_conjecture,
% 3.18/1.00      ( v1_funct_1(sK2) ),
% 3.18/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_24,plain,
% 3.18/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_22,negated_conjecture,
% 3.18/1.00      ( v1_relat_1(sK2) ),
% 3.18/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_23,plain,
% 3.18/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(contradiction,plain,
% 3.18/1.00      ( $false ),
% 3.18/1.00      inference(minisat,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_7373,c_314,c_27,c_26,c_25,c_24,c_23]) ).
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  ------                               Statistics
% 3.18/1.00  
% 3.18/1.00  ------ General
% 3.18/1.00  
% 3.18/1.00  abstr_ref_over_cycles:                  0
% 3.18/1.00  abstr_ref_under_cycles:                 0
% 3.18/1.00  gc_basic_clause_elim:                   0
% 3.18/1.00  forced_gc_time:                         0
% 3.18/1.00  parsing_time:                           0.01
% 3.18/1.00  unif_index_cands_time:                  0.
% 3.18/1.00  unif_index_add_time:                    0.
% 3.18/1.00  orderings_time:                         0.
% 3.18/1.00  out_proof_time:                         0.011
% 3.18/1.00  total_time:                             0.39
% 3.18/1.00  num_of_symbols:                         50
% 3.18/1.00  num_of_terms:                           6739
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing
% 3.18/1.00  
% 3.18/1.00  num_of_splits:                          0
% 3.18/1.00  num_of_split_atoms:                     0
% 3.18/1.00  num_of_reused_defs:                     0
% 3.18/1.00  num_eq_ax_congr_red:                    15
% 3.18/1.00  num_of_sem_filtered_clauses:            1
% 3.18/1.00  num_of_subtypes:                        1
% 3.18/1.00  monotx_restored_types:                  0
% 3.18/1.00  sat_num_of_epr_types:                   0
% 3.18/1.00  sat_num_of_non_cyclic_types:            0
% 3.18/1.00  sat_guarded_non_collapsed_types:        1
% 3.18/1.00  num_pure_diseq_elim:                    0
% 3.18/1.00  simp_replaced_by:                       0
% 3.18/1.00  res_preprocessed:                       121
% 3.18/1.00  prep_upred:                             0
% 3.18/1.00  prep_unflattend:                        14
% 3.18/1.00  smt_new_axioms:                         0
% 3.18/1.00  pred_elim_cands:                        6
% 3.18/1.00  pred_elim:                              0
% 3.18/1.00  pred_elim_cl:                           0
% 3.18/1.00  pred_elim_cycles:                       6
% 3.18/1.00  merged_defs:                            0
% 3.18/1.00  merged_defs_ncl:                        0
% 3.18/1.00  bin_hyper_res:                          0
% 3.18/1.00  prep_cycles:                            4
% 3.18/1.00  pred_elim_time:                         0.011
% 3.18/1.00  splitting_time:                         0.
% 3.18/1.00  sem_filter_time:                        0.
% 3.18/1.00  monotx_time:                            0.
% 3.18/1.00  subtype_inf_time:                       0.
% 3.18/1.00  
% 3.18/1.00  ------ Problem properties
% 3.18/1.00  
% 3.18/1.00  clauses:                                22
% 3.18/1.00  conjectures:                            7
% 3.18/1.00  epr:                                    7
% 3.18/1.00  horn:                                   19
% 3.18/1.00  ground:                                 9
% 3.18/1.00  unary:                                  11
% 3.18/1.00  binary:                                 3
% 3.18/1.00  lits:                                   57
% 3.18/1.00  lits_eq:                                8
% 3.18/1.00  fd_pure:                                0
% 3.18/1.00  fd_pseudo:                              0
% 3.18/1.00  fd_cond:                                1
% 3.18/1.00  fd_pseudo_cond:                         0
% 3.18/1.00  ac_symbols:                             0
% 3.18/1.00  
% 3.18/1.00  ------ Propositional Solver
% 3.18/1.00  
% 3.18/1.00  prop_solver_calls:                      29
% 3.18/1.00  prop_fast_solver_calls:                 1383
% 3.18/1.00  smt_solver_calls:                       0
% 3.18/1.00  smt_fast_solver_calls:                  0
% 3.18/1.00  prop_num_of_clauses:                    2478
% 3.18/1.00  prop_preprocess_simplified:             5952
% 3.18/1.00  prop_fo_subsumed:                       116
% 3.18/1.00  prop_solver_time:                       0.
% 3.18/1.00  smt_solver_time:                        0.
% 3.18/1.00  smt_fast_solver_time:                   0.
% 3.18/1.00  prop_fast_solver_time:                  0.
% 3.18/1.00  prop_unsat_core_time:                   0.
% 3.18/1.00  
% 3.18/1.00  ------ QBF
% 3.18/1.00  
% 3.18/1.00  qbf_q_res:                              0
% 3.18/1.00  qbf_num_tautologies:                    0
% 3.18/1.00  qbf_prep_cycles:                        0
% 3.18/1.00  
% 3.18/1.00  ------ BMC1
% 3.18/1.00  
% 3.18/1.00  bmc1_current_bound:                     -1
% 3.18/1.00  bmc1_last_solved_bound:                 -1
% 3.18/1.00  bmc1_unsat_core_size:                   -1
% 3.18/1.00  bmc1_unsat_core_parents_size:           -1
% 3.18/1.00  bmc1_merge_next_fun:                    0
% 3.18/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation
% 3.18/1.00  
% 3.18/1.00  inst_num_of_clauses:                    761
% 3.18/1.00  inst_num_in_passive:                    147
% 3.18/1.00  inst_num_in_active:                     538
% 3.18/1.00  inst_num_in_unprocessed:                76
% 3.18/1.00  inst_num_of_loops:                      650
% 3.18/1.00  inst_num_of_learning_restarts:          0
% 3.18/1.00  inst_num_moves_active_passive:          106
% 3.18/1.00  inst_lit_activity:                      0
% 3.18/1.00  inst_lit_activity_moves:                0
% 3.18/1.00  inst_num_tautologies:                   0
% 3.18/1.00  inst_num_prop_implied:                  0
% 3.18/1.00  inst_num_existing_simplified:           0
% 3.18/1.00  inst_num_eq_res_simplified:             0
% 3.18/1.00  inst_num_child_elim:                    0
% 3.18/1.00  inst_num_of_dismatching_blockings:      182
% 3.18/1.00  inst_num_of_non_proper_insts:           786
% 3.18/1.00  inst_num_of_duplicates:                 0
% 3.18/1.00  inst_inst_num_from_inst_to_res:         0
% 3.18/1.00  inst_dismatching_checking_time:         0.
% 3.18/1.00  
% 3.18/1.00  ------ Resolution
% 3.18/1.00  
% 3.18/1.00  res_num_of_clauses:                     0
% 3.18/1.00  res_num_in_passive:                     0
% 3.18/1.00  res_num_in_active:                      0
% 3.18/1.00  res_num_of_loops:                       125
% 3.18/1.00  res_forward_subset_subsumed:            62
% 3.18/1.00  res_backward_subset_subsumed:           2
% 3.18/1.00  res_forward_subsumed:                   0
% 3.18/1.00  res_backward_subsumed:                  0
% 3.18/1.00  res_forward_subsumption_resolution:     0
% 3.18/1.00  res_backward_subsumption_resolution:    0
% 3.18/1.00  res_clause_to_clause_subsumption:       607
% 3.18/1.00  res_orphan_elimination:                 0
% 3.18/1.00  res_tautology_del:                      122
% 3.18/1.00  res_num_eq_res_simplified:              0
% 3.18/1.00  res_num_sel_changes:                    0
% 3.18/1.00  res_moves_from_active_to_pass:          0
% 3.18/1.00  
% 3.18/1.00  ------ Superposition
% 3.18/1.00  
% 3.18/1.00  sup_time_total:                         0.
% 3.18/1.00  sup_time_generating:                    0.
% 3.18/1.00  sup_time_sim_full:                      0.
% 3.18/1.00  sup_time_sim_immed:                     0.
% 3.18/1.00  
% 3.18/1.00  sup_num_of_clauses:                     147
% 3.18/1.00  sup_num_in_active:                      125
% 3.18/1.00  sup_num_in_passive:                     22
% 3.18/1.00  sup_num_of_loops:                       129
% 3.18/1.00  sup_fw_superposition:                   248
% 3.18/1.00  sup_bw_superposition:                   88
% 3.18/1.00  sup_immediate_simplified:               71
% 3.18/1.00  sup_given_eliminated:                   2
% 3.18/1.00  comparisons_done:                       0
% 3.18/1.00  comparisons_avoided:                    0
% 3.18/1.00  
% 3.18/1.00  ------ Simplifications
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  sim_fw_subset_subsumed:                 62
% 3.18/1.00  sim_bw_subset_subsumed:                 0
% 3.18/1.00  sim_fw_subsumed:                        5
% 3.18/1.00  sim_bw_subsumed:                        3
% 3.18/1.00  sim_fw_subsumption_res:                 2
% 3.18/1.00  sim_bw_subsumption_res:                 1
% 3.18/1.00  sim_tautology_del:                      5
% 3.18/1.00  sim_eq_tautology_del:                   1
% 3.18/1.00  sim_eq_res_simp:                        3
% 3.18/1.00  sim_fw_demodulated:                     2
% 3.18/1.00  sim_bw_demodulated:                     3
% 3.18/1.00  sim_light_normalised:                   3
% 3.18/1.00  sim_joinable_taut:                      0
% 3.18/1.00  sim_joinable_simp:                      0
% 3.18/1.00  sim_ac_normalised:                      0
% 3.18/1.00  sim_smt_subsumption:                    0
% 3.18/1.00  
%------------------------------------------------------------------------------
