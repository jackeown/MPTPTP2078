%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0766+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:04 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 274 expanded)
%              Number of clauses        :   57 (  66 expanded)
%              Number of leaves         :   16 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  436 (2066 expanded)
%              Number of equality atoms :   59 ( 210 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X3] :
                ( r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(sK2(X0,X1),X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f26])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
      | ~ r2_hidden(X3,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
      | ~ r2_hidden(X3,X1)
      | o_0_0_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f43,f34])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                          & X1 != X3
                          & r2_hidden(k4_tarski(X1,X3),X0)
                          & r2_hidden(X3,k3_relat_1(X0)) )
                    & r2_hidden(k4_tarski(X1,X2),X0)
                    & r2_hidden(X2,k3_relat_1(X0)) )
              & ? [X2] :
                  ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                  & r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                            & X1 != X3
                            & r2_hidden(k4_tarski(X1,X3),X0)
                            & r2_hidden(X3,k3_relat_1(X0)) )
                      & r2_hidden(k4_tarski(X1,X2),X0)
                      & r2_hidden(X2,k3_relat_1(X0)) )
                & ? [X2] :
                    ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                    & r2_hidden(X2,k3_relat_1(X0)) )
                & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                            & X1 != X3
                            & r2_hidden(k4_tarski(X1,X3),X0)
                            & r2_hidden(X3,k3_relat_1(X0)) )
                      & r2_hidden(k4_tarski(X1,X2),X0)
                      & r2_hidden(X2,k3_relat_1(X0)) )
                & ? [X4] :
                    ( ~ r2_hidden(k4_tarski(X4,X1),X0)
                    & r2_hidden(X4,k3_relat_1(X0)) )
                & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    inference(rectify,[],[f9])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),X0)
                  & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),X0)
              & r2_hidden(X4,k3_relat_1(X0)) )
          & r2_hidden(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),X0)
                  & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),X0)
              & r2_hidden(X4,k3_relat_1(X0)) )
          & r2_hidden(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X4] :
          ( ~ r2_hidden(k4_tarski(X4,X1),X0)
          & r2_hidden(X4,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK6,X1),X0)
        & r2_hidden(sK6,k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X0)
          & X1 != X3
          & r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(X3,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(X2,sK5(X2)),X0)
        & sK5(X2) != X1
        & r2_hidden(k4_tarski(X1,sK5(X2)),X0)
        & r2_hidden(sK5(X2),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),X0)
                  & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),X0)
              & r2_hidden(X4,k3_relat_1(X0)) )
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ! [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                & sK4 != X3
                & r2_hidden(k4_tarski(sK4,X3),X0)
                & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(k4_tarski(sK4,X2),X0)
            | ~ r2_hidden(X2,k3_relat_1(X0)) )
        & ? [X4] :
            ( ~ r2_hidden(k4_tarski(X4,sK4),X0)
            & r2_hidden(X4,k3_relat_1(X0)) )
        & r2_hidden(sK4,k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                    & X1 != X3
                    & r2_hidden(k4_tarski(X1,X3),X0)
                    & r2_hidden(X3,k3_relat_1(X0)) )
                | ~ r2_hidden(k4_tarski(X1,X2),X0)
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & ? [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X1),X0)
                & r2_hidden(X4,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) )
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),sK3)
                  & r2_hidden(X3,k3_relat_1(sK3)) )
              | ~ r2_hidden(k4_tarski(X1,X2),sK3)
              | ~ r2_hidden(X2,k3_relat_1(sK3)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),sK3)
              & r2_hidden(X4,k3_relat_1(sK3)) )
          & r2_hidden(X1,k3_relat_1(sK3)) )
      & v2_wellord1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ! [X2] :
        ( ( ~ r2_hidden(k4_tarski(X2,sK5(X2)),sK3)
          & sK4 != sK5(X2)
          & r2_hidden(k4_tarski(sK4,sK5(X2)),sK3)
          & r2_hidden(sK5(X2),k3_relat_1(sK3)) )
        | ~ r2_hidden(k4_tarski(sK4,X2),sK3)
        | ~ r2_hidden(X2,k3_relat_1(sK3)) )
    & ~ r2_hidden(k4_tarski(sK6,sK4),sK3)
    & r2_hidden(sK6,k3_relat_1(sK3))
    & r2_hidden(sK4,k3_relat_1(sK3))
    & v2_wellord1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f17,f32,f31,f30,f29])).

fof(f48,plain,(
    v2_wellord1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
     => ! [X3] :
          ( ( r2_hidden(X3,sK1(X0,X1))
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK1(X0,X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( ( r2_hidden(X3,sK1(X0,X1))
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK1(X0,X1)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,sK1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_relat_1(X0))
      | ~ r2_hidden(X3,sK1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | o_0_0_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f42,f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK4,sK5(X2)),sK3)
      | ~ r2_hidden(k4_tarski(sK4,X2),sK3)
      | ~ r2_hidden(X2,k3_relat_1(sK3)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(X2,sK5(X2)),sK3)
      | ~ r2_hidden(k4_tarski(sK4,X2),sK3)
      | ~ r2_hidden(X2,k3_relat_1(sK3)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,sK1(X0,X1))
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ~ r2_hidden(k4_tarski(sK6,sK4),sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    r2_hidden(sK6,k3_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    r2_hidden(sK4,k3_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK2(X2,X1),X0),X2)
    | ~ r1_tarski(X1,k3_relat_1(X2))
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2)
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_19,negated_conjecture,
    ( v2_wellord1(sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_310,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK2(X2,X1),X0),X2)
    | ~ r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | sK3 != X2
    | o_0_0_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_311,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK2(sK3,X1),X0),sK3)
    | ~ r1_tarski(X1,k3_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | o_0_0_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_315,plain,
    ( ~ r1_tarski(X1,k3_relat_1(sK3))
    | r2_hidden(k4_tarski(sK2(sK3,X1),X0),sK3)
    | ~ r2_hidden(X0,X1)
    | o_0_0_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_311,c_20])).

cnf(c_316,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK2(sK3,X1),X0),sK3)
    | ~ r1_tarski(X1,k3_relat_1(sK3))
    | o_0_0_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_315])).

cnf(c_3735,plain,
    ( ~ r2_hidden(X0,sK1(sK3,sK4))
    | r2_hidden(k4_tarski(sK2(sK3,sK1(sK3,sK4)),X0),sK3)
    | ~ r1_tarski(sK1(sK3,sK4),k3_relat_1(sK3))
    | o_0_0_xboole_0 = sK1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_5618,plain,
    ( r2_hidden(k4_tarski(sK2(sK3,sK1(sK3,sK4)),sK4),sK3)
    | ~ r2_hidden(sK4,sK1(sK3,sK4))
    | ~ r1_tarski(sK1(sK3,sK4),k3_relat_1(sK3))
    | o_0_0_xboole_0 = sK1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3735])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,sK1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_355,plain,
    ( ~ r2_hidden(X0,sK1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_20])).

cnf(c_356,plain,
    ( ~ r2_hidden(X0,sK1(sK3,X1))
    | ~ r2_hidden(k4_tarski(X0,X1),sK3) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_5414,plain,
    ( ~ r2_hidden(sK2(sK3,sK1(sK3,sK4)),sK1(sK3,sK4))
    | ~ r2_hidden(k4_tarski(sK2(sK3,sK1(sK3,sK4)),sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,sK1(X1,X2))
    | r2_hidden(X0,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_343,plain,
    ( ~ r2_hidden(X0,sK1(X1,X2))
    | r2_hidden(X0,k3_relat_1(X1))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_344,plain,
    ( ~ r2_hidden(X0,sK1(sK3,X1))
    | r2_hidden(X0,k3_relat_1(sK3)) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_4665,plain,
    ( ~ r2_hidden(sK0(sK1(sK3,sK4),k3_relat_1(sK3)),sK1(sK3,sK4))
    | r2_hidden(sK0(sK1(sK3,sK4),k3_relat_1(sK3)),k3_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_8,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | ~ r1_tarski(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0)
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_289,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | ~ r1_tarski(X1,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK3 != X0
    | o_0_0_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_290,plain,
    ( r2_hidden(sK2(sK3,X0),X0)
    | ~ r1_tarski(X0,k3_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | o_0_0_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_294,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK3))
    | r2_hidden(sK2(sK3,X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_290,c_20])).

cnf(c_295,plain,
    ( r2_hidden(sK2(sK3,X0),X0)
    | ~ r1_tarski(X0,k3_relat_1(sK3))
    | o_0_0_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_294])).

cnf(c_4024,plain,
    ( r2_hidden(sK2(sK3,sK1(sK3,sK4)),sK1(sK3,sK4))
    | ~ r1_tarski(sK1(sK3,sK4),k3_relat_1(sK3))
    | o_0_0_xboole_0 = sK1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2519,plain,
    ( ~ r2_hidden(sK0(sK1(sK3,sK4),X0),X0)
    | r1_tarski(sK1(sK3,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4023,plain,
    ( ~ r2_hidden(sK0(sK1(sK3,sK4),k3_relat_1(sK3)),k3_relat_1(sK3))
    | r1_tarski(sK1(sK3,sK4),k3_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2519])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2518,plain,
    ( r2_hidden(sK0(sK1(sK3,sK4),X0),sK1(sK3,sK4))
    | r1_tarski(sK1(sK3,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3734,plain,
    ( r2_hidden(sK0(sK1(sK3,sK4),k3_relat_1(sK3)),sK1(sK3,sK4))
    | r1_tarski(sK1(sK3,sK4),k3_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2518])).

cnf(c_721,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1265,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK6,sK1(sK3,sK4))
    | X1 != sK1(sK3,sK4)
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1977,plain,
    ( r2_hidden(sK6,X0)
    | ~ r2_hidden(sK6,sK1(sK3,sK4))
    | X0 != sK1(sK3,sK4)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_3541,plain,
    ( ~ r2_hidden(sK6,sK1(sK3,sK4))
    | r2_hidden(sK6,o_0_0_xboole_0)
    | sK6 != sK6
    | o_0_0_xboole_0 != sK1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1977])).

cnf(c_3,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_277,plain,
    ( ~ r2_hidden(X0,X1)
    | o_0_0_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_278,plain,
    ( ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_1366,plain,
    ( ~ r2_hidden(sK6,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(X0,k3_relat_1(sK3))
    | ~ r2_hidden(k4_tarski(sK4,X0),sK3)
    | r2_hidden(k4_tarski(sK4,sK5(X0)),sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1002,plain,
    ( r2_hidden(X0,k3_relat_1(sK3)) != iProver_top
    | r2_hidden(k4_tarski(sK4,X0),sK3) != iProver_top
    | r2_hidden(k4_tarski(sK4,sK5(X0)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(X0,k3_relat_1(sK3))
    | ~ r2_hidden(k4_tarski(X0,sK5(X0)),sK3)
    | ~ r2_hidden(k4_tarski(sK4,X0),sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1004,plain,
    ( r2_hidden(X0,k3_relat_1(sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK5(X0)),sK3) != iProver_top
    | r2_hidden(k4_tarski(sK4,X0),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1300,plain,
    ( r2_hidden(k4_tarski(sK4,sK4),sK3) != iProver_top
    | r2_hidden(sK4,k3_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1002,c_1004])).

cnf(c_1301,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK4),sK3)
    | ~ r2_hidden(sK4,k3_relat_1(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1300])).

cnf(c_718,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1245,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_4,plain,
    ( r2_hidden(X0,sK1(X1,X2))
    | ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_367,plain,
    ( r2_hidden(X0,sK1(X1,X2))
    | ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_368,plain,
    ( r2_hidden(X0,sK1(sK3,X1))
    | ~ r2_hidden(X0,k3_relat_1(sK3))
    | r2_hidden(k4_tarski(X0,X1),sK3) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_1149,plain,
    ( r2_hidden(k4_tarski(sK4,X0),sK3)
    | r2_hidden(sK4,sK1(sK3,X0))
    | ~ r2_hidden(sK4,k3_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_1230,plain,
    ( r2_hidden(k4_tarski(sK4,sK4),sK3)
    | r2_hidden(sK4,sK1(sK3,sK4))
    | ~ r2_hidden(sK4,k3_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_1144,plain,
    ( r2_hidden(k4_tarski(sK6,X0),sK3)
    | r2_hidden(sK6,sK1(sK3,X0))
    | ~ r2_hidden(sK6,k3_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_1216,plain,
    ( r2_hidden(k4_tarski(sK6,sK4),sK3)
    | r2_hidden(sK6,sK1(sK3,sK4))
    | ~ r2_hidden(sK6,k3_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1144])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK6,sK4),sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK6,k3_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK4,k3_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5618,c_5414,c_4665,c_4024,c_4023,c_3734,c_3541,c_1366,c_1301,c_1245,c_1230,c_1216,c_16,c_17,c_18])).


%------------------------------------------------------------------------------
