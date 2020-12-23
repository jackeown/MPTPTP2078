%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0766+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:05 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 854 expanded)
%              Number of clauses        :   79 ( 221 expanded)
%              Number of leaves         :   16 ( 260 expanded)
%              Depth                    :   22
%              Number of atoms          :  464 (6094 expanded)
%              Number of equality atoms :  118 ( 726 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
          ( ( r2_hidden(X3,sK2(X0,X1))
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK2(X0,X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( ( r2_hidden(X3,sK2(X0,X1))
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK2(X0,X1)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,sK2(X0,X1))
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X4] :
          ( ~ r2_hidden(k4_tarski(X4,X1),X0)
          & r2_hidden(X4,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK7,X1),X0)
        & r2_hidden(sK7,k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X0)
          & X1 != X3
          & r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(X3,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(X2,sK6(X2)),X0)
        & sK6(X2) != X1
        & r2_hidden(k4_tarski(X1,sK6(X2)),X0)
        & r2_hidden(sK6(X2),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
                & sK5 != X3
                & r2_hidden(k4_tarski(sK5,X3),X0)
                & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(k4_tarski(sK5,X2),X0)
            | ~ r2_hidden(X2,k3_relat_1(X0)) )
        & ? [X4] :
            ( ~ r2_hidden(k4_tarski(X4,sK5),X0)
            & r2_hidden(X4,k3_relat_1(X0)) )
        & r2_hidden(sK5,k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
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
                  ( ~ r2_hidden(k4_tarski(X2,X3),sK4)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),sK4)
                  & r2_hidden(X3,k3_relat_1(sK4)) )
              | ~ r2_hidden(k4_tarski(X1,X2),sK4)
              | ~ r2_hidden(X2,k3_relat_1(sK4)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),sK4)
              & r2_hidden(X4,k3_relat_1(sK4)) )
          & r2_hidden(X1,k3_relat_1(sK4)) )
      & v2_wellord1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ! [X2] :
        ( ( ~ r2_hidden(k4_tarski(X2,sK6(X2)),sK4)
          & sK5 != sK6(X2)
          & r2_hidden(k4_tarski(sK5,sK6(X2)),sK4)
          & r2_hidden(sK6(X2),k3_relat_1(sK4)) )
        | ~ r2_hidden(k4_tarski(sK5,X2),sK4)
        | ~ r2_hidden(X2,k3_relat_1(sK4)) )
    & ~ r2_hidden(k4_tarski(sK7,sK5),sK4)
    & r2_hidden(sK7,k3_relat_1(sK4))
    & r2_hidden(sK5,k3_relat_1(sK4))
    & v2_wellord1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f23,f37,f36,f35,f34])).

fof(f52,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK5,sK6(X2)),sK4)
      | ~ r2_hidden(k4_tarski(sK5,X2),sK4)
      | ~ r2_hidden(X2,k3_relat_1(sK4)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(X2,sK6(X2)),sK4)
      | ~ r2_hidden(k4_tarski(sK5,X2),sK4)
      | ~ r2_hidden(X2,k3_relat_1(sK4)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    r2_hidden(sK5,k3_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X3] :
                ( r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(sK3(X0,X1),X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f32])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
      | ~ r2_hidden(X3,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
      | ~ r2_hidden(X3,X1)
      | o_0_0_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f39])).

fof(f53,plain,(
    v2_wellord1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | o_0_0_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f39])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,sK2(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f24])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_relat_1(X0))
      | ~ r2_hidden(X3,sK2(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ~ r2_hidden(k4_tarski(sK7,sK5),sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    r2_hidden(sK7,k3_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f4,f26])).

fof(f43,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_4,plain,
    ( r2_hidden(X0,sK2(X1,X2))
    | ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_380,plain,
    ( r2_hidden(X0,sK2(X1,X2))
    | ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_381,plain,
    ( r2_hidden(X0,sK2(sK4,X1))
    | ~ r2_hidden(X0,k3_relat_1(sK4))
    | r2_hidden(k4_tarski(X0,X1),sK4) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_1042,plain,
    ( r2_hidden(X0,sK2(sK4,X1)) = iProver_top
    | r2_hidden(X0,k3_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(X0,k3_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(sK5,X0),sK4)
    | r2_hidden(k4_tarski(sK5,sK6(X0)),sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1053,plain,
    ( r2_hidden(X0,k3_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(sK5,X0),sK4) != iProver_top
    | r2_hidden(k4_tarski(sK5,sK6(X0)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(X0,k3_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X0,sK6(X0)),sK4)
    | ~ r2_hidden(k4_tarski(sK5,X0),sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1055,plain,
    ( r2_hidden(X0,k3_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK6(X0)),sK4) != iProver_top
    | r2_hidden(k4_tarski(sK5,X0),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1287,plain,
    ( r2_hidden(k4_tarski(sK5,sK5),sK4) != iProver_top
    | r2_hidden(sK5,k3_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_1055])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK5,k3_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,plain,
    ( r2_hidden(sK5,k3_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1591,plain,
    ( r2_hidden(k4_tarski(sK5,sK5),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1287,c_23])).

cnf(c_1596,plain,
    ( r2_hidden(sK5,sK2(sK4,sK5)) = iProver_top
    | r2_hidden(sK5,k3_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_1591])).

cnf(c_1212,plain,
    ( r2_hidden(k4_tarski(sK5,X0),sK4)
    | r2_hidden(sK5,sK2(sK4,X0))
    | ~ r2_hidden(sK5,k3_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_1261,plain,
    ( r2_hidden(k4_tarski(sK5,sK5),sK4)
    | r2_hidden(sK5,sK2(sK4,sK5))
    | ~ r2_hidden(sK5,k3_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1212])).

cnf(c_1262,plain,
    ( r2_hidden(k4_tarski(sK5,sK5),sK4) = iProver_top
    | r2_hidden(sK5,sK2(sK4,sK5)) = iProver_top
    | r2_hidden(sK5,k3_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1261])).

cnf(c_2009,plain,
    ( r2_hidden(sK5,sK2(sK4,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1596,c_23,c_1262,c_1287])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK3(X2,X1),X0),X2)
    | ~ r1_tarski(X1,k3_relat_1(X2))
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2)
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_19,negated_conjecture,
    ( v2_wellord1(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_323,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK3(X2,X1),X0),X2)
    | ~ r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | sK4 != X2
    | o_0_0_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_324,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK3(sK4,X1),X0),sK4)
    | ~ r1_tarski(X1,k3_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | o_0_0_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_328,plain,
    ( ~ r1_tarski(X1,k3_relat_1(sK4))
    | r2_hidden(k4_tarski(sK3(sK4,X1),X0),sK4)
    | ~ r2_hidden(X0,X1)
    | o_0_0_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_324,c_20])).

cnf(c_329,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK3(sK4,X1),X0),sK4)
    | ~ r1_tarski(X1,k3_relat_1(sK4))
    | o_0_0_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_328])).

cnf(c_1045,plain,
    ( o_0_0_xboole_0 = X0
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(k4_tarski(sK3(sK4,X0),X1),sK4) = iProver_top
    | r1_tarski(X0,k3_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_8,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | ~ r1_tarski(X1,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0)
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_302,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | ~ r1_tarski(X1,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK4 != X0
    | o_0_0_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_303,plain,
    ( r2_hidden(sK3(sK4,X0),X0)
    | ~ r1_tarski(X0,k3_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | o_0_0_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_307,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK4))
    | r2_hidden(sK3(sK4,X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_303,c_20])).

cnf(c_308,plain,
    ( r2_hidden(sK3(sK4,X0),X0)
    | ~ r1_tarski(X0,k3_relat_1(sK4))
    | o_0_0_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_307])).

cnf(c_1046,plain,
    ( o_0_0_xboole_0 = X0
    | r2_hidden(sK3(sK4,X0),X0) = iProver_top
    | r1_tarski(X0,k3_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,sK2(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_368,plain,
    ( ~ r2_hidden(X0,sK2(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_20])).

cnf(c_369,plain,
    ( ~ r2_hidden(X0,sK2(sK4,X1))
    | ~ r2_hidden(k4_tarski(X0,X1),sK4) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_1043,plain,
    ( r2_hidden(X0,sK2(sK4,X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_1781,plain,
    ( sK2(sK4,X0) = o_0_0_xboole_0
    | r2_hidden(k4_tarski(sK3(sK4,sK2(sK4,X0)),X0),sK4) != iProver_top
    | r1_tarski(sK2(sK4,X0),k3_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1046,c_1043])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1058,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,sK2(X1,X2))
    | r2_hidden(X0,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_356,plain,
    ( ~ r2_hidden(X0,sK2(X1,X2))
    | r2_hidden(X0,k3_relat_1(X1))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_357,plain,
    ( ~ r2_hidden(X0,sK2(sK4,X1))
    | r2_hidden(X0,k3_relat_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_1044,plain,
    ( r2_hidden(X0,sK2(sK4,X1)) != iProver_top
    | r2_hidden(X0,k3_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_1471,plain,
    ( r2_hidden(sK0(sK2(sK4,X0),X1),k3_relat_1(sK4)) = iProver_top
    | r1_tarski(sK2(sK4,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1058,c_1044])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1059,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1946,plain,
    ( r1_tarski(sK2(sK4,X0),k3_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1471,c_1059])).

cnf(c_2072,plain,
    ( r2_hidden(k4_tarski(sK3(sK4,sK2(sK4,X0)),X0),sK4) != iProver_top
    | sK2(sK4,X0) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1781,c_1946])).

cnf(c_2073,plain,
    ( sK2(sK4,X0) = o_0_0_xboole_0
    | r2_hidden(k4_tarski(sK3(sK4,sK2(sK4,X0)),X0),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_2072])).

cnf(c_2080,plain,
    ( sK2(sK4,X0) = o_0_0_xboole_0
    | r2_hidden(X0,sK2(sK4,X0)) != iProver_top
    | r1_tarski(sK2(sK4,X0),k3_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_2073])).

cnf(c_2101,plain,
    ( r2_hidden(X0,sK2(sK4,X0)) != iProver_top
    | sK2(sK4,X0) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2080,c_1946])).

cnf(c_2102,plain,
    ( sK2(sK4,X0) = o_0_0_xboole_0
    | r2_hidden(X0,sK2(sK4,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2101])).

cnf(c_2109,plain,
    ( sK2(sK4,sK5) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_2009,c_2102])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK7,sK5),sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1051,plain,
    ( r2_hidden(k4_tarski(sK7,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1350,plain,
    ( r2_hidden(sK7,sK2(sK4,sK5)) = iProver_top
    | r2_hidden(sK7,k3_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_1051])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK7,k3_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,plain,
    ( r2_hidden(sK7,k3_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_25,plain,
    ( r2_hidden(k4_tarski(sK7,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1207,plain,
    ( r2_hidden(k4_tarski(sK7,X0),sK4)
    | r2_hidden(sK7,sK2(sK4,X0))
    | ~ r2_hidden(sK7,k3_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_1250,plain,
    ( r2_hidden(k4_tarski(sK7,sK5),sK4)
    | r2_hidden(sK7,sK2(sK4,sK5))
    | ~ r2_hidden(sK7,k3_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1207])).

cnf(c_1251,plain,
    ( r2_hidden(k4_tarski(sK7,sK5),sK4) = iProver_top
    | r2_hidden(sK7,sK2(sK4,sK5)) = iProver_top
    | r2_hidden(sK7,k3_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1250])).

cnf(c_1562,plain,
    ( r2_hidden(sK7,sK2(sK4,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1350,c_24,c_25,c_1251])).

cnf(c_2754,plain,
    ( r2_hidden(sK7,o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2109,c_1562])).

cnf(c_2762,plain,
    ( r2_hidden(X0,k3_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2109,c_1044])).

cnf(c_2,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_65,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1057,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X2)
    | k1_zfmisc_1(X2) != X3
    | sK1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_246,plain,
    ( ~ r2_hidden(X0,sK1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_1047,plain,
    ( r2_hidden(X0,sK1(k1_zfmisc_1(X1))) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_246])).

cnf(c_1855,plain,
    ( r1_tarski(sK1(k1_zfmisc_1(X0)),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1058,c_1047])).

cnf(c_1856,plain,
    ( sK1(k1_zfmisc_1(X0)) = o_0_0_xboole_0
    | r1_tarski(sK1(k1_zfmisc_1(X0)),k3_relat_1(sK4)) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1046,c_1047])).

cnf(c_1866,plain,
    ( sK1(k1_zfmisc_1(X0)) = o_0_0_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1855,c_1856])).

cnf(c_2603,plain,
    ( sK1(k1_zfmisc_1(o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1057,c_1866])).

cnf(c_2616,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2603,c_1047])).

cnf(c_2830,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2762,c_65,c_2616])).

cnf(c_2840,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2754,c_2830])).


%------------------------------------------------------------------------------
