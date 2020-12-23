%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:44 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 731 expanded)
%              Number of clauses        :   85 ( 241 expanded)
%              Number of leaves         :   16 ( 204 expanded)
%              Depth                    :   30
%              Number of atoms          :  449 (4024 expanded)
%              Number of equality atoms :  243 (1823 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                & k1_relat_1(X0) = k1_relat_1(X1) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                  & k1_relat_1(X0) = k1_relat_1(X1) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
          & ! [X3] :
              ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
              | ~ r2_hidden(X3,X2) )
          & k1_relat_1(X0) = k1_relat_1(X1) )
     => ( k7_relat_1(X0,sK3) != k7_relat_1(X1,sK3)
        & ! [X3] :
            ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,sK3) )
        & k1_relat_1(X0) = k1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( k7_relat_1(sK2,X2) != k7_relat_1(X0,X2)
            & ! [X3] :
                ( k1_funct_1(sK2,X3) = k1_funct_1(X0,X3)
                | ~ r2_hidden(X3,X2) )
            & k1_relat_1(sK2) = k1_relat_1(X0) )
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                & k1_relat_1(X0) = k1_relat_1(X1) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(sK1,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(sK1,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(sK1) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3)
    & ! [X3] :
        ( k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)
        | ~ r2_hidden(X3,sK3) )
    & k1_relat_1(sK1) = k1_relat_1(sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f27,f26,f25])).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f35,f29])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    k1_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
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

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) ) )
                & ( ! [X3] :
                      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                      | ~ r2_hidden(X3,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) ) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ( k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2))
                    & r2_hidden(sK0(X0,X1,X2),X2) ) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2))
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_146,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_485,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_146])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_157,plain,
    ( ~ v1_relat_1(X0_41)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0_41),X0_42)) = k1_relat_1(k7_relat_1(X0_41,X0_42)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_476,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(X0_41),X0_42)) = k1_relat_1(k7_relat_1(X0_41,X0_42))
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_157])).

cnf(c_1121,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0_42)) = k1_relat_1(k7_relat_1(sK1,X0_42)) ),
    inference(superposition,[status(thm)],[c_485,c_476])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_162,plain,
    ( ~ v1_relat_1(X0_41)
    | k7_relat_1(X0_41,k1_setfam_1(k2_tarski(X0_42,X1_42))) = k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_471,plain,
    ( k7_relat_1(X0_41,k1_setfam_1(k2_tarski(X0_42,X1_42))) = k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_162])).

cnf(c_722,plain,
    ( k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0_42,X1_42))) = k7_relat_1(k7_relat_1(sK1,X0_42),X1_42) ),
    inference(superposition,[status(thm)],[c_485,c_471])).

cnf(c_2590,plain,
    ( k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0_42) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0_42))) ),
    inference(superposition,[status(thm)],[c_1121,c_722])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_156,plain,
    ( ~ v1_relat_1(X0_41)
    | k7_relat_1(X0_41,k1_relat_1(X0_41)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_477,plain,
    ( k7_relat_1(X0_41,k1_relat_1(X0_41)) = X0_41
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_156])).

cnf(c_728,plain,
    ( k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_485,c_477])).

cnf(c_2638,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0_42))) = k7_relat_1(sK1,X0_42) ),
    inference(light_normalisation,[status(thm)],[c_2590,c_728])).

cnf(c_12,negated_conjecture,
    ( k1_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_150,negated_conjecture,
    ( k1_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_4,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_158,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_41,X0_42)),k1_relat_1(X0_41))
    | ~ v1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_475,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_41,X0_42)),k1_relat_1(X0_41)) = iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_158])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | r2_hidden(sK0(X2,X1,X0),X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(X1,X0) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_154,plain,
    ( ~ r1_tarski(X0_42,k1_relat_1(X0_41))
    | ~ r1_tarski(X0_42,k1_relat_1(X1_41))
    | r2_hidden(sK0(X0_41,X1_41,X0_42),X0_42)
    | ~ v1_funct_1(X0_41)
    | ~ v1_funct_1(X1_41)
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | k7_relat_1(X1_41,X0_42) = k7_relat_1(X0_41,X0_42) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_479,plain,
    ( k7_relat_1(X0_41,X0_42) = k7_relat_1(X1_41,X0_42)
    | r1_tarski(X0_42,k1_relat_1(X1_41)) != iProver_top
    | r1_tarski(X0_42,k1_relat_1(X0_41)) != iProver_top
    | r2_hidden(sK0(X1_41,X0_41,X0_42),X0_42) = iProver_top
    | v1_funct_1(X1_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v1_relat_1(X1_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_154])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_148,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_483,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_148])).

cnf(c_1120,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0_42)) = k1_relat_1(k7_relat_1(sK2,X0_42)) ),
    inference(superposition,[status(thm)],[c_483,c_476])).

cnf(c_1125,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0_42)) = k1_relat_1(k7_relat_1(sK2,X0_42)) ),
    inference(light_normalisation,[status(thm)],[c_1120,c_150])).

cnf(c_1767,plain,
    ( k1_relat_1(k7_relat_1(sK1,X0_42)) = k1_relat_1(k7_relat_1(sK2,X0_42)) ),
    inference(demodulation,[status(thm)],[c_1121,c_1125])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_159,plain,
    ( r2_hidden(X0_43,X0_42)
    | ~ r2_hidden(X0_43,k1_relat_1(k7_relat_1(X0_41,X0_42)))
    | ~ v1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_474,plain,
    ( r2_hidden(X0_43,X0_42) = iProver_top
    | r2_hidden(X0_43,k1_relat_1(k7_relat_1(X0_41,X0_42))) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_1918,plain,
    ( r2_hidden(X0_43,X0_42) = iProver_top
    | r2_hidden(X0_43,k1_relat_1(k7_relat_1(sK1,X0_42))) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1767,c_474])).

cnf(c_19,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3507,plain,
    ( r2_hidden(X0_43,k1_relat_1(k7_relat_1(sK1,X0_42))) != iProver_top
    | r2_hidden(X0_43,X0_42) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1918,c_19])).

cnf(c_3508,plain,
    ( r2_hidden(X0_43,X0_42) = iProver_top
    | r2_hidden(X0_43,k1_relat_1(k7_relat_1(sK1,X0_42))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3507])).

cnf(c_3515,plain,
    ( k7_relat_1(X0_41,k1_relat_1(k7_relat_1(sK1,X0_42))) = k7_relat_1(X1_41,k1_relat_1(k7_relat_1(sK1,X0_42)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0_42)),k1_relat_1(X0_41)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0_42)),k1_relat_1(X1_41)) != iProver_top
    | r2_hidden(sK0(X0_41,X1_41,k1_relat_1(k7_relat_1(sK1,X0_42))),X0_42) = iProver_top
    | v1_funct_1(X1_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v1_relat_1(X1_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_479,c_3508])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_151,negated_conjecture,
    ( ~ r2_hidden(X0_43,sK3)
    | k1_funct_1(sK1,X0_43) = k1_funct_1(sK2,X0_43) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_481,plain,
    ( k1_funct_1(sK1,X0_43) = k1_funct_1(sK2,X0_43)
    | r2_hidden(X0_43,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_151])).

cnf(c_4808,plain,
    ( k1_funct_1(sK2,sK0(X0_41,X1_41,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(X0_41,X1_41,k1_relat_1(k7_relat_1(sK1,sK3))))
    | k7_relat_1(X1_41,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(X0_41,k1_relat_1(k7_relat_1(sK1,sK3)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(X0_41)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(X1_41)) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v1_funct_1(X1_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(X1_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_3515,c_481])).

cnf(c_5969,plain,
    ( k1_funct_1(sK1,sK0(sK1,X0_41,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK2,sK0(sK1,X0_41,k1_relat_1(k7_relat_1(sK1,sK3))))
    | k7_relat_1(X0_41,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(X0_41)) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_475,c_4808])).

cnf(c_17,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6030,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | k1_funct_1(sK1,sK0(sK1,X0_41,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK2,sK0(sK1,X0_41,k1_relat_1(k7_relat_1(sK1,sK3))))
    | k7_relat_1(X0_41,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(X0_41)) != iProver_top
    | v1_funct_1(X0_41) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5969,c_17,c_18])).

cnf(c_6031,plain,
    ( k1_funct_1(sK1,sK0(sK1,X0_41,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK2,sK0(sK1,X0_41,k1_relat_1(k7_relat_1(sK1,sK3))))
    | k7_relat_1(X0_41,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(X0_41)) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(renaming,[status(thm)],[c_6030])).

cnf(c_6041,plain,
    ( k1_funct_1(sK2,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3))))
    | k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_150,c_6031])).

cnf(c_671,plain,
    ( k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0_42,X1_42))) = k7_relat_1(k7_relat_1(sK2,X0_42),X1_42) ),
    inference(superposition,[status(thm)],[c_483,c_471])).

cnf(c_1966,plain,
    ( k7_relat_1(k7_relat_1(sK2,k1_relat_1(sK1)),X0_42) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,X0_42))) ),
    inference(superposition,[status(thm)],[c_1121,c_671])).

cnf(c_727,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_483,c_477])).

cnf(c_732,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK1)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_727,c_150])).

cnf(c_2023,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,X0_42))) = k7_relat_1(sK2,X0_42) ),
    inference(light_normalisation,[status(thm)],[c_1966,c_732])).

cnf(c_6058,plain,
    ( k1_funct_1(sK2,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3))))
    | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK2,sK3)
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6041,c_2023])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_209,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_6067,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3))))
    | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6058])).

cnf(c_6502,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK2,sK3)
    | k1_funct_1(sK2,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6058,c_16,c_14,c_13,c_209,c_6067])).

cnf(c_6503,plain,
    ( k1_funct_1(sK2,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3))))
    | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_6502])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X1,sK0(X2,X1,X0)) != k1_funct_1(X2,sK0(X2,X1,X0))
    | k7_relat_1(X1,X0) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_155,plain,
    ( ~ r1_tarski(X0_42,k1_relat_1(X0_41))
    | ~ r1_tarski(X0_42,k1_relat_1(X1_41))
    | ~ v1_funct_1(X0_41)
    | ~ v1_funct_1(X1_41)
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | k1_funct_1(X1_41,sK0(X0_41,X1_41,X0_42)) != k1_funct_1(X0_41,sK0(X0_41,X1_41,X0_42))
    | k7_relat_1(X1_41,X0_42) = k7_relat_1(X0_41,X0_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_478,plain,
    ( k1_funct_1(X0_41,sK0(X1_41,X0_41,X0_42)) != k1_funct_1(X1_41,sK0(X1_41,X0_41,X0_42))
    | k7_relat_1(X0_41,X0_42) = k7_relat_1(X1_41,X0_42)
    | r1_tarski(X0_42,k1_relat_1(X1_41)) != iProver_top
    | r1_tarski(X0_42,k1_relat_1(X0_41)) != iProver_top
    | v1_funct_1(X1_41) != iProver_top
    | v1_funct_1(X0_41) != iProver_top
    | v1_relat_1(X1_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_155])).

cnf(c_6506,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
    | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK2,sK3)
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6503,c_478])).

cnf(c_6507,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
    | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK2,sK3)
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6506,c_150])).

cnf(c_6508,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK2,sK3)
    | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6507,c_2023])).

cnf(c_20,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_208,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_41,X0_42)),k1_relat_1(X0_41)) = iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_158])).

cnf(c_210,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_208])).

cnf(c_6511,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6508,c_17,c_18,c_19,c_20,c_210])).

cnf(c_12954,plain,
    ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3) ),
    inference(demodulation,[status(thm)],[c_2638,c_6511])).

cnf(c_169,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_658,plain,
    ( k7_relat_1(sK2,sK3) != X0_41
    | k7_relat_1(sK1,sK3) != X0_41
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_687,plain,
    ( k7_relat_1(sK2,sK3) != k7_relat_1(X0_41,sK3)
    | k7_relat_1(sK1,sK3) != k7_relat_1(X0_41,sK3)
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_690,plain,
    ( k7_relat_1(sK2,sK3) != k7_relat_1(sK1,sK3)
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)
    | k7_relat_1(sK1,sK3) != k7_relat_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_10,negated_conjecture,
    ( k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_152,negated_conjecture,
    ( k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_165,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_192,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_164,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_191,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_172,plain,
    ( X0_42 != X1_42
    | X0_41 != X1_41
    | k7_relat_1(X0_41,X0_42) = k7_relat_1(X1_41,X1_42) ),
    theory(equality)).

cnf(c_181,plain,
    ( sK3 != sK3
    | k7_relat_1(sK1,sK3) = k7_relat_1(sK1,sK3)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12954,c_690,c_152,c_192,c_191,c_181])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:19:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.83/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.83/0.99  
% 3.83/0.99  ------  iProver source info
% 3.83/0.99  
% 3.83/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.83/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.83/0.99  git: non_committed_changes: false
% 3.83/0.99  git: last_make_outside_of_git: false
% 3.83/0.99  
% 3.83/0.99  ------ 
% 3.83/0.99  
% 3.83/0.99  ------ Input Options
% 3.83/0.99  
% 3.83/0.99  --out_options                           all
% 3.83/0.99  --tptp_safe_out                         true
% 3.83/0.99  --problem_path                          ""
% 3.83/0.99  --include_path                          ""
% 3.83/0.99  --clausifier                            res/vclausify_rel
% 3.83/0.99  --clausifier_options                    --mode clausify
% 3.83/0.99  --stdin                                 false
% 3.83/0.99  --stats_out                             sel
% 3.83/0.99  
% 3.83/0.99  ------ General Options
% 3.83/0.99  
% 3.83/0.99  --fof                                   false
% 3.83/0.99  --time_out_real                         604.99
% 3.83/0.99  --time_out_virtual                      -1.
% 3.83/0.99  --symbol_type_check                     false
% 3.83/0.99  --clausify_out                          false
% 3.83/0.99  --sig_cnt_out                           false
% 3.83/0.99  --trig_cnt_out                          false
% 3.83/0.99  --trig_cnt_out_tolerance                1.
% 3.83/0.99  --trig_cnt_out_sk_spl                   false
% 3.83/0.99  --abstr_cl_out                          false
% 3.83/0.99  
% 3.83/0.99  ------ Global Options
% 3.83/0.99  
% 3.83/0.99  --schedule                              none
% 3.83/0.99  --add_important_lit                     false
% 3.83/0.99  --prop_solver_per_cl                    1000
% 3.83/0.99  --min_unsat_core                        false
% 3.83/0.99  --soft_assumptions                      false
% 3.83/0.99  --soft_lemma_size                       3
% 3.83/0.99  --prop_impl_unit_size                   0
% 3.83/0.99  --prop_impl_unit                        []
% 3.83/0.99  --share_sel_clauses                     true
% 3.83/0.99  --reset_solvers                         false
% 3.83/0.99  --bc_imp_inh                            [conj_cone]
% 3.83/0.99  --conj_cone_tolerance                   3.
% 3.83/0.99  --extra_neg_conj                        none
% 3.83/0.99  --large_theory_mode                     true
% 3.83/0.99  --prolific_symb_bound                   200
% 3.83/0.99  --lt_threshold                          2000
% 3.83/0.99  --clause_weak_htbl                      true
% 3.83/0.99  --gc_record_bc_elim                     false
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing Options
% 3.83/0.99  
% 3.83/0.99  --preprocessing_flag                    true
% 3.83/0.99  --time_out_prep_mult                    0.1
% 3.83/0.99  --splitting_mode                        input
% 3.83/0.99  --splitting_grd                         true
% 3.83/0.99  --splitting_cvd                         false
% 3.83/0.99  --splitting_cvd_svl                     false
% 3.83/0.99  --splitting_nvd                         32
% 3.83/0.99  --sub_typing                            true
% 3.83/0.99  --prep_gs_sim                           false
% 3.83/0.99  --prep_unflatten                        true
% 3.83/0.99  --prep_res_sim                          true
% 3.83/0.99  --prep_upred                            true
% 3.83/0.99  --prep_sem_filter                       exhaustive
% 3.83/0.99  --prep_sem_filter_out                   false
% 3.83/0.99  --pred_elim                             false
% 3.83/0.99  --res_sim_input                         true
% 3.83/0.99  --eq_ax_congr_red                       true
% 3.83/0.99  --pure_diseq_elim                       true
% 3.83/0.99  --brand_transform                       false
% 3.83/0.99  --non_eq_to_eq                          false
% 3.83/0.99  --prep_def_merge                        true
% 3.83/0.99  --prep_def_merge_prop_impl              false
% 3.83/0.99  --prep_def_merge_mbd                    true
% 3.83/0.99  --prep_def_merge_tr_red                 false
% 3.83/0.99  --prep_def_merge_tr_cl                  false
% 3.83/0.99  --smt_preprocessing                     true
% 3.83/0.99  --smt_ac_axioms                         fast
% 3.83/0.99  --preprocessed_out                      false
% 3.83/0.99  --preprocessed_stats                    false
% 3.83/0.99  
% 3.83/0.99  ------ Abstraction refinement Options
% 3.83/0.99  
% 3.83/0.99  --abstr_ref                             []
% 3.83/0.99  --abstr_ref_prep                        false
% 3.83/0.99  --abstr_ref_until_sat                   false
% 3.83/0.99  --abstr_ref_sig_restrict                funpre
% 3.83/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/0.99  --abstr_ref_under                       []
% 3.83/0.99  
% 3.83/0.99  ------ SAT Options
% 3.83/0.99  
% 3.83/0.99  --sat_mode                              false
% 3.83/0.99  --sat_fm_restart_options                ""
% 3.83/0.99  --sat_gr_def                            false
% 3.83/0.99  --sat_epr_types                         true
% 3.83/0.99  --sat_non_cyclic_types                  false
% 3.83/0.99  --sat_finite_models                     false
% 3.83/0.99  --sat_fm_lemmas                         false
% 3.83/0.99  --sat_fm_prep                           false
% 3.83/0.99  --sat_fm_uc_incr                        true
% 3.83/0.99  --sat_out_model                         small
% 3.83/0.99  --sat_out_clauses                       false
% 3.83/0.99  
% 3.83/0.99  ------ QBF Options
% 3.83/0.99  
% 3.83/0.99  --qbf_mode                              false
% 3.83/0.99  --qbf_elim_univ                         false
% 3.83/0.99  --qbf_dom_inst                          none
% 3.83/0.99  --qbf_dom_pre_inst                      false
% 3.83/0.99  --qbf_sk_in                             false
% 3.83/0.99  --qbf_pred_elim                         true
% 3.83/0.99  --qbf_split                             512
% 3.83/0.99  
% 3.83/0.99  ------ BMC1 Options
% 3.83/0.99  
% 3.83/0.99  --bmc1_incremental                      false
% 3.83/0.99  --bmc1_axioms                           reachable_all
% 3.83/0.99  --bmc1_min_bound                        0
% 3.83/0.99  --bmc1_max_bound                        -1
% 3.83/0.99  --bmc1_max_bound_default                -1
% 3.83/0.99  --bmc1_symbol_reachability              true
% 3.83/0.99  --bmc1_property_lemmas                  false
% 3.83/0.99  --bmc1_k_induction                      false
% 3.83/0.99  --bmc1_non_equiv_states                 false
% 3.83/0.99  --bmc1_deadlock                         false
% 3.83/0.99  --bmc1_ucm                              false
% 3.83/0.99  --bmc1_add_unsat_core                   none
% 3.83/0.99  --bmc1_unsat_core_children              false
% 3.83/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/0.99  --bmc1_out_stat                         full
% 3.83/0.99  --bmc1_ground_init                      false
% 3.83/0.99  --bmc1_pre_inst_next_state              false
% 3.83/0.99  --bmc1_pre_inst_state                   false
% 3.83/0.99  --bmc1_pre_inst_reach_state             false
% 3.83/0.99  --bmc1_out_unsat_core                   false
% 3.83/0.99  --bmc1_aig_witness_out                  false
% 3.83/0.99  --bmc1_verbose                          false
% 3.83/0.99  --bmc1_dump_clauses_tptp                false
% 3.83/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.83/0.99  --bmc1_dump_file                        -
% 3.83/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.83/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.83/0.99  --bmc1_ucm_extend_mode                  1
% 3.83/0.99  --bmc1_ucm_init_mode                    2
% 3.83/0.99  --bmc1_ucm_cone_mode                    none
% 3.83/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.83/0.99  --bmc1_ucm_relax_model                  4
% 3.83/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.83/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/0.99  --bmc1_ucm_layered_model                none
% 3.83/0.99  --bmc1_ucm_max_lemma_size               10
% 3.83/0.99  
% 3.83/0.99  ------ AIG Options
% 3.83/0.99  
% 3.83/0.99  --aig_mode                              false
% 3.83/0.99  
% 3.83/0.99  ------ Instantiation Options
% 3.83/0.99  
% 3.83/0.99  --instantiation_flag                    true
% 3.83/0.99  --inst_sos_flag                         false
% 3.83/0.99  --inst_sos_phase                        true
% 3.83/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/0.99  --inst_lit_sel_side                     num_symb
% 3.83/0.99  --inst_solver_per_active                1400
% 3.83/0.99  --inst_solver_calls_frac                1.
% 3.83/0.99  --inst_passive_queue_type               priority_queues
% 3.83/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/0.99  --inst_passive_queues_freq              [25;2]
% 3.83/0.99  --inst_dismatching                      true
% 3.83/0.99  --inst_eager_unprocessed_to_passive     true
% 3.83/0.99  --inst_prop_sim_given                   true
% 3.83/0.99  --inst_prop_sim_new                     false
% 3.83/0.99  --inst_subs_new                         false
% 3.83/0.99  --inst_eq_res_simp                      false
% 3.83/0.99  --inst_subs_given                       false
% 3.83/0.99  --inst_orphan_elimination               true
% 3.83/0.99  --inst_learning_loop_flag               true
% 3.83/0.99  --inst_learning_start                   3000
% 3.83/0.99  --inst_learning_factor                  2
% 3.83/0.99  --inst_start_prop_sim_after_learn       3
% 3.83/0.99  --inst_sel_renew                        solver
% 3.83/0.99  --inst_lit_activity_flag                true
% 3.83/0.99  --inst_restr_to_given                   false
% 3.83/0.99  --inst_activity_threshold               500
% 3.83/0.99  --inst_out_proof                        true
% 3.83/0.99  
% 3.83/0.99  ------ Resolution Options
% 3.83/0.99  
% 3.83/0.99  --resolution_flag                       true
% 3.83/0.99  --res_lit_sel                           adaptive
% 3.83/0.99  --res_lit_sel_side                      none
% 3.83/0.99  --res_ordering                          kbo
% 3.83/0.99  --res_to_prop_solver                    active
% 3.83/0.99  --res_prop_simpl_new                    false
% 3.83/0.99  --res_prop_simpl_given                  true
% 3.83/0.99  --res_passive_queue_type                priority_queues
% 3.83/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/0.99  --res_passive_queues_freq               [15;5]
% 3.83/0.99  --res_forward_subs                      full
% 3.83/0.99  --res_backward_subs                     full
% 3.83/0.99  --res_forward_subs_resolution           true
% 3.83/0.99  --res_backward_subs_resolution          true
% 3.83/0.99  --res_orphan_elimination                true
% 3.83/0.99  --res_time_limit                        2.
% 3.83/0.99  --res_out_proof                         true
% 3.83/0.99  
% 3.83/0.99  ------ Superposition Options
% 3.83/0.99  
% 3.83/0.99  --superposition_flag                    true
% 3.83/0.99  --sup_passive_queue_type                priority_queues
% 3.83/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/0.99  --sup_passive_queues_freq               [1;4]
% 3.83/0.99  --demod_completeness_check              fast
% 3.83/0.99  --demod_use_ground                      true
% 3.83/0.99  --sup_to_prop_solver                    passive
% 3.83/0.99  --sup_prop_simpl_new                    true
% 3.83/0.99  --sup_prop_simpl_given                  true
% 3.83/0.99  --sup_fun_splitting                     false
% 3.83/0.99  --sup_smt_interval                      50000
% 3.83/0.99  
% 3.83/0.99  ------ Superposition Simplification Setup
% 3.83/0.99  
% 3.83/0.99  --sup_indices_passive                   []
% 3.83/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_full_bw                           [BwDemod]
% 3.83/0.99  --sup_immed_triv                        [TrivRules]
% 3.83/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_immed_bw_main                     []
% 3.83/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.83/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.83/0.99  
% 3.83/0.99  ------ Combination Options
% 3.83/0.99  
% 3.83/0.99  --comb_res_mult                         3
% 3.83/0.99  --comb_sup_mult                         2
% 3.83/0.99  --comb_inst_mult                        10
% 3.83/0.99  
% 3.83/0.99  ------ Debug Options
% 3.83/0.99  
% 3.83/0.99  --dbg_backtrace                         false
% 3.83/0.99  --dbg_dump_prop_clauses                 false
% 3.83/0.99  --dbg_dump_prop_clauses_file            -
% 3.83/0.99  --dbg_out_stat                          false
% 3.83/0.99  ------ Parsing...
% 3.83/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.83/0.99  ------ Proving...
% 3.83/0.99  ------ Problem Properties 
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  clauses                                 17
% 3.83/0.99  conjectures                             7
% 3.83/0.99  EPR                                     4
% 3.83/0.99  Horn                                    16
% 3.83/0.99  unary                                   6
% 3.83/0.99  binary                                  5
% 3.83/0.99  lits                                    51
% 3.83/0.99  lits eq                                 11
% 3.83/0.99  fd_pure                                 0
% 3.83/0.99  fd_pseudo                               0
% 3.83/0.99  fd_cond                                 0
% 3.83/0.99  fd_pseudo_cond                          0
% 3.83/0.99  AC symbols                              0
% 3.83/0.99  
% 3.83/0.99  ------ Input Options Time Limit: Unbounded
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  ------ 
% 3.83/0.99  Current options:
% 3.83/0.99  ------ 
% 3.83/0.99  
% 3.83/0.99  ------ Input Options
% 3.83/0.99  
% 3.83/0.99  --out_options                           all
% 3.83/0.99  --tptp_safe_out                         true
% 3.83/0.99  --problem_path                          ""
% 3.83/0.99  --include_path                          ""
% 3.83/0.99  --clausifier                            res/vclausify_rel
% 3.83/0.99  --clausifier_options                    --mode clausify
% 3.83/0.99  --stdin                                 false
% 3.83/0.99  --stats_out                             sel
% 3.83/0.99  
% 3.83/0.99  ------ General Options
% 3.83/0.99  
% 3.83/0.99  --fof                                   false
% 3.83/0.99  --time_out_real                         604.99
% 3.83/0.99  --time_out_virtual                      -1.
% 3.83/0.99  --symbol_type_check                     false
% 3.83/0.99  --clausify_out                          false
% 3.83/0.99  --sig_cnt_out                           false
% 3.83/0.99  --trig_cnt_out                          false
% 3.83/0.99  --trig_cnt_out_tolerance                1.
% 3.83/0.99  --trig_cnt_out_sk_spl                   false
% 3.83/0.99  --abstr_cl_out                          false
% 3.83/0.99  
% 3.83/0.99  ------ Global Options
% 3.83/0.99  
% 3.83/0.99  --schedule                              none
% 3.83/0.99  --add_important_lit                     false
% 3.83/0.99  --prop_solver_per_cl                    1000
% 3.83/0.99  --min_unsat_core                        false
% 3.83/0.99  --soft_assumptions                      false
% 3.83/0.99  --soft_lemma_size                       3
% 3.83/0.99  --prop_impl_unit_size                   0
% 3.83/0.99  --prop_impl_unit                        []
% 3.83/0.99  --share_sel_clauses                     true
% 3.83/0.99  --reset_solvers                         false
% 3.83/0.99  --bc_imp_inh                            [conj_cone]
% 3.83/0.99  --conj_cone_tolerance                   3.
% 3.83/0.99  --extra_neg_conj                        none
% 3.83/0.99  --large_theory_mode                     true
% 3.83/0.99  --prolific_symb_bound                   200
% 3.83/0.99  --lt_threshold                          2000
% 3.83/0.99  --clause_weak_htbl                      true
% 3.83/0.99  --gc_record_bc_elim                     false
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing Options
% 3.83/0.99  
% 3.83/0.99  --preprocessing_flag                    true
% 3.83/0.99  --time_out_prep_mult                    0.1
% 3.83/0.99  --splitting_mode                        input
% 3.83/0.99  --splitting_grd                         true
% 3.83/0.99  --splitting_cvd                         false
% 3.83/0.99  --splitting_cvd_svl                     false
% 3.83/0.99  --splitting_nvd                         32
% 3.83/0.99  --sub_typing                            true
% 3.83/0.99  --prep_gs_sim                           false
% 3.83/0.99  --prep_unflatten                        true
% 3.83/0.99  --prep_res_sim                          true
% 3.83/0.99  --prep_upred                            true
% 3.83/0.99  --prep_sem_filter                       exhaustive
% 3.83/0.99  --prep_sem_filter_out                   false
% 3.83/0.99  --pred_elim                             false
% 3.83/0.99  --res_sim_input                         true
% 3.83/0.99  --eq_ax_congr_red                       true
% 3.83/0.99  --pure_diseq_elim                       true
% 3.83/0.99  --brand_transform                       false
% 3.83/0.99  --non_eq_to_eq                          false
% 3.83/0.99  --prep_def_merge                        true
% 3.83/0.99  --prep_def_merge_prop_impl              false
% 3.83/0.99  --prep_def_merge_mbd                    true
% 3.83/0.99  --prep_def_merge_tr_red                 false
% 3.83/0.99  --prep_def_merge_tr_cl                  false
% 3.83/0.99  --smt_preprocessing                     true
% 3.83/0.99  --smt_ac_axioms                         fast
% 3.83/0.99  --preprocessed_out                      false
% 3.83/0.99  --preprocessed_stats                    false
% 3.83/0.99  
% 3.83/0.99  ------ Abstraction refinement Options
% 3.83/0.99  
% 3.83/0.99  --abstr_ref                             []
% 3.83/0.99  --abstr_ref_prep                        false
% 3.83/0.99  --abstr_ref_until_sat                   false
% 3.83/0.99  --abstr_ref_sig_restrict                funpre
% 3.83/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/0.99  --abstr_ref_under                       []
% 3.83/0.99  
% 3.83/0.99  ------ SAT Options
% 3.83/0.99  
% 3.83/0.99  --sat_mode                              false
% 3.83/0.99  --sat_fm_restart_options                ""
% 3.83/0.99  --sat_gr_def                            false
% 3.83/0.99  --sat_epr_types                         true
% 3.83/0.99  --sat_non_cyclic_types                  false
% 3.83/0.99  --sat_finite_models                     false
% 3.83/0.99  --sat_fm_lemmas                         false
% 3.83/0.99  --sat_fm_prep                           false
% 3.83/0.99  --sat_fm_uc_incr                        true
% 3.83/0.99  --sat_out_model                         small
% 3.83/0.99  --sat_out_clauses                       false
% 3.83/0.99  
% 3.83/0.99  ------ QBF Options
% 3.83/0.99  
% 3.83/0.99  --qbf_mode                              false
% 3.83/0.99  --qbf_elim_univ                         false
% 3.83/0.99  --qbf_dom_inst                          none
% 3.83/0.99  --qbf_dom_pre_inst                      false
% 3.83/0.99  --qbf_sk_in                             false
% 3.83/0.99  --qbf_pred_elim                         true
% 3.83/0.99  --qbf_split                             512
% 3.83/0.99  
% 3.83/0.99  ------ BMC1 Options
% 3.83/0.99  
% 3.83/0.99  --bmc1_incremental                      false
% 3.83/0.99  --bmc1_axioms                           reachable_all
% 3.83/0.99  --bmc1_min_bound                        0
% 3.83/0.99  --bmc1_max_bound                        -1
% 3.83/0.99  --bmc1_max_bound_default                -1
% 3.83/0.99  --bmc1_symbol_reachability              true
% 3.83/0.99  --bmc1_property_lemmas                  false
% 3.83/0.99  --bmc1_k_induction                      false
% 3.83/0.99  --bmc1_non_equiv_states                 false
% 3.83/0.99  --bmc1_deadlock                         false
% 3.83/0.99  --bmc1_ucm                              false
% 3.83/0.99  --bmc1_add_unsat_core                   none
% 3.83/0.99  --bmc1_unsat_core_children              false
% 3.83/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/0.99  --bmc1_out_stat                         full
% 3.83/0.99  --bmc1_ground_init                      false
% 3.83/0.99  --bmc1_pre_inst_next_state              false
% 3.83/0.99  --bmc1_pre_inst_state                   false
% 3.83/0.99  --bmc1_pre_inst_reach_state             false
% 3.83/0.99  --bmc1_out_unsat_core                   false
% 3.83/0.99  --bmc1_aig_witness_out                  false
% 3.83/0.99  --bmc1_verbose                          false
% 3.83/0.99  --bmc1_dump_clauses_tptp                false
% 3.83/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.83/0.99  --bmc1_dump_file                        -
% 3.83/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.83/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.83/0.99  --bmc1_ucm_extend_mode                  1
% 3.83/0.99  --bmc1_ucm_init_mode                    2
% 3.83/0.99  --bmc1_ucm_cone_mode                    none
% 3.83/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.83/0.99  --bmc1_ucm_relax_model                  4
% 3.83/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.83/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/0.99  --bmc1_ucm_layered_model                none
% 3.83/0.99  --bmc1_ucm_max_lemma_size               10
% 3.83/0.99  
% 3.83/0.99  ------ AIG Options
% 3.83/0.99  
% 3.83/0.99  --aig_mode                              false
% 3.83/0.99  
% 3.83/0.99  ------ Instantiation Options
% 3.83/0.99  
% 3.83/0.99  --instantiation_flag                    true
% 3.83/0.99  --inst_sos_flag                         false
% 3.83/0.99  --inst_sos_phase                        true
% 3.83/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/0.99  --inst_lit_sel_side                     num_symb
% 3.83/0.99  --inst_solver_per_active                1400
% 3.83/0.99  --inst_solver_calls_frac                1.
% 3.83/0.99  --inst_passive_queue_type               priority_queues
% 3.83/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/0.99  --inst_passive_queues_freq              [25;2]
% 3.83/0.99  --inst_dismatching                      true
% 3.83/0.99  --inst_eager_unprocessed_to_passive     true
% 3.83/0.99  --inst_prop_sim_given                   true
% 3.83/0.99  --inst_prop_sim_new                     false
% 3.83/0.99  --inst_subs_new                         false
% 3.83/0.99  --inst_eq_res_simp                      false
% 3.83/0.99  --inst_subs_given                       false
% 3.83/0.99  --inst_orphan_elimination               true
% 3.83/0.99  --inst_learning_loop_flag               true
% 3.83/0.99  --inst_learning_start                   3000
% 3.83/0.99  --inst_learning_factor                  2
% 3.83/0.99  --inst_start_prop_sim_after_learn       3
% 3.83/0.99  --inst_sel_renew                        solver
% 3.83/0.99  --inst_lit_activity_flag                true
% 3.83/0.99  --inst_restr_to_given                   false
% 3.83/0.99  --inst_activity_threshold               500
% 3.83/0.99  --inst_out_proof                        true
% 3.83/0.99  
% 3.83/0.99  ------ Resolution Options
% 3.83/0.99  
% 3.83/0.99  --resolution_flag                       true
% 3.83/0.99  --res_lit_sel                           adaptive
% 3.83/0.99  --res_lit_sel_side                      none
% 3.83/0.99  --res_ordering                          kbo
% 3.83/0.99  --res_to_prop_solver                    active
% 3.83/0.99  --res_prop_simpl_new                    false
% 3.83/0.99  --res_prop_simpl_given                  true
% 3.83/0.99  --res_passive_queue_type                priority_queues
% 3.83/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/0.99  --res_passive_queues_freq               [15;5]
% 3.83/0.99  --res_forward_subs                      full
% 3.83/0.99  --res_backward_subs                     full
% 3.83/0.99  --res_forward_subs_resolution           true
% 3.83/0.99  --res_backward_subs_resolution          true
% 3.83/0.99  --res_orphan_elimination                true
% 3.83/0.99  --res_time_limit                        2.
% 3.83/0.99  --res_out_proof                         true
% 3.83/0.99  
% 3.83/0.99  ------ Superposition Options
% 3.83/0.99  
% 3.83/0.99  --superposition_flag                    true
% 3.83/0.99  --sup_passive_queue_type                priority_queues
% 3.83/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/0.99  --sup_passive_queues_freq               [1;4]
% 3.83/0.99  --demod_completeness_check              fast
% 3.83/0.99  --demod_use_ground                      true
% 3.83/0.99  --sup_to_prop_solver                    passive
% 3.83/0.99  --sup_prop_simpl_new                    true
% 3.83/0.99  --sup_prop_simpl_given                  true
% 3.83/0.99  --sup_fun_splitting                     false
% 3.83/0.99  --sup_smt_interval                      50000
% 3.83/0.99  
% 3.83/0.99  ------ Superposition Simplification Setup
% 3.83/0.99  
% 3.83/0.99  --sup_indices_passive                   []
% 3.83/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_full_bw                           [BwDemod]
% 3.83/0.99  --sup_immed_triv                        [TrivRules]
% 3.83/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_immed_bw_main                     []
% 3.83/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.83/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.83/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.83/0.99  
% 3.83/0.99  ------ Combination Options
% 3.83/0.99  
% 3.83/0.99  --comb_res_mult                         3
% 3.83/0.99  --comb_sup_mult                         2
% 3.83/0.99  --comb_inst_mult                        10
% 3.83/0.99  
% 3.83/0.99  ------ Debug Options
% 3.83/0.99  
% 3.83/0.99  --dbg_backtrace                         false
% 3.83/0.99  --dbg_dump_prop_clauses                 false
% 3.83/0.99  --dbg_dump_prop_clauses_file            -
% 3.83/0.99  --dbg_out_stat                          false
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  ------ Proving...
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  % SZS status Theorem for theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  fof(f8,conjecture,(
% 3.83/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X0) = k1_relat_1(X1)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f9,negated_conjecture,(
% 3.83/0.99    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X0) = k1_relat_1(X1)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 3.83/0.99    inference(negated_conjecture,[],[f8])).
% 3.83/0.99  
% 3.83/0.99  fof(f17,plain,(
% 3.83/0.99    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.83/0.99    inference(ennf_transformation,[],[f9])).
% 3.83/0.99  
% 3.83/0.99  fof(f18,plain,(
% 3.83/0.99    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.83/0.99    inference(flattening,[],[f17])).
% 3.83/0.99  
% 3.83/0.99  fof(f27,plain,(
% 3.83/0.99    ( ! [X0,X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => (k7_relat_1(X0,sK3) != k7_relat_1(X1,sK3) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,sK3)) & k1_relat_1(X0) = k1_relat_1(X1))) )),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f26,plain,(
% 3.83/0.99    ( ! [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK2,X2) != k7_relat_1(X0,X2) & ! [X3] : (k1_funct_1(sK2,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK2) = k1_relat_1(X0)) & v1_funct_1(sK2) & v1_relat_1(sK2))) )),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f25,plain,(
% 3.83/0.99    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(sK1,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(sK1,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK1) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f28,plain,(
% 3.83/0.99    ((k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) & ! [X3] : (k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) | ~r2_hidden(X3,sK3)) & k1_relat_1(sK1) = k1_relat_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 3.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f27,f26,f25])).
% 3.83/0.99  
% 3.83/0.99  fof(f40,plain,(
% 3.83/0.99    v1_relat_1(sK1)),
% 3.83/0.99    inference(cnf_transformation,[],[f28])).
% 3.83/0.99  
% 3.83/0.99  fof(f5,axiom,(
% 3.83/0.99    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f13,plain,(
% 3.83/0.99    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.83/0.99    inference(ennf_transformation,[],[f5])).
% 3.83/0.99  
% 3.83/0.99  fof(f35,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f13])).
% 3.83/0.99  
% 3.83/0.99  fof(f1,axiom,(
% 3.83/0.99    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f29,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f1])).
% 3.83/0.99  
% 3.83/0.99  fof(f48,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.83/0.99    inference(definition_unfolding,[],[f35,f29])).
% 3.83/0.99  
% 3.83/0.99  fof(f2,axiom,(
% 3.83/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f10,plain,(
% 3.83/0.99    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.83/0.99    inference(ennf_transformation,[],[f2])).
% 3.83/0.99  
% 3.83/0.99  fof(f30,plain,(
% 3.83/0.99    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f10])).
% 3.83/0.99  
% 3.83/0.99  fof(f47,plain,(
% 3.83/0.99    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X2)) )),
% 3.83/0.99    inference(definition_unfolding,[],[f30,f29])).
% 3.83/0.99  
% 3.83/0.99  fof(f6,axiom,(
% 3.83/0.99    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f14,plain,(
% 3.83/0.99    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 3.83/0.99    inference(ennf_transformation,[],[f6])).
% 3.83/0.99  
% 3.83/0.99  fof(f36,plain,(
% 3.83/0.99    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f14])).
% 3.83/0.99  
% 3.83/0.99  fof(f44,plain,(
% 3.83/0.99    k1_relat_1(sK1) = k1_relat_1(sK2)),
% 3.83/0.99    inference(cnf_transformation,[],[f28])).
% 3.83/0.99  
% 3.83/0.99  fof(f4,axiom,(
% 3.83/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f12,plain,(
% 3.83/0.99    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.83/0.99    inference(ennf_transformation,[],[f4])).
% 3.83/0.99  
% 3.83/0.99  fof(f34,plain,(
% 3.83/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f12])).
% 3.83/0.99  
% 3.83/0.99  fof(f7,axiom,(
% 3.83/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f15,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | (~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.83/0.99    inference(ennf_transformation,[],[f7])).
% 3.83/0.99  
% 3.83/0.99  fof(f16,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.83/0.99    inference(flattening,[],[f15])).
% 3.83/0.99  
% 3.83/0.99  fof(f21,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.83/0.99    inference(nnf_transformation,[],[f16])).
% 3.83/0.99  
% 3.83/0.99  fof(f22,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.83/0.99    inference(rectify,[],[f21])).
% 3.83/0.99  
% 3.83/0.99  fof(f23,plain,(
% 3.83/0.99    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2)))),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f24,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | (k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 3.83/0.99  
% 3.83/0.99  fof(f38,plain,(
% 3.83/0.99    ( ! [X2,X0,X1] : (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f24])).
% 3.83/0.99  
% 3.83/0.99  fof(f42,plain,(
% 3.83/0.99    v1_relat_1(sK2)),
% 3.83/0.99    inference(cnf_transformation,[],[f28])).
% 3.83/0.99  
% 3.83/0.99  fof(f3,axiom,(
% 3.83/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f11,plain,(
% 3.83/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 3.83/0.99    inference(ennf_transformation,[],[f3])).
% 3.83/0.99  
% 3.83/0.99  fof(f19,plain,(
% 3.83/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 3.83/0.99    inference(nnf_transformation,[],[f11])).
% 3.83/0.99  
% 3.83/0.99  fof(f20,plain,(
% 3.83/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 3.83/0.99    inference(flattening,[],[f19])).
% 3.83/0.99  
% 3.83/0.99  fof(f31,plain,(
% 3.83/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f20])).
% 3.83/0.99  
% 3.83/0.99  fof(f45,plain,(
% 3.83/0.99    ( ! [X3] : (k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) | ~r2_hidden(X3,sK3)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f28])).
% 3.83/0.99  
% 3.83/0.99  fof(f41,plain,(
% 3.83/0.99    v1_funct_1(sK1)),
% 3.83/0.99    inference(cnf_transformation,[],[f28])).
% 3.83/0.99  
% 3.83/0.99  fof(f43,plain,(
% 3.83/0.99    v1_funct_1(sK2)),
% 3.83/0.99    inference(cnf_transformation,[],[f28])).
% 3.83/0.99  
% 3.83/0.99  fof(f39,plain,(
% 3.83/0.99    ( ! [X2,X0,X1] : (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2)) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f24])).
% 3.83/0.99  
% 3.83/0.99  fof(f46,plain,(
% 3.83/0.99    k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3)),
% 3.83/0.99    inference(cnf_transformation,[],[f28])).
% 3.83/0.99  
% 3.83/0.99  cnf(c_16,negated_conjecture,
% 3.83/0.99      ( v1_relat_1(sK1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_146,negated_conjecture,
% 3.83/0.99      ( v1_relat_1(sK1) ),
% 3.83/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_485,plain,
% 3.83/0.99      ( v1_relat_1(sK1) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_146]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_5,plain,
% 3.83/0.99      ( ~ v1_relat_1(X0)
% 3.83/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 3.83/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_157,plain,
% 3.83/0.99      ( ~ v1_relat_1(X0_41)
% 3.83/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(X0_41),X0_42)) = k1_relat_1(k7_relat_1(X0_41,X0_42)) ),
% 3.83/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_476,plain,
% 3.83/0.99      ( k1_setfam_1(k2_tarski(k1_relat_1(X0_41),X0_42)) = k1_relat_1(k7_relat_1(X0_41,X0_42))
% 3.83/0.99      | v1_relat_1(X0_41) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_157]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1121,plain,
% 3.83/0.99      ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0_42)) = k1_relat_1(k7_relat_1(sK1,X0_42)) ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_485,c_476]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_0,plain,
% 3.83/0.99      ( ~ v1_relat_1(X0)
% 3.83/0.99      | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 3.83/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_162,plain,
% 3.83/0.99      ( ~ v1_relat_1(X0_41)
% 3.83/0.99      | k7_relat_1(X0_41,k1_setfam_1(k2_tarski(X0_42,X1_42))) = k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42) ),
% 3.83/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_471,plain,
% 3.83/0.99      ( k7_relat_1(X0_41,k1_setfam_1(k2_tarski(X0_42,X1_42))) = k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42)
% 3.83/0.99      | v1_relat_1(X0_41) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_162]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_722,plain,
% 3.83/0.99      ( k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0_42,X1_42))) = k7_relat_1(k7_relat_1(sK1,X0_42),X1_42) ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_485,c_471]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2590,plain,
% 3.83/0.99      ( k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0_42) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0_42))) ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1121,c_722]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6,plain,
% 3.83/0.99      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 3.83/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_156,plain,
% 3.83/0.99      ( ~ v1_relat_1(X0_41)
% 3.83/0.99      | k7_relat_1(X0_41,k1_relat_1(X0_41)) = X0_41 ),
% 3.83/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_477,plain,
% 3.83/0.99      ( k7_relat_1(X0_41,k1_relat_1(X0_41)) = X0_41
% 3.83/0.99      | v1_relat_1(X0_41) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_156]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_728,plain,
% 3.83/0.99      ( k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_485,c_477]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2638,plain,
% 3.83/0.99      ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0_42))) = k7_relat_1(sK1,X0_42) ),
% 3.83/0.99      inference(light_normalisation,[status(thm)],[c_2590,c_728]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_12,negated_conjecture,
% 3.83/0.99      ( k1_relat_1(sK1) = k1_relat_1(sK2) ),
% 3.83/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_150,negated_conjecture,
% 3.83/0.99      ( k1_relat_1(sK1) = k1_relat_1(sK2) ),
% 3.83/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_4,plain,
% 3.83/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
% 3.83/0.99      | ~ v1_relat_1(X0) ),
% 3.83/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_158,plain,
% 3.83/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0_41,X0_42)),k1_relat_1(X0_41))
% 3.83/0.99      | ~ v1_relat_1(X0_41) ),
% 3.83/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_475,plain,
% 3.83/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0_41,X0_42)),k1_relat_1(X0_41)) = iProver_top
% 3.83/0.99      | v1_relat_1(X0_41) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_158]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_8,plain,
% 3.83/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.83/0.99      | ~ r1_tarski(X0,k1_relat_1(X2))
% 3.83/0.99      | r2_hidden(sK0(X2,X1,X0),X0)
% 3.83/0.99      | ~ v1_funct_1(X1)
% 3.83/0.99      | ~ v1_funct_1(X2)
% 3.83/0.99      | ~ v1_relat_1(X1)
% 3.83/0.99      | ~ v1_relat_1(X2)
% 3.83/0.99      | k7_relat_1(X1,X0) = k7_relat_1(X2,X0) ),
% 3.83/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_154,plain,
% 3.83/0.99      ( ~ r1_tarski(X0_42,k1_relat_1(X0_41))
% 3.83/0.99      | ~ r1_tarski(X0_42,k1_relat_1(X1_41))
% 3.83/0.99      | r2_hidden(sK0(X0_41,X1_41,X0_42),X0_42)
% 3.83/0.99      | ~ v1_funct_1(X0_41)
% 3.83/0.99      | ~ v1_funct_1(X1_41)
% 3.83/0.99      | ~ v1_relat_1(X0_41)
% 3.83/0.99      | ~ v1_relat_1(X1_41)
% 3.83/0.99      | k7_relat_1(X1_41,X0_42) = k7_relat_1(X0_41,X0_42) ),
% 3.83/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_479,plain,
% 3.83/0.99      ( k7_relat_1(X0_41,X0_42) = k7_relat_1(X1_41,X0_42)
% 3.83/0.99      | r1_tarski(X0_42,k1_relat_1(X1_41)) != iProver_top
% 3.83/0.99      | r1_tarski(X0_42,k1_relat_1(X0_41)) != iProver_top
% 3.83/0.99      | r2_hidden(sK0(X1_41,X0_41,X0_42),X0_42) = iProver_top
% 3.83/0.99      | v1_funct_1(X1_41) != iProver_top
% 3.83/0.99      | v1_funct_1(X0_41) != iProver_top
% 3.83/0.99      | v1_relat_1(X1_41) != iProver_top
% 3.83/0.99      | v1_relat_1(X0_41) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_154]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_14,negated_conjecture,
% 3.83/0.99      ( v1_relat_1(sK2) ),
% 3.83/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_148,negated_conjecture,
% 3.83/0.99      ( v1_relat_1(sK2) ),
% 3.83/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_483,plain,
% 3.83/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_148]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1120,plain,
% 3.83/0.99      ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0_42)) = k1_relat_1(k7_relat_1(sK2,X0_42)) ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_483,c_476]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1125,plain,
% 3.83/0.99      ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0_42)) = k1_relat_1(k7_relat_1(sK2,X0_42)) ),
% 3.83/0.99      inference(light_normalisation,[status(thm)],[c_1120,c_150]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1767,plain,
% 3.83/0.99      ( k1_relat_1(k7_relat_1(sK1,X0_42)) = k1_relat_1(k7_relat_1(sK2,X0_42)) ),
% 3.83/0.99      inference(demodulation,[status(thm)],[c_1121,c_1125]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_3,plain,
% 3.83/0.99      ( r2_hidden(X0,X1)
% 3.83/0.99      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 3.83/0.99      | ~ v1_relat_1(X2) ),
% 3.83/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_159,plain,
% 3.83/0.99      ( r2_hidden(X0_43,X0_42)
% 3.83/0.99      | ~ r2_hidden(X0_43,k1_relat_1(k7_relat_1(X0_41,X0_42)))
% 3.83/0.99      | ~ v1_relat_1(X0_41) ),
% 3.83/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_474,plain,
% 3.83/0.99      ( r2_hidden(X0_43,X0_42) = iProver_top
% 3.83/0.99      | r2_hidden(X0_43,k1_relat_1(k7_relat_1(X0_41,X0_42))) != iProver_top
% 3.83/0.99      | v1_relat_1(X0_41) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_159]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1918,plain,
% 3.83/0.99      ( r2_hidden(X0_43,X0_42) = iProver_top
% 3.83/0.99      | r2_hidden(X0_43,k1_relat_1(k7_relat_1(sK1,X0_42))) != iProver_top
% 3.83/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1767,c_474]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_19,plain,
% 3.83/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_3507,plain,
% 3.83/0.99      ( r2_hidden(X0_43,k1_relat_1(k7_relat_1(sK1,X0_42))) != iProver_top
% 3.83/0.99      | r2_hidden(X0_43,X0_42) = iProver_top ),
% 3.83/0.99      inference(global_propositional_subsumption,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_1918,c_19]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_3508,plain,
% 3.83/0.99      ( r2_hidden(X0_43,X0_42) = iProver_top
% 3.83/0.99      | r2_hidden(X0_43,k1_relat_1(k7_relat_1(sK1,X0_42))) != iProver_top ),
% 3.83/0.99      inference(renaming,[status(thm)],[c_3507]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_3515,plain,
% 3.83/0.99      ( k7_relat_1(X0_41,k1_relat_1(k7_relat_1(sK1,X0_42))) = k7_relat_1(X1_41,k1_relat_1(k7_relat_1(sK1,X0_42)))
% 3.83/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0_42)),k1_relat_1(X0_41)) != iProver_top
% 3.83/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK1,X0_42)),k1_relat_1(X1_41)) != iProver_top
% 3.83/0.99      | r2_hidden(sK0(X0_41,X1_41,k1_relat_1(k7_relat_1(sK1,X0_42))),X0_42) = iProver_top
% 3.83/0.99      | v1_funct_1(X1_41) != iProver_top
% 3.83/0.99      | v1_funct_1(X0_41) != iProver_top
% 3.83/0.99      | v1_relat_1(X1_41) != iProver_top
% 3.83/0.99      | v1_relat_1(X0_41) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_479,c_3508]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_11,negated_conjecture,
% 3.83/0.99      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ),
% 3.83/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_151,negated_conjecture,
% 3.83/0.99      ( ~ r2_hidden(X0_43,sK3)
% 3.83/0.99      | k1_funct_1(sK1,X0_43) = k1_funct_1(sK2,X0_43) ),
% 3.83/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_481,plain,
% 3.83/0.99      ( k1_funct_1(sK1,X0_43) = k1_funct_1(sK2,X0_43)
% 3.83/0.99      | r2_hidden(X0_43,sK3) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_151]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_4808,plain,
% 3.83/0.99      ( k1_funct_1(sK2,sK0(X0_41,X1_41,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(X0_41,X1_41,k1_relat_1(k7_relat_1(sK1,sK3))))
% 3.83/0.99      | k7_relat_1(X1_41,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(X0_41,k1_relat_1(k7_relat_1(sK1,sK3)))
% 3.83/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(X0_41)) != iProver_top
% 3.83/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(X1_41)) != iProver_top
% 3.83/0.99      | v1_funct_1(X0_41) != iProver_top
% 3.83/0.99      | v1_funct_1(X1_41) != iProver_top
% 3.83/0.99      | v1_relat_1(X0_41) != iProver_top
% 3.83/0.99      | v1_relat_1(X1_41) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_3515,c_481]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_5969,plain,
% 3.83/0.99      ( k1_funct_1(sK1,sK0(sK1,X0_41,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK2,sK0(sK1,X0_41,k1_relat_1(k7_relat_1(sK1,sK3))))
% 3.83/0.99      | k7_relat_1(X0_41,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
% 3.83/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(X0_41)) != iProver_top
% 3.83/0.99      | v1_funct_1(X0_41) != iProver_top
% 3.83/0.99      | v1_funct_1(sK1) != iProver_top
% 3.83/0.99      | v1_relat_1(X0_41) != iProver_top
% 3.83/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_475,c_4808]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_17,plain,
% 3.83/0.99      ( v1_relat_1(sK1) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_15,negated_conjecture,
% 3.83/0.99      ( v1_funct_1(sK1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_18,plain,
% 3.83/0.99      ( v1_funct_1(sK1) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6030,plain,
% 3.83/0.99      ( v1_relat_1(X0_41) != iProver_top
% 3.83/0.99      | k1_funct_1(sK1,sK0(sK1,X0_41,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK2,sK0(sK1,X0_41,k1_relat_1(k7_relat_1(sK1,sK3))))
% 3.83/0.99      | k7_relat_1(X0_41,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
% 3.83/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(X0_41)) != iProver_top
% 3.83/0.99      | v1_funct_1(X0_41) != iProver_top ),
% 3.83/0.99      inference(global_propositional_subsumption,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_5969,c_17,c_18]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6031,plain,
% 3.83/0.99      ( k1_funct_1(sK1,sK0(sK1,X0_41,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK2,sK0(sK1,X0_41,k1_relat_1(k7_relat_1(sK1,sK3))))
% 3.83/0.99      | k7_relat_1(X0_41,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
% 3.83/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(X0_41)) != iProver_top
% 3.83/0.99      | v1_funct_1(X0_41) != iProver_top
% 3.83/0.99      | v1_relat_1(X0_41) != iProver_top ),
% 3.83/0.99      inference(renaming,[status(thm)],[c_6030]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6041,plain,
% 3.83/0.99      ( k1_funct_1(sK2,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3))))
% 3.83/0.99      | k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
% 3.83/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
% 3.83/0.99      | v1_funct_1(sK2) != iProver_top
% 3.83/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_150,c_6031]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_671,plain,
% 3.83/0.99      ( k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0_42,X1_42))) = k7_relat_1(k7_relat_1(sK2,X0_42),X1_42) ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_483,c_471]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1966,plain,
% 3.83/0.99      ( k7_relat_1(k7_relat_1(sK2,k1_relat_1(sK1)),X0_42) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,X0_42))) ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1121,c_671]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_727,plain,
% 3.83/0.99      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_483,c_477]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_732,plain,
% 3.83/0.99      ( k7_relat_1(sK2,k1_relat_1(sK1)) = sK2 ),
% 3.83/0.99      inference(light_normalisation,[status(thm)],[c_727,c_150]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2023,plain,
% 3.83/0.99      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,X0_42))) = k7_relat_1(sK2,X0_42) ),
% 3.83/0.99      inference(light_normalisation,[status(thm)],[c_1966,c_732]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6058,plain,
% 3.83/0.99      ( k1_funct_1(sK2,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3))))
% 3.83/0.99      | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK2,sK3)
% 3.83/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
% 3.83/0.99      | v1_funct_1(sK2) != iProver_top
% 3.83/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.83/0.99      inference(demodulation,[status(thm)],[c_6041,c_2023]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_13,negated_conjecture,
% 3.83/0.99      ( v1_funct_1(sK2) ),
% 3.83/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_209,plain,
% 3.83/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1))
% 3.83/0.99      | ~ v1_relat_1(sK1) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_158]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6067,plain,
% 3.83/0.99      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1))
% 3.83/0.99      | ~ v1_funct_1(sK2)
% 3.83/0.99      | ~ v1_relat_1(sK2)
% 3.83/0.99      | k1_funct_1(sK2,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3))))
% 3.83/0.99      | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK2,sK3) ),
% 3.83/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6058]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6502,plain,
% 3.83/0.99      ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK2,sK3)
% 3.83/0.99      | k1_funct_1(sK2,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3)))) ),
% 3.83/0.99      inference(global_propositional_subsumption,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_6058,c_16,c_14,c_13,c_209,c_6067]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6503,plain,
% 3.83/0.99      ( k1_funct_1(sK2,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3)))) = k1_funct_1(sK1,sK0(sK1,sK2,k1_relat_1(k7_relat_1(sK1,sK3))))
% 3.83/0.99      | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK2,sK3) ),
% 3.83/0.99      inference(renaming,[status(thm)],[c_6502]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_7,plain,
% 3.83/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.83/0.99      | ~ r1_tarski(X0,k1_relat_1(X2))
% 3.83/0.99      | ~ v1_funct_1(X1)
% 3.83/0.99      | ~ v1_funct_1(X2)
% 3.83/0.99      | ~ v1_relat_1(X1)
% 3.83/0.99      | ~ v1_relat_1(X2)
% 3.83/0.99      | k1_funct_1(X1,sK0(X2,X1,X0)) != k1_funct_1(X2,sK0(X2,X1,X0))
% 3.83/0.99      | k7_relat_1(X1,X0) = k7_relat_1(X2,X0) ),
% 3.83/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_155,plain,
% 3.83/0.99      ( ~ r1_tarski(X0_42,k1_relat_1(X0_41))
% 3.83/0.99      | ~ r1_tarski(X0_42,k1_relat_1(X1_41))
% 3.83/0.99      | ~ v1_funct_1(X0_41)
% 3.83/0.99      | ~ v1_funct_1(X1_41)
% 3.83/0.99      | ~ v1_relat_1(X0_41)
% 3.83/0.99      | ~ v1_relat_1(X1_41)
% 3.83/0.99      | k1_funct_1(X1_41,sK0(X0_41,X1_41,X0_42)) != k1_funct_1(X0_41,sK0(X0_41,X1_41,X0_42))
% 3.83/0.99      | k7_relat_1(X1_41,X0_42) = k7_relat_1(X0_41,X0_42) ),
% 3.83/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_478,plain,
% 3.83/0.99      ( k1_funct_1(X0_41,sK0(X1_41,X0_41,X0_42)) != k1_funct_1(X1_41,sK0(X1_41,X0_41,X0_42))
% 3.83/0.99      | k7_relat_1(X0_41,X0_42) = k7_relat_1(X1_41,X0_42)
% 3.83/0.99      | r1_tarski(X0_42,k1_relat_1(X1_41)) != iProver_top
% 3.83/0.99      | r1_tarski(X0_42,k1_relat_1(X0_41)) != iProver_top
% 3.83/0.99      | v1_funct_1(X1_41) != iProver_top
% 3.83/0.99      | v1_funct_1(X0_41) != iProver_top
% 3.83/0.99      | v1_relat_1(X1_41) != iProver_top
% 3.83/0.99      | v1_relat_1(X0_41) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_155]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6506,plain,
% 3.83/0.99      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
% 3.83/0.99      | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK2,sK3)
% 3.83/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK2)) != iProver_top
% 3.83/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
% 3.83/0.99      | v1_funct_1(sK2) != iProver_top
% 3.83/0.99      | v1_funct_1(sK1) != iProver_top
% 3.83/0.99      | v1_relat_1(sK2) != iProver_top
% 3.83/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_6503,c_478]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6507,plain,
% 3.83/0.99      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3)))
% 3.83/0.99      | k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK2,sK3)
% 3.83/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
% 3.83/0.99      | v1_funct_1(sK2) != iProver_top
% 3.83/0.99      | v1_funct_1(sK1) != iProver_top
% 3.83/0.99      | v1_relat_1(sK2) != iProver_top
% 3.83/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.83/0.99      inference(light_normalisation,[status(thm)],[c_6506,c_150]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6508,plain,
% 3.83/0.99      ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK2,sK3)
% 3.83/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) != iProver_top
% 3.83/0.99      | v1_funct_1(sK2) != iProver_top
% 3.83/0.99      | v1_funct_1(sK1) != iProver_top
% 3.83/0.99      | v1_relat_1(sK2) != iProver_top
% 3.83/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.83/0.99      inference(demodulation,[status(thm)],[c_6507,c_2023]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_20,plain,
% 3.83/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_208,plain,
% 3.83/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0_41,X0_42)),k1_relat_1(X0_41)) = iProver_top
% 3.83/0.99      | v1_relat_1(X0_41) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_158]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_210,plain,
% 3.83/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,sK3)),k1_relat_1(sK1)) = iProver_top
% 3.83/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_208]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6511,plain,
% 3.83/0.99      ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK3))) = k7_relat_1(sK2,sK3) ),
% 3.83/0.99      inference(global_propositional_subsumption,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_6508,c_17,c_18,c_19,c_20,c_210]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_12954,plain,
% 3.83/0.99      ( k7_relat_1(sK2,sK3) = k7_relat_1(sK1,sK3) ),
% 3.83/0.99      inference(demodulation,[status(thm)],[c_2638,c_6511]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_169,plain,
% 3.83/0.99      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 3.83/0.99      theory(equality) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_658,plain,
% 3.83/0.99      ( k7_relat_1(sK2,sK3) != X0_41
% 3.83/0.99      | k7_relat_1(sK1,sK3) != X0_41
% 3.83/0.99      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_169]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_687,plain,
% 3.83/0.99      ( k7_relat_1(sK2,sK3) != k7_relat_1(X0_41,sK3)
% 3.83/0.99      | k7_relat_1(sK1,sK3) != k7_relat_1(X0_41,sK3)
% 3.83/0.99      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_658]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_690,plain,
% 3.83/0.99      ( k7_relat_1(sK2,sK3) != k7_relat_1(sK1,sK3)
% 3.83/0.99      | k7_relat_1(sK1,sK3) = k7_relat_1(sK2,sK3)
% 3.83/0.99      | k7_relat_1(sK1,sK3) != k7_relat_1(sK1,sK3) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_687]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_10,negated_conjecture,
% 3.83/0.99      ( k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
% 3.83/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_152,negated_conjecture,
% 3.83/0.99      ( k7_relat_1(sK1,sK3) != k7_relat_1(sK2,sK3) ),
% 3.83/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_165,plain,( X0_42 = X0_42 ),theory(equality) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_192,plain,
% 3.83/0.99      ( sK3 = sK3 ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_165]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_164,plain,( X0_41 = X0_41 ),theory(equality) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_191,plain,
% 3.83/0.99      ( sK1 = sK1 ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_164]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_172,plain,
% 3.83/0.99      ( X0_42 != X1_42
% 3.83/0.99      | X0_41 != X1_41
% 3.83/0.99      | k7_relat_1(X0_41,X0_42) = k7_relat_1(X1_41,X1_42) ),
% 3.83/0.99      theory(equality) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_181,plain,
% 3.83/0.99      ( sK3 != sK3
% 3.83/0.99      | k7_relat_1(sK1,sK3) = k7_relat_1(sK1,sK3)
% 3.83/0.99      | sK1 != sK1 ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_172]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(contradiction,plain,
% 3.83/0.99      ( $false ),
% 3.83/0.99      inference(minisat,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_12954,c_690,c_152,c_192,c_191,c_181]) ).
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  ------                               Statistics
% 3.83/0.99  
% 3.83/0.99  ------ Selected
% 3.83/0.99  
% 3.83/0.99  total_time:                             0.384
% 3.83/0.99  
%------------------------------------------------------------------------------
