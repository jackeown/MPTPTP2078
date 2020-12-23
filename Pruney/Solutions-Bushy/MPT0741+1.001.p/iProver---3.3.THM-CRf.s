%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0741+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:01 EST 2020

% Result     : Theorem 0.83s
% Output     : CNFRefutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 109 expanded)
%              Number of clauses        :   27 (  28 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  231 ( 567 expanded)
%              Number of equality atoms :   22 (  62 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) ) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) ) )
       => v3_ordinal1(X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(X0)
      & ! [X1] :
          ( ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(X0)
        & ! [X1] :
            ( ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) )
            | ~ r2_hidden(X1,X0) ) )
   => ( ~ v3_ordinal1(sK3)
      & ! [X1] :
          ( ( r1_tarski(X1,sK3)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ v3_ordinal1(sK3)
    & ! [X1] :
        ( ( r1_tarski(X1,sK3)
          & v3_ordinal1(X1) )
        | ~ r2_hidden(X1,sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f22])).

fof(f37,plain,(
    ! [X1] :
      ( v3_ordinal1(X1)
      | ~ r2_hidden(X1,sK3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK0(X0),X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK0(X0),X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f26,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK3)
      | ~ r2_hidden(X1,sK3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1,X2] :
            ( r2_hidden(X2,X1)
            | X1 = X2
            | r2_hidden(X1,X2)
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK2(X0),sK1(X0))
        & sK1(X0) != sK2(X0)
        & ~ r2_hidden(sK1(X0),sK2(X0))
        & r2_hidden(sK2(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ( ~ r2_hidden(sK2(X0),sK1(X0))
          & sK1(X0) != sK2(X0)
          & ~ r2_hidden(sK1(X0),sK2(X0))
          & r2_hidden(sK2(X0),X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f17,f18])).

fof(f32,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ r2_hidden(sK2(X0),sK1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | sK1(X0) != sK2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ r2_hidden(sK1(X0),sK2(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
    <=> ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(flattening,[],[f20])).

fof(f35,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    ~ v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1252,plain,
    ( r2_hidden(sK1(X0),sK2(X0))
    | r2_hidden(sK2(X0),sK1(X0))
    | ~ v3_ordinal1(sK1(X0))
    | ~ v3_ordinal1(sK2(X0))
    | sK1(X0) = sK2(X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1254,plain,
    ( r2_hidden(sK1(sK3),sK2(sK3))
    | r2_hidden(sK2(sK3),sK1(sK3))
    | ~ v3_ordinal1(sK1(sK3))
    | ~ v3_ordinal1(sK2(sK3))
    | sK1(sK3) = sK2(sK3) ),
    inference(instantiation,[status(thm)],[c_1252])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1229,plain,
    ( ~ r2_hidden(sK1(sK3),sK3)
    | v3_ordinal1(sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1223,plain,
    ( ~ r2_hidden(sK2(sK3),sK3)
    | v3_ordinal1(sK2(sK3)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( ~ r1_tarski(sK0(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | r1_tarski(X0,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_183,plain,
    ( ~ r2_hidden(X0,sK3)
    | v1_ordinal1(X1)
    | sK0(X1) != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_184,plain,
    ( ~ r2_hidden(sK0(sK3),sK3)
    | v1_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_183])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_47,plain,
    ( r2_hidden(sK0(sK3),sK3)
    | v1_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_186,plain,
    ( v1_ordinal1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_184,c_47])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK2(X0),sK1(X0))
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_43,plain,
    ( ~ r2_hidden(sK2(sK3),sK1(sK3))
    | v2_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( v2_ordinal1(X0)
    | sK1(X0) != sK2(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_40,plain,
    ( v2_ordinal1(sK3)
    | sK1(sK3) != sK2(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK1(X0),sK2(X0))
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_37,plain,
    ( ~ r2_hidden(sK1(sK3),sK2(sK3))
    | v2_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( r2_hidden(sK2(X0),X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_34,plain,
    ( r2_hidden(sK2(sK3),sK3)
    | v2_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0),X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_31,plain,
    ( r2_hidden(sK1(sK3),sK3)
    | v2_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( v3_ordinal1(X0)
    | ~ v2_ordinal1(X0)
    | ~ v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_27,plain,
    ( v3_ordinal1(sK3)
    | ~ v2_ordinal1(sK3)
    | ~ v1_ordinal1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_13,negated_conjecture,
    ( ~ v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1254,c_1229,c_1223,c_186,c_43,c_40,c_37,c_34,c_31,c_27,c_13])).


%------------------------------------------------------------------------------
