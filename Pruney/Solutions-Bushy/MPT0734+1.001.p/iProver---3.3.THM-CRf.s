%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0734+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:00 EST 2020

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 123 expanded)
%              Number of clauses        :   31 (  33 expanded)
%              Number of leaves         :   13 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  236 ( 600 expanded)
%              Number of equality atoms :   29 (  29 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r2_hidden(X1,X2)
                  & r1_tarski(X0,X1) )
               => r2_hidden(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ! [X2] :
                ( v3_ordinal1(X2)
               => ( ( r2_hidden(X1,X2)
                    & r1_tarski(X0,X1) )
                 => r2_hidden(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,X2)
          & r2_hidden(X1,X2)
          & r1_tarski(X0,X1)
          & v3_ordinal1(X2) )
     => ( ~ r2_hidden(X0,sK3)
        & r2_hidden(X1,sK3)
        & r1_tarski(X0,X1)
        & v3_ordinal1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
     => ( ? [X2] :
            ( ~ r2_hidden(X0,X2)
            & r2_hidden(sK2,X2)
            & r1_tarski(X0,sK2)
            & v3_ordinal1(X2) )
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X0,X2)
                & r2_hidden(X1,X2)
                & r1_tarski(X0,X1)
                & v3_ordinal1(X2) )
            & v3_ordinal1(X1) )
        & v1_ordinal1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(sK1,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(sK1,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r2_hidden(sK1,sK3)
    & r2_hidden(sK2,sK3)
    & r1_tarski(sK1,sK2)
    & v3_ordinal1(sK3)
    & v3_ordinal1(sK2)
    & v1_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f28,f27,f26])).

fof(f43,plain,(
    ~ r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK0(X0),X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK0(X0),X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f31,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    v1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_473,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_791,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK1,sK2)
    | X1 != sK2
    | X0 != sK1 ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_811,plain,
    ( r1_tarski(X0,sK2)
    | ~ r1_tarski(sK1,sK2)
    | X0 != sK1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_853,plain,
    ( r1_tarski(sK3,sK2)
    | ~ r1_tarski(sK1,sK2)
    | sK2 != sK2
    | sK3 != sK1 ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_470,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_812,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_781,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK1,X0)
    | ~ r1_tarski(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_803,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r1_tarski(sK1,sK2)
    | r1_tarski(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_781])).

cnf(c_8,negated_conjecture,
    ( ~ r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_145,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_4,c_6])).

cnf(c_11,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_185,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v1_ordinal1(X0)
    | X1 = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_145,c_11])).

cnf(c_186,plain,
    ( r2_hidden(X0,sK3)
    | ~ r1_tarski(X0,sK3)
    | ~ v1_ordinal1(X0)
    | sK3 = X0 ),
    inference(unflattening,[status(thm)],[c_185])).

cnf(c_314,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ v1_ordinal1(X0)
    | sK3 = X0
    | sK3 != sK3
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_186])).

cnf(c_315,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ v1_ordinal1(sK1)
    | sK3 = sK1 ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_256,plain,
    ( r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_9])).

cnf(c_257,plain,
    ( r1_tarski(sK2,sK3)
    | ~ v1_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_249,plain,
    ( ~ r1_tarski(X0,X1)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_9])).

cnf(c_250,plain,
    ( ~ r1_tarski(sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_249])).

cnf(c_0,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_171,plain,
    ( v1_ordinal1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_172,plain,
    ( v1_ordinal1(sK3) ),
    inference(unflattening,[status(thm)],[c_171])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_13,negated_conjecture,
    ( v1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_853,c_812,c_803,c_315,c_257,c_250,c_172,c_10,c_13])).


%------------------------------------------------------------------------------
