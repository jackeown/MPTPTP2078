%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0071+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:17 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  79 expanded)
%              Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :  153 ( 293 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f118])).

fof(f223,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f224,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f128,f223])).

fof(f297,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f224])).

fof(f106,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f107,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f106])).

fof(f178,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X3)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f107])).

fof(f179,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X3)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f178])).

fof(f239,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK15,sK17)
      & r1_xboole_0(sK16,sK18)
      & r1_tarski(sK17,sK18)
      & r1_tarski(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f240,plain,
    ( ~ r1_xboole_0(sK15,sK17)
    & r1_xboole_0(sK16,sK18)
    & r1_tarski(sK17,sK18)
    & r1_tarski(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17,sK18])],[f179,f239])).

fof(f384,plain,(
    r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f240])).

fof(f386,plain,(
    r1_xboole_0(sK16,sK18) ),
    inference(cnf_transformation,[],[f240])).

fof(f105,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f176,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f105])).

fof(f177,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f176])).

fof(f383,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f177])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f122,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f122])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f190])).

fof(f192,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f191,f192])).

fof(f249,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f193])).

fof(f295,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f224])).

fof(f296,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f224])).

fof(f387,plain,(
    ~ r1_xboole_0(sK15,sK17) ),
    inference(cnf_transformation,[],[f240])).

fof(f385,plain,(
    r1_tarski(sK17,sK18) ),
    inference(cnf_transformation,[],[f240])).

cnf(c_52,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f297])).

cnf(c_5666,plain,
    ( ~ r1_xboole_0(sK15,X0)
    | ~ r2_hidden(sK9(sK15,sK17),X0)
    | ~ r2_hidden(sK9(sK15,sK17),sK15) ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_14237,plain,
    ( ~ r1_xboole_0(sK15,sK18)
    | ~ r2_hidden(sK9(sK15,sK17),sK18)
    | ~ r2_hidden(sK9(sK15,sK17),sK15) ),
    inference(instantiation,[status(thm)],[c_5666])).

cnf(c_143,negated_conjecture,
    ( r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f384])).

cnf(c_4342,plain,
    ( r1_tarski(sK15,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_143])).

cnf(c_141,negated_conjecture,
    ( r1_xboole_0(sK16,sK18) ),
    inference(cnf_transformation,[],[f386])).

cnf(c_4344,plain,
    ( r1_xboole_0(sK16,sK18) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_141])).

cnf(c_139,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f383])).

cnf(c_4346,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X2,X1) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_139])).

cnf(c_9833,plain,
    ( r1_xboole_0(X0,sK18) = iProver_top
    | r1_tarski(X0,sK16) != iProver_top ),
    inference(superposition,[status(thm)],[c_4344,c_4346])).

cnf(c_10890,plain,
    ( r1_xboole_0(sK15,sK18) = iProver_top ),
    inference(superposition,[status(thm)],[c_4342,c_9833])).

cnf(c_10910,plain,
    ( r1_xboole_0(sK15,sK18) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10890])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f249])).

cnf(c_5611,plain,
    ( ~ r1_tarski(sK17,X0)
    | r2_hidden(sK9(sK15,sK17),X0)
    | ~ r2_hidden(sK9(sK15,sK17),sK17) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8590,plain,
    ( ~ r1_tarski(sK17,sK18)
    | r2_hidden(sK9(sK15,sK17),sK18)
    | ~ r2_hidden(sK9(sK15,sK17),sK17) ),
    inference(instantiation,[status(thm)],[c_5611])).

cnf(c_54,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK9(X0,X1),X0) ),
    inference(cnf_transformation,[],[f295])).

cnf(c_5223,plain,
    ( r1_xboole_0(sK15,sK17)
    | r2_hidden(sK9(sK15,sK17),sK15) ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_53,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK9(X0,X1),X1) ),
    inference(cnf_transformation,[],[f296])).

cnf(c_5220,plain,
    ( r1_xboole_0(sK15,sK17)
    | r2_hidden(sK9(sK15,sK17),sK17) ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_140,negated_conjecture,
    ( ~ r1_xboole_0(sK15,sK17) ),
    inference(cnf_transformation,[],[f387])).

cnf(c_142,negated_conjecture,
    ( r1_tarski(sK17,sK18) ),
    inference(cnf_transformation,[],[f385])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14237,c_10910,c_8590,c_5223,c_5220,c_140,c_142])).

%------------------------------------------------------------------------------
