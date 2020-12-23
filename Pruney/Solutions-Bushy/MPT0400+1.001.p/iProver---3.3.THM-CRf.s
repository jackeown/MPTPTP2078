%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0400+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:13 EST 2020

% Result     : Theorem 0.85s
% Output     : CNFRefutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 111 expanded)
%              Number of clauses        :   26 (  31 expanded)
%              Number of leaves         :    6 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  156 ( 449 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f10])).

fof(f13,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK1(X1,X4))
        & r2_hidden(sK1(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK0(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK0(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK1(X1,X4))
              & r2_hidden(sK1(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13,f12])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(sK0(X0,X1),X3)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f17,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK1(X1,X4),X1)
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f18,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(X4,sK1(X1,X4))
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_setfam_1(X1,X2)
        & r1_setfam_1(X0,X1) )
     => r1_setfam_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_setfam_1(X1,X2)
          & r1_setfam_1(X0,X1) )
       => r1_setfam_1(X0,X2) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_setfam_1(X0,X2)
      & r1_setfam_1(X1,X2)
      & r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_setfam_1(X0,X2)
      & r1_setfam_1(X1,X2)
      & r1_setfam_1(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_setfam_1(X0,X2)
        & r1_setfam_1(X1,X2)
        & r1_setfam_1(X0,X1) )
   => ( ~ r1_setfam_1(sK2,sK4)
      & r1_setfam_1(sK3,sK4)
      & r1_setfam_1(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ~ r1_setfam_1(sK2,sK4)
    & r1_setfam_1(sK3,sK4)
    & r1_setfam_1(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f15])).

fof(f24,plain,(
    ~ r1_setfam_1(sK2,sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f23,plain,(
    r1_setfam_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f22,plain,(
    r1_setfam_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_232,plain,
    ( ~ r1_tarski(X0_37,X1_37)
    | ~ r1_tarski(X2_37,X0_37)
    | r1_tarski(X2_37,X1_37) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_573,plain,
    ( ~ r1_tarski(X0_37,sK1(sK3,sK0(sK2,sK4)))
    | r1_tarski(X0_37,sK1(sK4,sK1(sK3,sK0(sK2,sK4))))
    | ~ r1_tarski(sK1(sK3,sK0(sK2,sK4)),sK1(sK4,sK1(sK3,sK0(sK2,sK4)))) ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_669,plain,
    ( ~ r1_tarski(sK1(sK3,sK0(sK2,sK4)),sK1(sK4,sK1(sK3,sK0(sK2,sK4))))
    | ~ r1_tarski(sK0(sK2,sK4),sK1(sK3,sK0(sK2,sK4)))
    | r1_tarski(sK0(sK2,sK4),sK1(sK4,sK1(sK3,sK0(sK2,sK4)))) ),
    inference(instantiation,[status(thm)],[c_573])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(sK0(X2,X1),X0)
    | r1_setfam_1(X2,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_236,plain,
    ( ~ r2_hidden(X0_37,X0_36)
    | ~ r1_tarski(sK0(X1_36,X0_36),X0_37)
    | r1_setfam_1(X1_36,X0_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_578,plain,
    ( ~ r2_hidden(sK1(sK4,sK1(sK3,sK0(sK2,sK4))),sK4)
    | ~ r1_tarski(sK0(X0_36,sK4),sK1(sK4,sK1(sK3,sK0(sK2,sK4))))
    | r1_setfam_1(X0_36,sK4) ),
    inference(instantiation,[status(thm)],[c_236])).

cnf(c_590,plain,
    ( ~ r2_hidden(sK1(sK4,sK1(sK3,sK0(sK2,sK4))),sK4)
    | ~ r1_tarski(sK0(sK2,sK4),sK1(sK4,sK1(sK3,sK0(sK2,sK4))))
    | r1_setfam_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(X2,X0),X2)
    | ~ r1_setfam_1(X1,X2) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_233,plain,
    ( ~ r2_hidden(X0_37,X0_36)
    | r2_hidden(sK1(X1_36,X0_37),X1_36)
    | ~ r1_setfam_1(X0_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_331,plain,
    ( r2_hidden(sK1(X0_36,sK1(sK3,sK0(sK2,sK4))),X0_36)
    | ~ r2_hidden(sK1(sK3,sK0(sK2,sK4)),sK3)
    | ~ r1_setfam_1(sK3,X0_36) ),
    inference(instantiation,[status(thm)],[c_233])).

cnf(c_479,plain,
    ( ~ r2_hidden(sK1(sK3,sK0(sK2,sK4)),sK3)
    | r2_hidden(sK1(sK4,sK1(sK3,sK0(sK2,sK4))),sK4)
    | ~ r1_setfam_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,sK1(X2,X0))
    | ~ r1_setfam_1(X1,X2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_234,plain,
    ( ~ r2_hidden(X0_37,X0_36)
    | r1_tarski(X0_37,sK1(X1_36,X0_37))
    | ~ r1_setfam_1(X0_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_330,plain,
    ( ~ r2_hidden(sK1(sK3,sK0(sK2,sK4)),sK3)
    | r1_tarski(sK1(sK3,sK0(sK2,sK4)),sK1(X0_36,sK1(sK3,sK0(sK2,sK4))))
    | ~ r1_setfam_1(sK3,X0_36) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_443,plain,
    ( ~ r2_hidden(sK1(sK3,sK0(sK2,sK4)),sK3)
    | r1_tarski(sK1(sK3,sK0(sK2,sK4)),sK1(sK4,sK1(sK3,sK0(sK2,sK4))))
    | ~ r1_setfam_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_284,plain,
    ( r2_hidden(sK1(X0_36,sK0(sK2,sK4)),X0_36)
    | ~ r2_hidden(sK0(sK2,sK4),sK2)
    | ~ r1_setfam_1(sK2,X0_36) ),
    inference(instantiation,[status(thm)],[c_233])).

cnf(c_296,plain,
    ( r2_hidden(sK1(sK3,sK0(sK2,sK4)),sK3)
    | ~ r2_hidden(sK0(sK2,sK4),sK2)
    | ~ r1_setfam_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_283,plain,
    ( ~ r2_hidden(sK0(sK2,sK4),sK2)
    | r1_tarski(sK0(sK2,sK4),sK1(X0_36,sK0(sK2,sK4)))
    | ~ r1_setfam_1(sK2,X0_36) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_293,plain,
    ( ~ r2_hidden(sK0(sK2,sK4),sK2)
    | r1_tarski(sK0(sK2,sK4),sK1(sK3,sK0(sK2,sK4)))
    | ~ r1_setfam_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_setfam_1(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_5,negated_conjecture,
    ( ~ r1_setfam_1(sK2,sK4) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_109,plain,
    ( r2_hidden(sK0(sK2,sK4),sK2) ),
    inference(resolution,[status(thm)],[c_1,c_5])).

cnf(c_6,negated_conjecture,
    ( r1_setfam_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_7,negated_conjecture,
    ( r1_setfam_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_669,c_590,c_479,c_443,c_296,c_293,c_109,c_5,c_6,c_7])).


%------------------------------------------------------------------------------
