%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0291+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:33 EST 2020

% Result     : Theorem 11.95s
% Output     : CNFRefutation 11.95s
% Verified   : 
% Statistics : Number of formulae       :   41 (  63 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  163 ( 303 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f395,plain,(
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

fof(f406,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f395])).

fof(f611,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK13(X0,X1),X1)
        & r2_hidden(sK13(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f612,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK13(X0,X1),X1)
          & r2_hidden(sK13(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f406,f611])).

fof(f778,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f612])).

fof(f389,conjecture,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f390,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r1_xboole_0(X2,X1) )
       => r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f389])).

fof(f566,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k3_tarski(X0),X1)
      & ! [X2] :
          ( r1_xboole_0(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f390])).

fof(f720,plain,
    ( ? [X0,X1] :
        ( ~ r1_xboole_0(k3_tarski(X0),X1)
        & ! [X2] :
            ( r1_xboole_0(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
   => ( ~ r1_xboole_0(k3_tarski(sK36),sK37)
      & ! [X2] :
          ( r1_xboole_0(X2,sK37)
          | ~ r2_hidden(X2,sK36) ) ) ),
    introduced(choice_axiom,[])).

fof(f721,plain,
    ( ~ r1_xboole_0(k3_tarski(sK36),sK37)
    & ! [X2] :
        ( r1_xboole_0(X2,sK37)
        | ~ r2_hidden(X2,sK36) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK36,sK37])],[f566,f720])).

fof(f1262,plain,(
    ! [X2] :
      ( r1_xboole_0(X2,sK37)
      | ~ r2_hidden(X2,sK36) ) ),
    inference(cnf_transformation,[],[f721])).

fof(f286,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f674,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f286])).

fof(f675,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f674])).

fof(f678,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK32(X0,X5),X0)
        & r2_hidden(X5,sK32(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f677,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK31(X0,X1),X0)
        & r2_hidden(X2,sK31(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f676,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK30(X0,X1),X3) )
          | ~ r2_hidden(sK30(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK30(X0,X1),X4) )
          | r2_hidden(sK30(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f679,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK30(X0,X1),X3) )
            | ~ r2_hidden(sK30(X0,X1),X1) )
          & ( ( r2_hidden(sK31(X0,X1),X0)
              & r2_hidden(sK30(X0,X1),sK31(X0,X1)) )
            | r2_hidden(sK30(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK32(X0,X5),X0)
                & r2_hidden(X5,sK32(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK30,sK31,sK32])],[f675,f678,f677,f676])).

fof(f1103,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK32(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f679])).

fof(f1683,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK32(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f1103])).

fof(f1104,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK32(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f679])).

fof(f1682,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK32(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f1104])).

fof(f776,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK13(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f612])).

fof(f777,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK13(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f612])).

fof(f1263,plain,(
    ~ r1_xboole_0(k3_tarski(sK36),sK37) ),
    inference(cnf_transformation,[],[f721])).

cnf(c_55,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f778])).

cnf(c_19572,plain,
    ( ~ r1_xboole_0(X0,sK37)
    | ~ r2_hidden(sK13(k3_tarski(sK36),sK37),X0)
    | ~ r2_hidden(sK13(k3_tarski(sK36),sK37),sK37) ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_32031,plain,
    ( ~ r1_xboole_0(sK32(sK36,sK13(k3_tarski(sK36),sK37)),sK37)
    | ~ r2_hidden(sK13(k3_tarski(sK36),sK37),sK32(sK36,sK13(k3_tarski(sK36),sK37)))
    | ~ r2_hidden(sK13(k3_tarski(sK36),sK37),sK37) ),
    inference(instantiation,[status(thm)],[c_19572])).

cnf(c_529,negated_conjecture,
    ( r1_xboole_0(X0,sK37)
    | ~ r2_hidden(X0,sK36) ),
    inference(cnf_transformation,[],[f1262])).

cnf(c_27833,plain,
    ( r1_xboole_0(sK32(sK36,sK13(k3_tarski(sK36),sK37)),sK37)
    | ~ r2_hidden(sK32(sK36,sK13(k3_tarski(sK36),sK37)),sK36) ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_374,plain,
    ( r2_hidden(X0,sK32(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f1683])).

cnf(c_19732,plain,
    ( r2_hidden(sK13(k3_tarski(sK36),sK37),sK32(sK36,sK13(k3_tarski(sK36),sK37)))
    | ~ r2_hidden(sK13(k3_tarski(sK36),sK37),k3_tarski(sK36)) ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_373,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK32(X1,X0),X1) ),
    inference(cnf_transformation,[],[f1682])).

cnf(c_19733,plain,
    ( r2_hidden(sK32(sK36,sK13(k3_tarski(sK36),sK37)),sK36)
    | ~ r2_hidden(sK13(k3_tarski(sK36),sK37),k3_tarski(sK36)) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_57,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK13(X0,X1),X0) ),
    inference(cnf_transformation,[],[f776])).

cnf(c_15061,plain,
    ( r1_xboole_0(k3_tarski(sK36),sK37)
    | r2_hidden(sK13(k3_tarski(sK36),sK37),k3_tarski(sK36)) ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_56,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK13(X0,X1),X1) ),
    inference(cnf_transformation,[],[f777])).

cnf(c_15024,plain,
    ( r1_xboole_0(k3_tarski(sK36),sK37)
    | r2_hidden(sK13(k3_tarski(sK36),sK37),sK37) ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_528,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(sK36),sK37) ),
    inference(cnf_transformation,[],[f1263])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32031,c_27833,c_19732,c_19733,c_15061,c_15024,c_528])).

%------------------------------------------------------------------------------
