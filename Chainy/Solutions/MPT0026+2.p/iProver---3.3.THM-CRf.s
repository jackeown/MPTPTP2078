%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0026+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:12 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   55 (  87 expanded)
%              Number of clauses        :   21 (  22 expanded)
%              Number of leaves         :   10 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  189 ( 321 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f73])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f112])).

fof(f114,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f113,f114])).

fof(f165,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f115])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f121,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f122,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f121])).

fof(f123,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f122])).

fof(f124,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f125,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f123,f124])).

fof(f176,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f125])).

fof(f277,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f176])).

fof(f46,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f234,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f160,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f56,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f245,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f56])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f159,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f167,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f115])).

fof(f166,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f115])).

fof(f49,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f49])).

fof(f97,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f98,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f97])).

fof(f155,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK14,k3_xboole_0(sK15,sK16))
      & r1_tarski(sK14,sK16)
      & r1_tarski(sK14,sK15) ) ),
    introduced(choice_axiom,[])).

fof(f156,plain,
    ( ~ r1_tarski(sK14,k3_xboole_0(sK15,sK16))
    & r1_tarski(sK14,sK16)
    & r1_tarski(sK14,sK15) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16])],[f98,f155])).

fof(f239,plain,(
    ~ r1_tarski(sK14,k3_xboole_0(sK15,sK16)) ),
    inference(cnf_transformation,[],[f156])).

fof(f238,plain,(
    r1_tarski(sK14,sK16) ),
    inference(cnf_transformation,[],[f156])).

fof(f237,plain,(
    r1_tarski(sK14,sK15) ),
    inference(cnf_transformation,[],[f156])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f165])).

cnf(c_4147,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(sK14,k3_xboole_0(sK15,sK16)),X0)
    | r2_hidden(sK1(sK14,k3_xboole_0(sK15,sK16)),X1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_14871,plain,
    ( ~ r1_tarski(sK14,X0)
    | r2_hidden(sK1(sK14,k3_xboole_0(sK15,sK16)),X0)
    | ~ r2_hidden(sK1(sK14,k3_xboole_0(sK15,sK16)),sK14) ),
    inference(instantiation,[status(thm)],[c_4147])).

cnf(c_22903,plain,
    ( ~ r1_tarski(sK14,sK15)
    | r2_hidden(sK1(sK14,k3_xboole_0(sK15,sK16)),sK15)
    | ~ r2_hidden(sK1(sK14,k3_xboole_0(sK15,sK16)),sK14) ),
    inference(instantiation,[status(thm)],[c_14871])).

cnf(c_3474,plain,
    ( ~ r1_tarski(X0,sK16)
    | ~ r2_hidden(sK1(sK14,k3_xboole_0(sK15,sK16)),X0)
    | r2_hidden(sK1(sK14,k3_xboole_0(sK15,sK16)),sK16) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6876,plain,
    ( ~ r1_tarski(sK14,sK16)
    | r2_hidden(sK1(sK14,k3_xboole_0(sK15,sK16)),sK16)
    | ~ r2_hidden(sK1(sK14,k3_xboole_0(sK15,sK16)),sK14) ),
    inference(instantiation,[status(thm)],[c_3474])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f277])).

cnf(c_75,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f234])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f160])).

cnf(c_86,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f245])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_1612,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(theory_normalisation,[status(thm)],[c_19,c_75,c_3,c_86,c_2])).

cnf(c_3184,plain,
    ( r2_hidden(sK1(sK14,k3_xboole_0(sK15,sK16)),k3_xboole_0(sK15,sK16))
    | ~ r2_hidden(sK1(sK14,k3_xboole_0(sK15,sK16)),sK16)
    | ~ r2_hidden(sK1(sK14,k3_xboole_0(sK15,sK16)),sK15) ),
    inference(instantiation,[status(thm)],[c_1612])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f167])).

cnf(c_3116,plain,
    ( r1_tarski(sK14,k3_xboole_0(sK15,sK16))
    | ~ r2_hidden(sK1(sK14,k3_xboole_0(sK15,sK16)),k3_xboole_0(sK15,sK16)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f166])).

cnf(c_3119,plain,
    ( r1_tarski(sK14,k3_xboole_0(sK15,sK16))
    | r2_hidden(sK1(sK14,k3_xboole_0(sK15,sK16)),sK14) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_78,negated_conjecture,
    ( ~ r1_tarski(sK14,k3_xboole_0(sK15,sK16)) ),
    inference(cnf_transformation,[],[f239])).

cnf(c_79,negated_conjecture,
    ( r1_tarski(sK14,sK16) ),
    inference(cnf_transformation,[],[f238])).

cnf(c_80,negated_conjecture,
    ( r1_tarski(sK14,sK15) ),
    inference(cnf_transformation,[],[f237])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22903,c_6876,c_3184,c_3116,c_3119,c_78,c_79,c_80])).

%------------------------------------------------------------------------------
